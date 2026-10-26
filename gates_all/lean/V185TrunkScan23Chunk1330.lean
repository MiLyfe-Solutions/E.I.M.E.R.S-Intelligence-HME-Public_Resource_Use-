import V185TrunkScan23Chunk1329

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7877770 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_7877770 : Nat := 118140960795 + 7877770 * 2 ^ 59
def prefixEnd_7877770 : Nat := 4983230072969 + 3 ^ 40 * 7877770 * 2
def baseEnd_7877770 : Nat := 4045082495569748422345801

theorem tailTrace_7877770 : CollatzResearch.WordTrace tailWord_7877770 prefixEnd_7877770 4045082495569748422345801 := by
  unfold tailWord_7877770
  simp only [CollatzResearch.WordTrace]
  refine ⟨71831469167548045211767691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191550584446794787231380509 71831469167548045211767691)
  ·
    refine ⟨107747203751322067817651537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71831469167548045211767691 107747203751322067817651537)
    ·
      refine ⟨80810402813491550863238653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107747203751322067817651537 80810402813491550863238653)
      ·
        refine ⟨30303901055059331573714495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80810402813491550863238653 30303901055059331573714495)
        ·
          refine ⟨45455851582588997360571743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30303901055059331573714495 45455851582588997360571743)
          ·
            refine ⟨68183777373883496040857615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45455851582588997360571743 68183777373883496040857615)
            ·
              refine ⟨102275666060825244061286423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68183777373883496040857615 102275666060825244061286423)
              ·
                refine ⟨153413499091237866091929635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102275666060825244061286423 153413499091237866091929635)
                ·
                  refine ⟨230120248636856799137894453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153413499091237866091929635 230120248636856799137894453)
                  ·
                    refine ⟨21573773309705324919177605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 230120248636856799137894453 21573773309705324919177605)
                    ·
                      refine ⟨4045082495569748422345801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21573773309705324919177605 4045082495569748422345801)
                      ·
                        rfl

theorem cell23_7877770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_7877770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877770 prefixEnd_7877770 := by exact prefixLift 7877770
  have htrace : WordTrace (prefixWord ++ tailWord_7877770) baseStart_7877770 baseEnd_7877770 := by
    simpa [prefixWord, tailWord_7877770, baseEnd_7877770] using wordTrace_append hprefix tailTrace_7877770
  have hstable : (prefixWord ++ tailWord_7877770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877770).length < 2 ^ (prefixWord ++ tailWord_7877770).sum := by decide
  have hdescent : baseEnd_7877770 < baseStart_7877770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877774 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_7877774 : Nat := 118140960795 + 7877774 * 2 ^ 59
def prefixEnd_7877774 : Nat := 4983230072969 + 3 ^ 40 * 7877774 * 2
def baseEnd_7877774 : Nat := 4045084549492366406695783

theorem tailTrace_7877774 : CollatzResearch.WordTrace tailWord_7877774 prefixEnd_7877774 4045084549492366406695783 := by
  unfold tailWord_7877774
  simp only [CollatzResearch.WordTrace]
  refine ⟨35915752820272211191277047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191550681708118459686810917 35915752820272211191277047)
  ·
    refine ⟨53873629230408316786915571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35915752820272211191277047 53873629230408316786915571)
    ·
      refine ⟨80810443845612475180373357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53873629230408316786915571 80810443845612475180373357)
      ·
        refine ⟨30303916442104678192640009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80810443845612475180373357 30303916442104678192640009)
        ·
          refine ⟨22727937331578508644480007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30303916442104678192640009 22727937331578508644480007)
          ·
            refine ⟨34091905997367762966720011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22727937331578508644480007 34091905997367762966720011)
            ·
              refine ⟨51137858996051644450080017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34091905997367762966720011 51137858996051644450080017)
              ·
                refine ⟨38353394247038733337560013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51137858996051644450080017 38353394247038733337560013)
                ·
                  refine ⟨14382522842639525001585005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38353394247038733337560013 14382522842639525001585005)
                  ·
                    refine ⟨5393446065989821875594377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14382522842639525001585005 5393446065989821875594377)
                    ·
                      refine ⟨4045084549492366406695783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393446065989821875594377 4045084549492366406695783)
                      ·
                        rfl

theorem cell23_7877774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_7877774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877774 prefixEnd_7877774 := by exact prefixLift 7877774
  have htrace : WordTrace (prefixWord ++ tailWord_7877774) baseStart_7877774 baseEnd_7877774 := by
    simpa [prefixWord, tailWord_7877774, baseEnd_7877774] using wordTrace_append hprefix tailTrace_7877774
  have hstable : (prefixWord ++ tailWord_7877774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877774).length < 2 ^ (prefixWord ++ tailWord_7877774).sum := by decide
  have hdescent : baseEnd_7877774 < baseStart_7877774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877821 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_7877821 : Nat := 118140960795 + 7877821 * 2 ^ 59
def prefixEnd_7877821 : Nat := 4983230072969 + 3 ^ 40 * 7877821 * 2
def baseEnd_7877821 : Nat := 4045108683083127722808067

theorem tailTrace_7877821 : CollatzResearch.WordTrace tailWord_7877821 prefixEnd_7877821 4045108683083127722808067 := by
  unfold tailWord_7877821
  simp only [CollatzResearch.WordTrace]
  refine ⟨287327736793007416557177317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191551824528671611038118211 287327736793007416557177317)
  ·
    refine ⟨53873950648688890604470747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287327736793007416557177317 53873950648688890604470747)
    ·
      refine ⟨80810925973033335906706121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53873950648688890604470747 80810925973033335906706121)
      ·
        refine ⟨60608194479775001930029591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80810925973033335906706121 60608194479775001930029591)
        ·
          refine ⟨90912291719662502895044387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60608194479775001930029591 90912291719662502895044387)
          ·
            refine ⟨136368437579493754342566581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90912291719662502895044387 136368437579493754342566581)
            ·
              refine ⟨12784541023077539469615617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136368437579493754342566581 12784541023077539469615617)
              ·
                refine ⟨9588405767308154602211713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12784541023077539469615617 9588405767308154602211713)
                ·
                  refine ⟨7191304325481115951658785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9588405767308154602211713 7191304325481115951658785)
                  ·
                    refine ⟨5393478244110836963744089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7191304325481115951658785 5393478244110836963744089)
                    ·
                      refine ⟨4045108683083127722808067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393478244110836963744089 4045108683083127722808067)
                      ·
                        rfl

theorem cell23_7877821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_7877821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877821 prefixEnd_7877821 := by exact prefixLift 7877821
  have htrace : WordTrace (prefixWord ++ tailWord_7877821) baseStart_7877821 baseEnd_7877821 := by
    simpa [prefixWord, tailWord_7877821, baseEnd_7877821] using wordTrace_append hprefix tailTrace_7877821
  have hstable : (prefixWord ++ tailWord_7877821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877821).length < 2 ^ (prefixWord ++ tailWord_7877821).sum := by decide
  have hdescent : baseEnd_7877821 < baseStart_7877821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877838 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_7877838 : Nat := 118140960795 + 7877838 * 2 ^ 59
def prefixEnd_7877838 : Nat := 4983230072969 + 3 ^ 40 * 7877838 * 2
def baseEnd_7877838 : Nat := 4045117412254254156295489

theorem tailTrace_7877838 : CollatzResearch.WordTrace tailWord_7877838 prefixEnd_7877838 4045117412254254156295489 := by
  unfold tailWord_7877838
  simp only [CollatzResearch.WordTrace]
  refine ⟨35916044604243228557568271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191552237889297218973697445 35916044604243228557568271)
  ·
    refine ⟨53874066906364842836352407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35916044604243228557568271 53874066906364842836352407)
    ·
      refine ⟨80811100359547264254528611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53874066906364842836352407 80811100359547264254528611)
      ·
        refine ⟨121216650539320896381792917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80811100359547264254528611 121216650539320896381792917)
        ·
          refine ⟨5682030494030667017896543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121216650539320896381792917 5682030494030667017896543)
          ·
            refine ⟨8523045741046000526844815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5682030494030667017896543 8523045741046000526844815)
            ·
              refine ⟨12784568611569000790267223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8523045741046000526844815 12784568611569000790267223)
              ·
                refine ⟨19176852917353501185400835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784568611569000790267223 19176852917353501185400835)
                ·
                  refine ⟨28765279376030251778101253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19176852917353501185400835 28765279376030251778101253)
                  ·
                    refine ⟨5393489883005672208393985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28765279376030251778101253 5393489883005672208393985)
                    ·
                      refine ⟨4045117412254254156295489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393489883005672208393985 4045117412254254156295489)
                      ·
                        rfl

theorem cell23_7877838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_7877838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877838 prefixEnd_7877838 := by exact prefixLift 7877838
  have htrace : WordTrace (prefixWord ++ tailWord_7877838) baseStart_7877838 baseEnd_7877838 := by
    simpa [prefixWord, tailWord_7877838, baseEnd_7877838] using wordTrace_append hprefix tailTrace_7877838
  have hstable : (prefixWord ++ tailWord_7877838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877838).length < 2 ^ (prefixWord ++ tailWord_7877838).sum := by decide
  have hdescent : baseEnd_7877838 < baseStart_7877838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877847 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 2, 5, 2]
def baseStart_7877847 : Nat := 118140960795 + 7877847 * 2 ^ 59
def prefixEnd_7877847 : Nat := 4983230072969 + 3 ^ 40 * 7877847 * 2
def baseEnd_7877847 : Nat := 4045122033580144621082947

theorem tailTrace_7877847 : CollatzResearch.WordTrace tailWord_7877847 prefixEnd_7877847 4045122033580144621082947 := by
  unfold tailWord_7877847
  simp only [CollatzResearch.WordTrace]
  refine ⟨287328685090913222997623795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191552456727275481998415863 287328685090913222997623795)
  ·
    refine ⟨430993027636369834496435693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287328685090913222997623795 430993027636369834496435693)
    ·
      refine ⟨161622385363638687936163385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430993027636369834496435693 161622385363638687936163385)
      ·
        refine ⟨121216789022729015952122539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161622385363638687936163385 121216789022729015952122539)
        ·
          refine ⟨181825183534093523928183809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121216789022729015952122539 181825183534093523928183809)
          ·
            refine ⟨136368887650570142946137857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181825183534093523928183809 136368887650570142946137857)
            ·
              refine ⟨102276665737927607209603393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136368887650570142946137857 102276665737927607209603393)
              ·
                refine ⟨76707499303445705407202545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102276665737927607209603393 76707499303445705407202545)
                ·
                  refine ⟨57530624477584279055401909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76707499303445705407202545 57530624477584279055401909)
                  ·
                    refine ⟨5393496044773526161443929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57530624477584279055401909 5393496044773526161443929)
                    ·
                      refine ⟨4045122033580144621082947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393496044773526161443929 4045122033580144621082947)
                      ·
                        rfl

theorem cell23_7877847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_7877847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877847 prefixEnd_7877847 := by exact prefixLift 7877847
  have htrace : WordTrace (prefixWord ++ tailWord_7877847) baseStart_7877847 baseEnd_7877847 := by
    simpa [prefixWord, tailWord_7877847, baseEnd_7877847] using wordTrace_append hprefix tailTrace_7877847
  have hstable : (prefixWord ++ tailWord_7877847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877847).length < 2 ^ (prefixWord ++ tailWord_7877847).sum := by decide
  have hdescent : baseEnd_7877847 < baseStart_7877847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877850 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_7877850 : Nat := 118140960795 + 7877850 * 2 ^ 59
def prefixEnd_7877850 : Nat := 4983230072969 + 3 ^ 40 * 7877850 * 2
def baseEnd_7877850 : Nat := 4045123574022108109345433

theorem tailTrace_7877850 : CollatzResearch.WordTrace tailWord_7877850 prefixEnd_7877850 4045123574022108109345433 := by
  unfold tailWord_7877850
  simp only [CollatzResearch.WordTrace]
  refine ⟨71832198627475588627495751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191552529673268236339988669 71832198627475588627495751)
  ·
    refine ⟨107748297941213382941243627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71832198627475588627495751 107748297941213382941243627)
    ·
      refine ⟨161622446911820074411865441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107748297941213382941243627 161622446911820074411865441)
      ·
        refine ⟨121216835183865055808899081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161622446911820074411865441 121216835183865055808899081)
        ·
          refine ⟨90912626387898791856674311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121216835183865055808899081 90912626387898791856674311)
          ·
            refine ⟨136368939581848187785011467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90912626387898791856674311 136368939581848187785011467)
            ·
              refine ⟨204553409372772281677517201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136368939581848187785011467 204553409372772281677517201)
              ·
                refine ⟨153415057029579211258137901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204553409372772281677517201 153415057029579211258137901)
                ·
                  refine ⟨57530646386092204221801713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153415057029579211258137901 57530646386092204221801713)
                  ·
                    refine ⟨43147984789569153166351285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57530646386092204221801713 43147984789569153166351285)
                    ·
                      refine ⟨4045123574022108109345433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43147984789569153166351285 4045123574022108109345433)
                      ·
                        rfl

theorem cell23_7877850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_7877850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877850 prefixEnd_7877850 := by exact prefixLift 7877850
  have htrace : WordTrace (prefixWord ++ tailWord_7877850) baseStart_7877850 baseEnd_7877850 := by
    simpa [prefixWord, tailWord_7877850, baseEnd_7877850] using wordTrace_append hprefix tailTrace_7877850
  have hstable : (prefixWord ++ tailWord_7877850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877850).length < 2 ^ (prefixWord ++ tailWord_7877850).sum := by decide
  have hdescent : baseEnd_7877850 < baseStart_7877850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877861 : List Nat := [1, 3, 1, 4, 3, 2, 1, 3, 5]
def baseStart_7877861 : Nat := 118140960795 + 7877861 * 2 ^ 59
def prefixEnd_7877861 : Nat := 4983230072969 + 3 ^ 40 * 7877861 * 2
def baseEnd_7877861 : Nat := 449458802478811951811987

theorem tailTrace_7877861 : CollatzResearch.WordTrace tailWord_7877861 prefixEnd_7877861 449458802478811951811987 := by
  unfold tailWord_7877861
  simp only [CollatzResearch.WordTrace]
  refine ⟨287329195712862503388633437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191552797141908335592422291 287329195712862503388633437)
  ·
    refine ⟨107748448392323438770737539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287329195712862503388633437 107748448392323438770737539)
    ·
      refine ⟨161622672588485158156106309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107748448392323438770737539 161622672588485158156106309)
      ·
        refine ⟨30304251110340967154269933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161622672588485158156106309 30304251110340967154269933)
        ·
          refine ⟨11364094166377862682851225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30304251110340967154269933 11364094166377862682851225)
          ·
            refine ⟨8523070624783397012138419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11364094166377862682851225 8523070624783397012138419)
            ·
              refine ⟨12784605937175095518207629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8523070624783397012138419 12784605937175095518207629)
              ·
                refine ⟨4794227226440660819327861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12784605937175095518207629 4794227226440660819327861)
                ·
                  refine ⟨449458802478811951811987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4794227226440660819327861 449458802478811951811987)
                  ·
                    rfl

theorem cell23_7877861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_7877861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877861 prefixEnd_7877861 := by exact prefixLift 7877861
  have htrace : WordTrace (prefixWord ++ tailWord_7877861) baseStart_7877861 baseEnd_7877861 := by
    simpa [prefixWord, tailWord_7877861, baseEnd_7877861] using wordTrace_append hprefix tailTrace_7877861
  have hstable : (prefixWord ++ tailWord_7877861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877861).length < 2 ^ (prefixWord ++ tailWord_7877861).sum := by decide
  have hdescent : baseEnd_7877861 < baseStart_7877861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877874 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_7877874 : Nat := 118140960795 + 7877874 * 2 ^ 59
def prefixEnd_7877874 : Nat := 4983230072969 + 3 ^ 40 * 7877874 * 2
def baseEnd_7877874 : Nat := 1348378632519272005148441

theorem tailTrace_7877874 : CollatzResearch.WordTrace tailWord_7877874 prefixEnd_7877874 1348378632519272005148441 := by
  unfold tailWord_7877874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71832417465453851652214169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191553113241210271072571117 71832417465453851652214169)
  ·
    refine ⟨53874313099090388739160627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71832417465453851652214169 53874313099090388739160627)
    ·
      refine ⟨80811469648635583108740941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53874313099090388739160627 80811469648635583108740941)
      ·
        refine ⟨30304301118238343665777853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80811469648635583108740941 30304301118238343665777853)
        ·
          refine ⟨11364112919339378874666695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30304301118238343665777853 11364112919339378874666695)
          ·
            refine ⟨17046169379009068312000043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11364112919339378874666695 17046169379009068312000043)
            ·
              refine ⟨25569254068513602468000065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17046169379009068312000043 25569254068513602468000065)
              ·
                refine ⟨19176940551385201851000049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25569254068513602468000065 19176940551385201851000049)
                ·
                  refine ⟨14382705413538901388250037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19176940551385201851000049 14382705413538901388250037)
                  ·
                    refine ⟨1348378632519272005148441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14382705413538901388250037 1348378632519272005148441)
                    ·
                      rfl

theorem cell23_7877874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_7877874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877874 prefixEnd_7877874 := by exact prefixLift 7877874
  have htrace : WordTrace (prefixWord ++ tailWord_7877874) baseStart_7877874 baseEnd_7877874 := by
    simpa [prefixWord, tailWord_7877874, baseEnd_7877874] using wordTrace_append hprefix tailTrace_7877874
  have hstable : (prefixWord ++ tailWord_7877874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877874).length < 2 ^ (prefixWord ++ tailWord_7877874).sum := by decide
  have hdescent : baseEnd_7877874 < baseStart_7877874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877897 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 3]
def baseStart_7877897 : Nat := 118140960795 + 7877897 * 2 ^ 59
def prefixEnd_7877897 : Nat := 4983230072969 + 3 ^ 40 * 7877897 * 2
def baseEnd_7877897 : Nat := 4045147707612869425457717

theorem tailTrace_7877897 : CollatzResearch.WordTrace tailWord_7877897 prefixEnd_7877897 4045147707612869425457717 := by
  unfold tailWord_7877897
  simp only [CollatzResearch.WordTrace]
  refine ⟨287330508740732081536943945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191553672493821387691295963 287330508740732081536943945)
  ·
    refine ⟨215497881555549061152707959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287330508740732081536943945 215497881555549061152707959)
    ·
      refine ⟨323246822333323591729061939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215497881555549061152707959 323246822333323591729061939)
      ·
        refine ⟨484870233499985387593592909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323246822333323591729061939 484870233499985387593592909)
        ·
          refine ⟨181826337562494520347597341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484870233499985387593592909 181826337562494520347597341)
          ·
            refine ⟨68184876585935445130349003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181826337562494520347597341 68184876585935445130349003)
            ·
              refine ⟨102277314878903167695523505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68184876585935445130349003 102277314878903167695523505)
              ·
                refine ⟨76707986159177375771642629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102277314878903167695523505 76707986159177375771642629)
                ·
                  refine ⟨14382747404845757957182993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76707986159177375771642629 14382747404845757957182993)
                  ·
                    refine ⟨10787060553634318467887245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14382747404845757957182993 10787060553634318467887245)
                    ·
                      refine ⟨4045147707612869425457717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10787060553634318467887245 4045147707612869425457717)
                      ·
                        rfl

theorem cell23_7877897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_7877897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877897 prefixEnd_7877897 := by exact prefixLift 7877897
  have htrace : WordTrace (prefixWord ++ tailWord_7877897) baseStart_7877897 baseEnd_7877897 := by
    simpa [prefixWord, tailWord_7877897, baseEnd_7877897] using wordTrace_append hprefix tailTrace_7877897
  have hstable : (prefixWord ++ tailWord_7877897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877897).length < 2 ^ (prefixWord ++ tailWord_7877897).sum := by decide
  have hdescent : baseEnd_7877897 < baseStart_7877897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877914 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_7877914 : Nat := 118140960795 + 7877914 * 2 ^ 59
def prefixEnd_7877914 : Nat := 4983230072969 + 3 ^ 40 * 7877914 * 2
def baseEnd_7877914 : Nat := 4045156436783995858945139

theorem tailTrace_7877914 : CollatzResearch.WordTrace tailWord_7877914 prefixEnd_7877914 4045156436783995858945139 := by
  unfold tailWord_7877914
  simp only [CollatzResearch.WordTrace]
  refine ⟨71832782195417623360078199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191554085854446995626875197 71832782195417623360078199)
  ·
    refine ⟨107749173293126435040117299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71832782195417623360078199 107749173293126435040117299)
    ·
      refine ⟨161623759939689652560175949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107749173293126435040117299 161623759939689652560175949)
      ·
        refine ⟨60608909977383619710065981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161623759939689652560175949 60608909977383619710065981)
        ·
          refine ⟨22728341241518857391274743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60608909977383619710065981 22728341241518857391274743)
          ·
            refine ⟨34092511862278286086912115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22728341241518857391274743 34092511862278286086912115)
            ·
              refine ⟨51138767793417429130368173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34092511862278286086912115 51138767793417429130368173)
              ·
                refine ⟨19177037922531535923888065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51138767793417429130368173 19177037922531535923888065)
                ·
                  refine ⟨14382778441898651942916049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19177037922531535923888065 14382778441898651942916049)
                  ·
                    refine ⟨10787083831423988957187037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14382778441898651942916049 10787083831423988957187037)
                    ·
                      refine ⟨4045156436783995858945139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10787083831423988957187037 4045156436783995858945139)
                      ·
                        rfl

theorem cell23_7877914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_7877914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877914 prefixEnd_7877914 := by exact prefixLift 7877914
  have htrace : WordTrace (prefixWord ++ tailWord_7877914) baseStart_7877914 baseEnd_7877914 := by
    simpa [prefixWord, tailWord_7877914, baseEnd_7877914] using wordTrace_append hprefix tailTrace_7877914
  have hstable : (prefixWord ++ tailWord_7877914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877914).length < 2 ^ (prefixWord ++ tailWord_7877914).sum := by decide
  have hdescent : baseEnd_7877914 < baseStart_7877914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877938 : List Nat := [3, 2, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_7877938 : Nat := 118140960795 + 7877938 * 2 ^ 59
def prefixEnd_7877938 : Nat := 4983230072969 + 3 ^ 40 * 7877938 * 2
def baseEnd_7877938 : Nat := 1348389586773234588348343

theorem tailTrace_7877938 : CollatzResearch.WordTrace tailWord_7877938 prefixEnd_7877938 1348389586773234588348343 := by
  unfold tailWord_7877938
  simp only [CollatzResearch.WordTrace]
  refine ⟨71833001033395886384796617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191554669422389030359457645 71833001033395886384796617)
  ·
    refine ⟨53874750775046914788597463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71833001033395886384796617 53874750775046914788597463)
    ·
      refine ⟨80812126162570372182896195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53874750775046914788597463 80812126162570372182896195)
      ·
        refine ⟨121218189243855558274344293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80812126162570372182896195 121218189243855558274344293)
        ·
          refine ⟨22728410483222917176439555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121218189243855558274344293 22728410483222917176439555)
          ·
            refine ⟨34092615724834375764659333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22728410483222917176439555 34092615724834375764659333)
            ·
              refine ⟨6392365448406445455873625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34092615724834375764659333 6392365448406445455873625)
              ·
                refine ⟨4794274086304834091905219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6392365448406445455873625 4794274086304834091905219)
                ·
                  refine ⟨7191411129457251137857829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794274086304834091905219 7191411129457251137857829)
                  ·
                    refine ⟨1348389586773234588348343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191411129457251137857829 1348389586773234588348343)
                    ·
                      rfl

theorem cell23_7877938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_7877938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877938 prefixEnd_7877938 := by exact prefixLift 7877938
  have htrace : WordTrace (prefixWord ++ tailWord_7877938) baseStart_7877938 baseEnd_7877938 := by
    simpa [prefixWord, tailWord_7877938, baseEnd_7877938] using wordTrace_append hprefix tailTrace_7877938
  have hstable : (prefixWord ++ tailWord_7877938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877938).length < 2 ^ (prefixWord ++ tailWord_7877938).sum := by decide
  have hdescent : baseEnd_7877938 < baseStart_7877938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877944 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 3, 1, 3]
def baseStart_7877944 : Nat := 118140960795 + 7877944 * 2 ^ 59
def prefixEnd_7877944 : Nat := 4983230072969 + 3 ^ 40 * 7877944 * 2
def baseEnd_7877944 : Nat := 4045171841203630741570001

theorem tailTrace_7877944 : CollatzResearch.WordTrace tailWord_7877944 prefixEnd_7877944 4045171841203630741570001 := by
  unfold tailWord_7877944
  simp only [CollatzResearch.WordTrace]
  refine ⟨143666111485780904281952443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191554815314374539042603257 143666111485780904281952443)
  ·
    refine ⟨215499167228671356422928665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143666111485780904281952443 215499167228671356422928665)
    ·
      refine ⟨161624375421503517317196499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215499167228671356422928665 161624375421503517317196499)
      ·
        refine ⟨242436563132255275975794749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161624375421503517317196499 242436563132255275975794749)
        ·
          refine ⟨90913711174595728490923031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242436563132255275975794749 90913711174595728490923031)
          ·
            refine ⟨136370566761893592736384547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90913711174595728490923031 136370566761893592736384547)
            ·
              refine ⟨204555850142840389104576821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136370566761893592736384547 204555850142840389104576821)
              ·
                refine ⟨19177110950891286478554077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204555850142840389104576821 19177110950891286478554077)
                ·
                  refine ⟨7191416606584232429457779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19177110950891286478554077 7191416606584232429457779)
                  ·
                    refine ⟨10787124909876348644186669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7191416606584232429457779 10787124909876348644186669)
                    ·
                      refine ⟨4045171841203630741570001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10787124909876348644186669 4045171841203630741570001)
                      ·
                        rfl

theorem cell23_7877944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_7877944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877944 prefixEnd_7877944 := by exact prefixLift 7877944
  have htrace : WordTrace (prefixWord ++ tailWord_7877944) baseStart_7877944 baseEnd_7877944 := by
    simpa [prefixWord, tailWord_7877944, baseEnd_7877944] using wordTrace_append hprefix tailTrace_7877944
  have hstable : (prefixWord ++ tailWord_7877944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877944).length < 2 ^ (prefixWord ++ tailWord_7877944).sum := by decide
  have hdescent : baseEnd_7877944 < baseStart_7877944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877965 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_7877965 : Nat := 118140960795 + 7877965 * 2 ^ 59
def prefixEnd_7877965 : Nat := 4983230072969 + 3 ^ 40 * 7877965 * 2
def baseEnd_7877965 : Nat := 4045182624297375159407405

theorem tailTrace_7877965 : CollatzResearch.WordTrace tailWord_7877965 prefixEnd_7877965 4045182624297375159407405 := by
  unfold tailWord_7877965
  simp only [CollatzResearch.WordTrace]
  refine ⟨287332988904485729150419349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191555325936323819433612899 287332988904485729150419349)
  ·
    refine ⟨13468733854897768553925907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287332988904485729150419349 13468733854897768553925907)
    ·
      refine ⟨20203100782346652830888861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13468733854897768553925907 20203100782346652830888861)
      ·
        refine ⟨7576162793379994811583323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20203100782346652830888861 7576162793379994811583323)
        ·
          refine ⟨11364244190069992217374985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7576162793379994811583323 11364244190069992217374985)
          ·
            refine ⟨8523183142552494163031239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11364244190069992217374985 8523183142552494163031239)
            ·
              refine ⟨12784774713828741244546859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8523183142552494163031239 12784774713828741244546859)
              ·
                refine ⟨19177162070743111866820289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784774713828741244546859 19177162070743111866820289)
                ·
                  refine ⟨14382871553057333900115217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19177162070743111866820289 14382871553057333900115217)
                  ·
                    refine ⟨10787153664793000425086413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14382871553057333900115217 10787153664793000425086413)
                    ·
                      refine ⟨4045182624297375159407405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10787153664793000425086413 4045182624297375159407405)
                      ·
                        rfl

theorem cell23_7877965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_7877965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877965 prefixEnd_7877965 := by exact prefixLift 7877965
  have htrace : WordTrace (prefixWord ++ tailWord_7877965) baseStart_7877965 baseEnd_7877965 := by
    simpa [prefixWord, tailWord_7877965, baseEnd_7877965] using wordTrace_append hprefix tailTrace_7877965
  have hstable : (prefixWord ++ tailWord_7877965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877965).length < 2 ^ (prefixWord ++ tailWord_7877965).sum := by decide
  have hdescent : baseEnd_7877965 < baseStart_7877965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877977 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 1, 6]
def baseStart_7877977 : Nat := 118140960795 + 7877977 * 2 ^ 59
def prefixEnd_7877977 : Nat := 4983230072969 + 3 ^ 40 * 7877977 * 2
def baseEnd_7877977 : Nat := 1348396262021743037485783

theorem tailTrace_7877977 : CollatzResearch.WordTrace tailWord_7877977 prefixEnd_7877977 1348396262021743037485783 := by
  unfold tailWord_7877977
  simp only [CollatzResearch.WordTrace]
  refine ⟨287333426580442255199856185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191555617720294836799904123 287333426580442255199856185)
  ·
    refine ⟨215500069935331691399892139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287333426580442255199856185 215500069935331691399892139)
    ·
      refine ⟨323250104902997537099838209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215500069935331691399892139 323250104902997537099838209)
      ·
        refine ⟨242437578677248152824878657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323250104902997537099838209 242437578677248152824878657)
        ·
          refine ⟨181828184007936114618658993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242437578677248152824878657 181828184007936114618658993)
          ·
            refine ⟨136371138005952085963994245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181828184007936114618658993 136371138005952085963994245)
            ·
              refine ⟨25569588376116016118248921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136371138005952085963994245 25569588376116016118248921)
              ·
                refine ⟨19177191282087012088686691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25569588376116016118248921 19177191282087012088686691)
                ·
                  refine ⟨28765786923130518133030037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19177191282087012088686691 28765786923130518133030037)
                  ·
                    refine ⟨1348396262021743037485783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28765786923130518133030037 1348396262021743037485783)
                    ·
                      rfl

theorem cell23_7877977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_7877977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877977 prefixEnd_7877977 := by exact prefixLift 7877977
  have htrace : WordTrace (prefixWord ++ tailWord_7877977) baseStart_7877977 baseEnd_7877977 := by
    simpa [prefixWord, tailWord_7877977, baseEnd_7877977] using wordTrace_append hprefix tailTrace_7877977
  have hstable : (prefixWord ++ tailWord_7877977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877977).length < 2 ^ (prefixWord ++ tailWord_7877977).sum := by decide
  have hdescent : baseEnd_7877977 < baseStart_7877977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878001 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 3, 2, 2]
def baseStart_7878001 : Nat := 118140960795 + 7878001 * 2 ^ 59
def prefixEnd_7878001 : Nat := 4983230072969 + 3 ^ 40 * 7878001 * 2
def baseEnd_7878001 : Nat := 4045201109600937018557239

theorem tailTrace_7878001 : CollatzResearch.WordTrace tailWord_7878001 prefixEnd_7878001 4045201109600937018557239 := by
  unfold tailWord_7878001
  simp only [CollatzResearch.WordTrace]
  refine ⟨287334301932355307298729857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191556201288236871532486571 287334301932355307298729857)
  ·
    refine ⟨215500726449266480474047393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287334301932355307298729857 215500726449266480474047393)
    ·
      refine ⟨161625544836949860355535545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215500726449266480474047393 161625544836949860355535545)
      ·
        refine ⟨121219158627712395266651659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161625544836949860355535545 121219158627712395266651659)
        ·
          refine ⟨181828737941568592899977489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121219158627712395266651659 181828737941568592899977489)
          ·
            refine ⟨136371553456176444674983117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181828737941568592899977489 136371553456176444674983117)
            ·
              refine ⟨51139332546066166753118669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136371553456176444674983117 51139332546066166753118669)
              ·
                refine ⟨19177249704774812532419501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51139332546066166753118669 19177249704774812532419501)
                ·
                  refine ⟨7191468639290554699657313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19177249704774812532419501 7191468639290554699657313)
                  ·
                    refine ⟨5393601479467916024742985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7191468639290554699657313 5393601479467916024742985)
                    ·
                      refine ⟨4045201109600937018557239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393601479467916024742985 4045201109600937018557239)
                      ·
                        rfl

theorem cell23_7878001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_7878001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878001 prefixEnd_7878001 := by exact prefixLift 7878001
  have htrace : WordTrace (prefixWord ++ tailWord_7878001) baseStart_7878001 baseEnd_7878001 := by
    simpa [prefixWord, tailWord_7878001, baseEnd_7878001] using wordTrace_append hprefix tailTrace_7878001
  have hstable : (prefixWord ++ tailWord_7878001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878001).length < 2 ^ (prefixWord ++ tailWord_7878001).sum := by decide
  have hdescent : baseEnd_7878001 < baseStart_7878001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878011 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 2, 4]
def baseStart_7878011 : Nat := 118140960795 + 7878011 * 2 ^ 59
def prefixEnd_7878011 : Nat := 4983230072969 + 3 ^ 40 * 7878011 * 2
def baseEnd_7878011 : Nat := 1348402081469160659810731

theorem tailTrace_7878011 : CollatzResearch.WordTrace tailWord_7878011 prefixEnd_7878011 1348402081469160659810731 := by
  unfold tailWord_7878011
  simp only [CollatzResearch.WordTrace]
  refine ⟨287334666662319079006593887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191556444441546052671062591 287334666662319079006593887)
  ·
    refine ⟨431001999993478618509890831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287334666662319079006593887 431001999993478618509890831)
    ·
      refine ⟨646502999990217927764836247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431001999993478618509890831 646502999990217927764836247)
      ·
        refine ⟨969754499985326891647254371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646502999990217927764836247 969754499985326891647254371)
        ·
          refine ⟨1454631749977990337470881557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969754499985326891647254371 1454631749977990337470881557)
          ·
            refine ⟨68185863280218297068947573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1454631749977990337470881557 68185863280218297068947573)
            ·
              refine ⟨6392424682520465350213835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68185863280218297068947573 6392424682520465350213835)
              ·
                refine ⟨9588637023780698025320753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6392424682520465350213835 9588637023780698025320753)
                ·
                  refine ⟨7191477767835523518990565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9588637023780698025320753 7191477767835523518990565)
                  ·
                    refine ⟨1348402081469160659810731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191477767835523518990565 1348402081469160659810731)
                    ·
                      rfl

theorem cell23_7878011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 4].length) (baseStart_7878011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878011 prefixEnd_7878011 := by exact prefixLift 7878011
  have htrace : WordTrace (prefixWord ++ tailWord_7878011) baseStart_7878011 baseEnd_7878011 := by
    simpa [prefixWord, tailWord_7878011, baseEnd_7878011] using wordTrace_append hprefix tailTrace_7878011
  have hstable : (prefixWord ++ tailWord_7878011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878011).length < 2 ^ (prefixWord ++ tailWord_7878011).sum := by decide
  have hdescent : baseEnd_7878011 < baseStart_7878011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878018 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_7878018 : Nat := 118140960795 + 7878018 * 2 ^ 59
def prefixEnd_7878018 : Nat := 4983230072969 + 3 ^ 40 * 7878018 * 2
def baseEnd_7878018 : Nat := 4045209838772063452044661

theorem tailTrace_7878018 : CollatzResearch.WordTrace tailWord_7878018 prefixEnd_7878018 4045209838772063452044661 := by
  unfold tailWord_7878018
  simp only [CollatzResearch.WordTrace]
  refine ⟨71833730493323429800524677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191556614648862479468065805 71833730493323429800524677)
  ·
    refine ⟨13468824467498143087598377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71833730493323429800524677 13468824467498143087598377)
    ·
      refine ⟨10101618350623607315698783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13468824467498143087598377 10101618350623607315698783)
      ·
        refine ⟨15152427525935410973548175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10101618350623607315698783 15152427525935410973548175)
        ·
          refine ⟨22728641288903116460322263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15152427525935410973548175 22728641288903116460322263)
          ·
            refine ⟨34092961933354674690483395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22728641288903116460322263 34092961933354674690483395)
            ·
              refine ⟨51139442900032012035725093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34092961933354674690483395 51139442900032012035725093)
              ·
                refine ⟨9588645543756002256698455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51139442900032012035725093 9588645543756002256698455)
                ·
                  refine ⟨14382968315634003385047683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9588645543756002256698455 14382968315634003385047683)
                  ·
                    refine ⟨21574452473451005077571525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14382968315634003385047683 21574452473451005077571525)
                    ·
                      refine ⟨4045209838772063452044661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21574452473451005077571525 4045209838772063452044661)
                      ·
                        rfl

theorem cell23_7878018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_7878018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878018 prefixEnd_7878018 := by exact prefixLift 7878018
  have htrace : WordTrace (prefixWord ++ tailWord_7878018) baseStart_7878018 baseEnd_7878018 := by
    simpa [prefixWord, tailWord_7878018, baseEnd_7878018] using wordTrace_append hprefix tailTrace_7878018
  have hstable : (prefixWord ++ tailWord_7878018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878018).length < 2 ^ (prefixWord ++ tailWord_7878018).sum := by decide
  have hdescent : baseEnd_7878018 < baseStart_7878018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878024 : List Nat := [2, 1, 3, 3, 1, 2, 4, 7]
def baseStart_7878024 : Nat := 118140960795 + 7878024 * 2 ^ 59
def prefixEnd_7878024 : Nat := 4983230072969 + 3 ^ 40 * 7878024 * 2
def baseEnd_7878024 : Nat := 149822700727999645502579

theorem tailTrace_7878024 : CollatzResearch.WordTrace tailWord_7878024 prefixEnd_7878024 149822700727999645502579 := by
  unfold tailWord_7878024
  simp only [CollatzResearch.WordTrace]
  refine ⟨143667570405635991113408563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191556760540847988151211417 143667570405635991113408563)
  ·
    refine ⟨215501355608453986670112845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143667570405635991113408563 215501355608453986670112845)
    ·
      refine ⟨80813008353170245001292317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215501355608453986670112845 80813008353170245001292317)
      ·
        refine ⟨30304878132438841875484619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80813008353170245001292317 30304878132438841875484619)
        ·
          refine ⟨45457317198658262813226929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30304878132438841875484619 45457317198658262813226929)
          ·
            refine ⟨34092987898993697109920197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45457317198658262813226929 34092987898993697109920197)
            ·
              refine ⟨6392435231061318208110037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34092987898993697109920197 6392435231061318208110037)
              ·
                refine ⟨149822700727999645502579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6392435231061318208110037 149822700727999645502579)
                ·
                  rfl

theorem cell23_7878024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 7].length) (baseStart_7878024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878024 prefixEnd_7878024 := by exact prefixLift 7878024
  have htrace : WordTrace (prefixWord ++ tailWord_7878024) baseStart_7878024 baseEnd_7878024 := by
    simpa [prefixWord, tailWord_7878024, baseEnd_7878024] using wordTrace_append hprefix tailTrace_7878024
  have hstable : (prefixWord ++ tailWord_7878024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878024).length < 2 ^ (prefixWord ++ tailWord_7878024).sum := by decide
  have hdescent : baseEnd_7878024 < baseStart_7878024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878051 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 3]
def baseStart_7878051 : Nat := 118140960795 + 7878051 * 2 ^ 59
def prefixEnd_7878051 : Nat := 4983230072969 + 3 ^ 40 * 7878051 * 2
def baseEnd_7878051 : Nat := 4045226783633661822932009

theorem tailTrace_7878051 : CollatzResearch.WordTrace tailWord_7878051 prefixEnd_7878051 4045226783633661822932009 := by
  unfold tailWord_7878051
  simp only [CollatzResearch.WordTrace]
  refine ⟨287336125582174165838050007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191557417054782777225366671 287336125582174165838050007)
  ·
    refine ⟨431004188373261248757075011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287336125582174165838050007 431004188373261248757075011)
    ·
      refine ⟨646506282559891873135612517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431004188373261248757075011 646506282559891873135612517)
      ·
        refine ⟨121219927979979726212927347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 646506282559891873135612517 121219927979979726212927347)
        ·
          refine ⟨181829891969969589319391021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121219927979979726212927347 181829891969969589319391021)
          ·
            refine ⟨68186209488738595994771633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181829891969969589319391021 68186209488738595994771633)
            ·
              refine ⟨51139657116553946996078725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68186209488738595994771633 51139657116553946996078725)
              ·
                refine ⟨9588685709353865061764761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51139657116553946996078725 9588685709353865061764761)
                ·
                  refine ⟨7191514282015398796323571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9588685709353865061764761 7191514282015398796323571)
                  ·
                    refine ⟨10787271423023098194485357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7191514282015398796323571 10787271423023098194485357)
                    ·
                      refine ⟨4045226783633661822932009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10787271423023098194485357 4045226783633661822932009)
                      ·
                        rfl

theorem cell23_7878051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_7878051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878051 prefixEnd_7878051 := by exact prefixLift 7878051
  have htrace : WordTrace (prefixWord ++ tailWord_7878051) baseStart_7878051 baseEnd_7878051 := by
    simpa [prefixWord, tailWord_7878051, baseEnd_7878051] using wordTrace_append hprefix tailTrace_7878051
  have hstable : (prefixWord ++ tailWord_7878051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878051).length < 2 ^ (prefixWord ++ tailWord_7878051).sum := by decide
  have hdescent : baseEnd_7878051 < baseStart_7878051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878067 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 2, 6]
def baseStart_7878067 : Nat := 118140960795 + 7878067 * 2 ^ 59
def prefixEnd_7878067 : Nat := 4983230072969 + 3 ^ 40 * 7878067 * 2
def baseEnd_7878067 : Nat := 1348411666441377920110645

theorem tailTrace_7878067 : CollatzResearch.WordTrace tailWord_7878067 prefixEnd_7878067 1348411666441377920110645 := by
  unfold tailWord_7878067
  simp only [CollatzResearch.WordTrace]
  refine ⟨287336709150116200570632455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191557806100077467047088303 287336709150116200570632455)
  ·
    refine ⟨431005063725174300855948683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287336709150116200570632455 431005063725174300855948683)
    ·
      refine ⟨646507595587761451283923025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431005063725174300855948683 646507595587761451283923025)
      ·
        refine ⟨484880696690821088462942269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646507595587761451283923025 484880696690821088462942269)
        ·
          refine ⟨181830261259057908173603351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484880696690821088462942269 181830261259057908173603351)
          ·
            refine ⟨272745391888586862260405027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181830261259057908173603351 272745391888586862260405027)
            ·
              refine ⟨409118087832880293390607541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272745391888586862260405027 409118087832880293390607541)
              ·
                refine ⟨38354820734332527505369457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409118087832880293390607541 38354820734332527505369457)
                ·
                  refine ⟨28766115550749395629027093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38354820734332527505369457 28766115550749395629027093)
                  ·
                    refine ⟨1348411666441377920110645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28766115550749395629027093 1348411666441377920110645)
                    ·
                      rfl

theorem cell23_7878067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 6].length) (baseStart_7878067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878067 prefixEnd_7878067 := by exact prefixLift 7878067
  have htrace : WordTrace (prefixWord ++ tailWord_7878067) baseStart_7878067 baseEnd_7878067 := by
    simpa [prefixWord, tailWord_7878067, baseEnd_7878067] using wordTrace_append hprefix tailTrace_7878067
  have hstable : (prefixWord ++ tailWord_7878067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878067).length < 2 ^ (prefixWord ++ tailWord_7878067).sum := by decide
  have hdescent : baseEnd_7878067 < baseStart_7878067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878082 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7878082 : Nat := 118140960795 + 7878082 * 2 ^ 59
def prefixEnd_7878082 : Nat := 4983230072969 + 3 ^ 40 * 7878082 * 2
def baseEnd_7878082 : Nat := 4045242701533951201644367

theorem tailTrace_7878082 : CollatzResearch.WordTrace tailWord_7878082 prefixEnd_7878082 4045242701533951201644367 := by
  unfold tailWord_7878082
  simp only [CollatzResearch.WordTrace]
  refine ⟨71834314061265464533107125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191558170830041238754952333 71834314061265464533107125)
  ·
    refine ⟨6734466943243637299978793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71834314061265464533107125 6734466943243637299978793)
    ·
      refine ⟨5050850207432727974984095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6734466943243637299978793 5050850207432727974984095)
      ·
        refine ⟨7576275311149091962476143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050850207432727974984095 7576275311149091962476143)
        ·
          refine ⟨11364412966723637943714215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7576275311149091962476143 11364412966723637943714215)
          ·
            refine ⟨17046619450085456915571323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11364412966723637943714215 17046619450085456915571323)
            ·
              refine ⟨25569929175128185373356985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17046619450085456915571323 25569929175128185373356985)
              ·
                refine ⟨19177446881346139030017739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25569929175128185373356985 19177446881346139030017739)
                ·
                  refine ⟨28766170322019208545026609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19177446881346139030017739 28766170322019208545026609)
                  ·
                    refine ⟨21574627741514406408769957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28766170322019208545026609 21574627741514406408769957)
                    ·
                      refine ⟨4045242701533951201644367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21574627741514406408769957 4045242701533951201644367)
                      ·
                        rfl

theorem cell23_7878082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7878082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878082 prefixEnd_7878082 := by exact prefixLift 7878082
  have htrace : WordTrace (prefixWord ++ tailWord_7878082) baseStart_7878082 baseEnd_7878082 := by
    simpa [prefixWord, tailWord_7878082, baseEnd_7878082] using wordTrace_append hprefix tailTrace_7878082
  have hstable : (prefixWord ++ tailWord_7878082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878082).length < 2 ^ (prefixWord ++ tailWord_7878082).sum := by decide
  have hdescent : baseEnd_7878082 < baseStart_7878082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878091 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 6, 2, 2]
def baseStart_7878091 : Nat := 118140960795 + 7878091 * 2 ^ 59
def prefixEnd_7878091 : Nat := 4983230072969 + 3 ^ 40 * 7878091 * 2
def baseEnd_7878091 : Nat := 4045247322859841666431825

theorem tailTrace_7878091 : CollatzResearch.WordTrace tailWord_7878091 prefixEnd_7878091 4045247322859841666431825 := by
  unfold tailWord_7878091
  simp only [CollatzResearch.WordTrace]
  refine ⟨287337584502029252669506127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191558389668019501779670751 287337584502029252669506127)
  ·
    refine ⟨431006376753043879004259191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287337584502029252669506127 431006376753043879004259191)
    ·
      refine ⟨646509565129565818506388787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431006376753043879004259191 646509565129565818506388787)
      ·
        refine ⟨969764347694348727759583181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646509565129565818506388787 969764347694348727759583181)
        ·
          refine ⟨363661630385380772909843693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 969764347694348727759583181 363661630385380772909843693)
          ·
            refine ⟨136373111394517789841191385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363661630385380772909843693 136373111394517789841191385)
            ·
              refine ⟨102279833545888342380893539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136373111394517789841191385 102279833545888342380893539)
              ·
                refine ⟨153419750318832513571340309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102279833545888342380893539 153419750318832513571340309)
                ·
                  refine ⟨7191550796195274073656577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153419750318832513571340309 7191550796195274073656577)
                  ·
                    refine ⟨5393663097146455555242433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7191550796195274073656577 5393663097146455555242433)
                    ·
                      refine ⟨4045247322859841666431825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393663097146455555242433 4045247322859841666431825)
                      ·
                        rfl

theorem cell23_7878091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 2, 2].length) (baseStart_7878091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878091 prefixEnd_7878091 := by exact prefixLift 7878091
  have htrace : WordTrace (prefixWord ++ tailWord_7878091) baseStart_7878091 baseEnd_7878091 := by
    simpa [prefixWord, tailWord_7878091, baseEnd_7878091] using wordTrace_append hprefix tailTrace_7878091
  have hstable : (prefixWord ++ tailWord_7878091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878091).length < 2 ^ (prefixWord ++ tailWord_7878091).sum := by decide
  have hdescent : baseEnd_7878091 < baseStart_7878091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878094 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_7878094 : Nat := 118140960795 + 7878094 * 2 ^ 59
def prefixEnd_7878094 : Nat := 4983230072969 + 3 ^ 40 * 7878094 * 2
def baseEnd_7878094 : Nat := 4045248863301805154694311

theorem tailTrace_7878094 : CollatzResearch.WordTrace tailWord_7878094 prefixEnd_7878094 4045248863301805154694311 := by
  unfold tailWord_7878094
  simp only [CollatzResearch.WordTrace]
  refine ⟨35917211740127298022733167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191558462614012256121243557 35917211740127298022733167)
  ·
    refine ⟨53875817610190947034099751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35917211740127298022733167 53875817610190947034099751)
    ·
      refine ⟨80813726415286420551149627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53875817610190947034099751 80813726415286420551149627)
      ·
        refine ⟨121220589622929630826724441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80813726415286420551149627 121220589622929630826724441)
        ·
          refine ⟨90915442217197223120043331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121220589622929630826724441 90915442217197223120043331)
          ·
            refine ⟨136373163325795834680064997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90915442217197223120043331 136373163325795834680064997)
            ·
              refine ⟨25569968123586719002512187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136373163325795834680064997 25569968123586719002512187)
              ·
                refine ⟨38354952185380078503768281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25569968123586719002512187 38354952185380078503768281)
                ·
                  refine ⟨28766214139035058877826211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38354952185380078503768281 28766214139035058877826211)
                  ·
                    refine ⟨43149321208552588316739317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28766214139035058877826211 43149321208552588316739317)
                    ·
                      refine ⟨4045248863301805154694311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43149321208552588316739317 4045248863301805154694311)
                      ·
                        rfl

theorem cell23_7878094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_7878094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878094 prefixEnd_7878094 := by exact prefixLift 7878094
  have htrace : WordTrace (prefixWord ++ tailWord_7878094) baseStart_7878094 baseEnd_7878094 := by
    simpa [prefixWord, tailWord_7878094, baseEnd_7878094] using wordTrace_append hprefix tailTrace_7878094
  have hstable : (prefixWord ++ tailWord_7878094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878094).length < 2 ^ (prefixWord ++ tailWord_7878094).sum := by decide
  have hdescent : baseEnd_7878094 < baseStart_7878094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878125 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_7878125 : Nat := 118140960795 + 7878125 * 2 ^ 59
def prefixEnd_7878125 : Nat := 4983230072969 + 3 ^ 40 * 7878125 * 2
def baseEnd_7878125 : Nat := 4045264781202094533406669

theorem tailTrace_7878125 : CollatzResearch.WordTrace tailWord_7878125 prefixEnd_7878125 4045264781202094533406669 := by
  unfold tailWord_7878125
  simp only [CollatzResearch.WordTrace]
  refine ⟨287338824583906076476243829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191559216389270717650829219 287338824583906076476243829)
  ·
    refine ⟨26938014804741194669647859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287338824583906076476243829 26938014804741194669647859)
    ·
      refine ⟨40407022207111792004471789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26938014804741194669647859 40407022207111792004471789)
      ·
        refine ⟨15152633327666922001676921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40407022207111792004471789 15152633327666922001676921)
        ·
          refine ⟨11364474995750191501257691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15152633327666922001676921 11364474995750191501257691)
          ·
            refine ⟨17046712493625287251886537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11364474995750191501257691 17046712493625287251886537)
            ·
              refine ⟨12785034370218965438914903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17046712493625287251886537 12785034370218965438914903)
              ·
                refine ⟨19177551555328448158372355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12785034370218965438914903 19177551555328448158372355)
                ·
                  refine ⟨28766327332992672237558533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19177551555328448158372355 28766327332992672237558533)
                  ·
                    refine ⟨5393686374936126044542225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28766327332992672237558533 5393686374936126044542225)
                    ·
                      refine ⟨4045264781202094533406669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393686374936126044542225 4045264781202094533406669)
                      ·
                        rfl

theorem cell23_7878125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_7878125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878125 prefixEnd_7878125 := by exact prefixLift 7878125
  have htrace : WordTrace (prefixWord ++ tailWord_7878125) baseStart_7878125 baseEnd_7878125 := by
    simpa [prefixWord, tailWord_7878125, baseEnd_7878125] using wordTrace_append hprefix tailTrace_7878125
  have hstable : (prefixWord ++ tailWord_7878125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878125).length < 2 ^ (prefixWord ++ tailWord_7878125).sum := by decide
  have hdescent : baseEnd_7878125 < baseStart_7878125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878194 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_7878194 : Nat := 118140960795 + 7878194 * 2 ^ 59
def prefixEnd_7878194 : Nat := 4983230072969 + 3 ^ 40 * 7878194 * 2
def baseEnd_7878194 : Nat := 4045300211367254763443851

theorem tailTrace_7878194 : CollatzResearch.WordTrace tailWord_7878194 prefixEnd_7878194 4045300211367254763443851 := by
  unfold tailWord_7878194
  simp only [CollatzResearch.WordTrace]
  refine ⟨71835335305164025315126409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191560894147104067507003757 71835335305164025315126409)
  ·
    refine ⟨53876501478873018986344807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71835335305164025315126409 53876501478873018986344807)
    ·
      refine ⟨80814752218309528479517211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53876501478873018986344807 80814752218309528479517211)
      ·
        refine ⟨121222128327464292719275817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80814752218309528479517211 121222128327464292719275817)
        ·
          refine ⟨90916596245598219539456863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121222128327464292719275817 90916596245598219539456863)
          ·
            refine ⟨136374894368397329309185295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90916596245598219539456863 136374894368397329309185295)
            ·
              refine ⟨204562341552595993963777943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136374894368397329309185295 204562341552595993963777943)
              ·
                refine ⟨306843512328893990945666915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204562341552595993963777943 306843512328893990945666915)
                ·
                  refine ⟨460265268493340986418500373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306843512328893990945666915 460265268493340986418500373)
                  ·
                    refine ⟨21574934460625358738367205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 460265268493340986418500373 21574934460625358738367205)
                    ·
                      refine ⟨4045300211367254763443851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21574934460625358738367205 4045300211367254763443851)
                      ·
                        rfl

theorem cell23_7878194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_7878194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878194 prefixEnd_7878194 := by exact prefixLift 7878194
  have htrace : WordTrace (prefixWord ++ tailWord_7878194) baseStart_7878194 baseEnd_7878194 := by
    simpa [prefixWord, tailWord_7878194, baseEnd_7878194] using wordTrace_append hprefix tailTrace_7878194
  have hstable : (prefixWord ++ tailWord_7878194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878194).length < 2 ^ (prefixWord ++ tailWord_7878194).sum := by decide
  have hdescent : baseEnd_7878194 < baseStart_7878194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878201 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 3]
def baseStart_7878201 : Nat := 118140960795 + 7878201 * 2 ^ 59
def prefixEnd_7878201 : Nat := 4983230072969 + 3 ^ 40 * 7878201 * 2
def baseEnd_7878201 : Nat := 4045303805731836236056319

theorem tailTrace_7878201 : CollatzResearch.WordTrace tailWord_7878201 prefixEnd_7878201 4045303805731836236056319 := by
  unfold tailWord_7878201
  simp only [CollatzResearch.WordTrace]
  refine ⟨287341596531630741456010457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191561064354420494304006971 287341596531630741456010457)
  ·
    refine ⟨215506197398723056092007843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287341596531630741456010457 215506197398723056092007843)
    ·
      refine ⟨323259296098084584138011765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215506197398723056092007843 323259296098084584138011765)
      ·
        refine ⟨30305559009195429762938603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323259296098084584138011765 30305559009195429762938603)
        ·
          refine ⟨45458338513793144644407905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30305559009195429762938603 45458338513793144644407905)
          ·
            refine ⟨34093753885344858483305929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45458338513793144644407905 34093753885344858483305929)
            ·
              refine ⟨25570315414008643862479447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34093753885344858483305929 25570315414008643862479447)
              ·
                refine ⟨38355473121012965793719171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25570315414008643862479447 38355473121012965793719171)
                ·
                  refine ⟨57533209681519448690578757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38355473121012965793719171 57533209681519448690578757)
                  ·
                    refine ⟨10787476815284896629483517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57533209681519448690578757 10787476815284896629483517)
                    ·
                      refine ⟨4045303805731836236056319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10787476815284896629483517 4045303805731836236056319)
                      ·
                        rfl

theorem cell23_7878201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_7878201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878201 prefixEnd_7878201 := by exact prefixLift 7878201
  have htrace : WordTrace (prefixWord ++ tailWord_7878201) baseStart_7878201 baseEnd_7878201 := by
    simpa [prefixWord, tailWord_7878201, baseEnd_7878201] using wordTrace_append hprefix tailTrace_7878201
  have hstable : (prefixWord ++ tailWord_7878201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878201).length < 2 ^ (prefixWord ++ tailWord_7878201).sum := by decide
  have hdescent : baseEnd_7878201 < baseStart_7878201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878225 : List Nat := [1, 2, 2, 1, 3, 2, 5, 2, 1, 4]
def baseStart_7878225 : Nat := 118140960795 + 7878225 * 2 ^ 59
def prefixEnd_7878225 : Nat := 4983230072969 + 3 ^ 40 * 7878225 * 2
def baseEnd_7878225 : Nat := 1348438709755848047385403

theorem tailTrace_7878225 : CollatzResearch.WordTrace tailWord_7878225 prefixEnd_7878225 1348438709755848047385403 := by
  unfold tailWord_7878225
  simp only [CollatzResearch.WordTrace]
  refine ⟨287342471883543793554884129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191561647922362529036589419 287342471883543793554884129)
  ·
    refine ⟨215506853912657845166163097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287342471883543793554884129 215506853912657845166163097)
    ·
      refine ⟨161630140434493383874622323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215506853912657845166163097 161630140434493383874622323)
      ·
        refine ⟨242445210651740075811933485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161630140434493383874622323 242445210651740075811933485)
        ·
          refine ⟨90916953994402528429475057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242445210651740075811933485 90916953994402528429475057)
          ·
            refine ⟨68187715495801896322106293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90916953994402528429475057 68187715495801896322106293)
            ·
              refine ⟨6392598327731427780197465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68187715495801896322106293 6392598327731427780197465)
              ·
                refine ⟨4794448745798570835148099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6392598327731427780197465 4794448745798570835148099)
                ·
                  refine ⟨7191673118697856252722149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794448745798570835148099 7191673118697856252722149)
                  ·
                    refine ⟨1348438709755848047385403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191673118697856252722149 1348438709755848047385403)
                    ·
                      rfl

theorem cell23_7878225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_7878225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878225 prefixEnd_7878225 := by exact prefixLift 7878225
  have htrace : WordTrace (prefixWord ++ tailWord_7878225) baseStart_7878225 baseEnd_7878225 := by
    simpa [prefixWord, tailWord_7878225, baseEnd_7878225] using wordTrace_append hprefix tailTrace_7878225
  have hstable : (prefixWord ++ tailWord_7878225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878225).length < 2 ^ (prefixWord ++ tailWord_7878225).sum := by decide
  have hdescent : baseEnd_7878225 < baseStart_7878225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878265 : List Nat := [1, 2, 1, 3, 3, 1, 2, 5, 1, 1, 3]
def baseStart_7878265 : Nat := 118140960795 + 7878265 * 2 ^ 59
def prefixEnd_7878265 : Nat := 4983230072969 + 3 ^ 40 * 7878265 * 2
def baseEnd_7878265 : Nat := 4045336668493723985656025

theorem tailTrace_7878265 : CollatzResearch.WordTrace tailWord_7878265 prefixEnd_7878265 4045336668493723985656025 := by
  unfold tailWord_7878265
  simp only [CollatzResearch.WordTrace]
  refine ⟨287343930803398880386340249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191562620535599253590893499 287343930803398880386340249)
  ·
    refine ⟨215507948102549160289755187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287343930803398880386340249 215507948102549160289755187)
    ·
      refine ⟨323261922153823740434632781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215507948102549160289755187 323261922153823740434632781)
      ·
        refine ⟨121223220807683902662987293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323261922153823740434632781 121223220807683902662987293)
        ·
          refine ⟨45458707802881463498620235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121223220807683902662987293 45458707802881463498620235)
          ·
            refine ⟨68188061704322195247930353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45458707802881463498620235 68188061704322195247930353)
            ·
              refine ⟨51141046278241646435947765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68188061704322195247930353 51141046278241646435947765)
              ·
                refine ⟨4794473088585154353370103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51141046278241646435947765 4794473088585154353370103)
                ·
                  refine ⟨7191709632877731530055155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794473088585154353370103 7191709632877731530055155)
                  ·
                    refine ⟨10787564449316597295082733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7191709632877731530055155 10787564449316597295082733)
                    ·
                      refine ⟨4045336668493723985656025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10787564449316597295082733 4045336668493723985656025)
                      ·
                        rfl

theorem cell23_7878265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_7878265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878265 prefixEnd_7878265 := by exact prefixLift 7878265
  have htrace : WordTrace (prefixWord ++ tailWord_7878265) baseStart_7878265 baseEnd_7878265 := by
    simpa [prefixWord, tailWord_7878265, baseEnd_7878265] using wordTrace_append hprefix tailTrace_7878265
  have hstable : (prefixWord ++ tailWord_7878265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878265).length < 2 ^ (prefixWord ++ tailWord_7878265).sum := by decide
  have hdescent : baseEnd_7878265 < baseStart_7878265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878271 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 4, 6, 2]
def baseStart_7878271 : Nat := 118140960795 + 7878271 * 2 ^ 59
def prefixEnd_7878271 : Nat := 4983230072969 + 3 ^ 40 * 7878271 * 2
def baseEnd_7878271 : Nat := 4045339749377650962180997

theorem tailTrace_7878271 : CollatzResearch.WordTrace tailWord_7878271 prefixEnd_7878271 4045339749377650962180997 := by
  unfold tailWord_7878271
  simp only [CollatzResearch.WordTrace]
  refine ⟨287344149641377143411058667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191562766427584762274039111 287344149641377143411058667)
  ·
    refine ⟨431016224462065715116588001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287344149641377143411058667 431016224462065715116588001)
    ·
      refine ⟨323262168346549286337441001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431016224462065715116588001 323262168346549286337441001)
      ·
        refine ⟨242446626259911964753080751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323262168346549286337441001 242446626259911964753080751)
        ·
          refine ⟨363669939389867947129621127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242446626259911964753080751 363669939389867947129621127)
          ·
            refine ⟨545504909084801920694431691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363669939389867947129621127 545504909084801920694431691)
            ·
              refine ⟨818257363627202881041647537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545504909084801920694431691 818257363627202881041647537)
              ·
                refine ⟨613693022720402160781235653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818257363627202881041647537 613693022720402160781235653)
                ·
                  refine ⟨115067441760075405146481685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613693022720402160781235653 115067441760075405146481685)
                  ·
                    refine ⟨5393786332503534616241329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115067441760075405146481685 5393786332503534616241329)
                    ·
                      refine ⟨4045339749377650962180997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393786332503534616241329 4045339749377650962180997)
                      ·
                        rfl

theorem cell23_7878271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_7878271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878271 prefixEnd_7878271 := by exact prefixLift 7878271
  have htrace : WordTrace (prefixWord ++ tailWord_7878271) baseStart_7878271 baseEnd_7878271 := by
    simpa [prefixWord, tailWord_7878271, baseEnd_7878271] using wordTrace_append hprefix tailTrace_7878271
  have hstable : (prefixWord ++ tailWord_7878271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878271).length < 2 ^ (prefixWord ++ tailWord_7878271).sum := by decide
  have hdescent : baseEnd_7878271 < baseStart_7878271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878281 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 4, 4]
def baseStart_7878281 : Nat := 118140960795 + 7878281 * 2 ^ 59
def prefixEnd_7878281 : Nat := 4983230072969 + 3 ^ 40 * 7878281 * 2
def baseEnd_7878281 : Nat := 1348448294728065307685317

theorem tailTrace_7878281 : CollatzResearch.WordTrace tailWord_7878281 prefixEnd_7878281 1348448294728065307685317 := by
  unfold tailWord_7878281
  simp only [CollatzResearch.WordTrace]
  refine ⟨287344514371340915118922697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191563009580893943412615131 287344514371340915118922697)
  ·
    refine ⟨215508385778505686339192023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287344514371340915118922697 215508385778505686339192023)
    ·
      refine ⟨323262578667758529508788035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215508385778505686339192023 323262578667758529508788035)
      ·
        refine ⟨484893868001637794263182053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323262578667758529508788035 484893868001637794263182053)
        ·
          refine ⟨90917600250307086424346635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 484893868001637794263182053 90917600250307086424346635)
          ·
            refine ⟨136376400375460629636519953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90917600250307086424346635 136376400375460629636519953)
            ·
              refine ⟨102282300281595472227389965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136376400375460629636519953 102282300281595472227389965)
              ·
                refine ⟨38355862605598302085271237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102282300281595472227389965 38355862605598302085271237)
                ·
                  refine ⟨7191724238549681640988357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38355862605598302085271237 7191724238549681640988357)
                  ·
                    refine ⟨1348448294728065307685317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191724238549681640988357 1348448294728065307685317)
                    ·
                      rfl

theorem cell23_7878281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 4].length) (baseStart_7878281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878281 prefixEnd_7878281 := by exact prefixLift 7878281
  have htrace : WordTrace (prefixWord ++ tailWord_7878281) baseStart_7878281 baseEnd_7878281 := by
    simpa [prefixWord, tailWord_7878281, baseEnd_7878281] using wordTrace_append hprefix tailTrace_7878281
  have hstable : (prefixWord ++ tailWord_7878281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878281).length < 2 ^ (prefixWord ++ tailWord_7878281).sum := by decide
  have hdescent : baseEnd_7878281 < baseStart_7878281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878282 : List Nat := [3, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3]
def baseStart_7878282 : Nat := 118140960795 + 7878282 * 2 ^ 59
def prefixEnd_7878282 : Nat := 4983230072969 + 3 ^ 40 * 7878282 * 2
def baseEnd_7878282 : Nat := 4045345397664850419143447

theorem tailTrace_7878282 : CollatzResearch.WordTrace tailWord_7878282 prefixEnd_7878282 4045345397664850419143447 := by
  unfold tailWord_7878282
  simp only [CollatzResearch.WordTrace]
  refine ⟨71836137711084323072427275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191563033896224861526472733 71836137711084323072427275)
  ·
    refine ⟨107754206566626484608640913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71836137711084323072427275 107754206566626484608640913)
    ·
      refine ⟨80815654924969863456480685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107754206566626484608640913 80815654924969863456480685)
      ·
        refine ⟨30305870596863698796180257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80815654924969863456480685 30305870596863698796180257)
        ·
          refine ⟨22729402947647774097135193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30305870596863698796180257 22729402947647774097135193)
          ·
            refine ⟨17047052210735830572851395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22729402947647774097135193 17047052210735830572851395)
            ·
              refine ⟨25570578316103745859277093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17047052210735830572851395 25570578316103745859277093)
              ·
                refine ⟨4794483434269452348614455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25570578316103745859277093 4794483434269452348614455)
                ·
                  refine ⟨7191725151404178522921683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794483434269452348614455 7191725151404178522921683)
                  ·
                    refine ⟨10787587727106267784382525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7191725151404178522921683 10787587727106267784382525)
                    ·
                      refine ⟨4045345397664850419143447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10787587727106267784382525 4045345397664850419143447)
                      ·
                        rfl

theorem cell23_7878282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_7878282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878282 prefixEnd_7878282 := by exact prefixLift 7878282
  have htrace : WordTrace (prefixWord ++ tailWord_7878282) baseStart_7878282 baseEnd_7878282 := by
    simpa [prefixWord, tailWord_7878282, baseEnd_7878282] using wordTrace_append hprefix tailTrace_7878282
  have hstable : (prefixWord ++ tailWord_7878282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878282).length < 2 ^ (prefixWord ++ tailWord_7878282).sum := by decide
  have hdescent : baseEnd_7878282 < baseStart_7878282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878288 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 7, 2, 2]
def baseStart_7878288 : Nat := 118140960795 + 7878288 * 2 ^ 59
def prefixEnd_7878288 : Nat := 4983230072969 + 3 ^ 40 * 7878288 * 2
def baseEnd_7878288 : Nat := 4045348478548777395668419

theorem tailTrace_7878288 : CollatzResearch.WordTrace tailWord_7878288 prefixEnd_7878288 4045348478548777395668419 := by
  unfold tailWord_7878288
  simp only [CollatzResearch.WordTrace]
  refine ⟨143672384841157777657213759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191563179788210370209618345 143672384841157777657213759)
  ·
    refine ⟨215508577261736666485820639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143672384841157777657213759 215508577261736666485820639)
    ·
      refine ⟨323262865892604999728730959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215508577261736666485820639 323262865892604999728730959)
      ·
        refine ⟨484894298838907499593096439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323262865892604999728730959 484894298838907499593096439)
        ·
          refine ⟨727341448258361249389644659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484894298838907499593096439 727341448258361249389644659)
          ·
            refine ⟨1091012172387541874084466989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727341448258361249389644659 1091012172387541874084466989)
            ·
              refine ⟨409129564645328202781675121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091012172387541874084466989 409129564645328202781675121)
              ·
                refine ⟨306847173483996152086256341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409129564645328202781675121 306847173483996152086256341)
                ·
                  refine ⟨7191730628531159814521633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 306847173483996152086256341 7191730628531159814521633)
                  ·
                    refine ⟨5393797971398369860891225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7191730628531159814521633 5393797971398369860891225)
                    ·
                      refine ⟨4045348478548777395668419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393797971398369860891225 4045348478548777395668419)
                      ·
                        rfl

theorem cell23_7878288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 2, 2].length) (baseStart_7878288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878288 prefixEnd_7878288 := by exact prefixLift 7878288
  have htrace : WordTrace (prefixWord ++ tailWord_7878288) baseStart_7878288 baseEnd_7878288 := by
    simpa [prefixWord, tailWord_7878288, baseEnd_7878288] using wordTrace_append hprefix tailTrace_7878288
  have hstable : (prefixWord ++ tailWord_7878288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878288).length < 2 ^ (prefixWord ++ tailWord_7878288).sum := by decide
  have hdescent : baseEnd_7878288 < baseStart_7878288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878305 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_7878305 : Nat := 118140960795 + 7878305 * 2 ^ 59
def prefixEnd_7878305 : Nat := 4983230072969 + 3 ^ 40 * 7878305 * 2
def baseEnd_7878305 : Nat := 4045357207719903829155841

theorem tailTrace_7878305 : CollatzResearch.WordTrace tailWord_7878305 prefixEnd_7878305 4045357207719903829155841 := by
  unfold tailWord_7878305
  simp only [CollatzResearch.WordTrace]
  refine ⟨287345389723253967217796369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191563593148835978145197579 287345389723253967217796369)
  ·
    refine ⟨215509042292440475413347277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287345389723253967217796369 215509042292440475413347277)
    ·
      refine ⟨80815890859665178280005229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215509042292440475413347277 80815890859665178280005229)
      ·
        refine ⟨30305959072374441855001961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80815890859665178280005229 30305959072374441855001961)
        ·
          refine ⟨22729469304280831391251471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30305959072374441855001961 22729469304280831391251471)
          ·
            refine ⟨34094203956421247086877207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22729469304280831391251471 34094203956421247086877207)
            ·
              refine ⟨51141305934631870630315811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34094203956421247086877207 51141305934631870630315811)
              ·
                refine ⟨76711958901947805945473717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51141305934631870630315811 76711958901947805945473717)
                ·
                  refine ⟨7191746147057606807388161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76711958901947805945473717 7191746147057606807388161)
                  ·
                    refine ⟨5393809610293205105541121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7191746147057606807388161 5393809610293205105541121)
                    ·
                      refine ⟨4045357207719903829155841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393809610293205105541121 4045357207719903829155841)
                      ·
                        rfl

theorem cell23_7878305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_7878305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878305 prefixEnd_7878305 := by exact prefixLift 7878305
  have htrace : WordTrace (prefixWord ++ tailWord_7878305) baseStart_7878305 baseEnd_7878305 := by
    simpa [prefixWord, tailWord_7878305, baseEnd_7878305] using wordTrace_append hprefix tailTrace_7878305
  have hstable : (prefixWord ++ tailWord_7878305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878305).length < 2 ^ (prefixWord ++ tailWord_7878305).sum := by decide
  have hdescent : baseEnd_7878305 < baseStart_7878305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878308 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_7878308 : Nat := 118140960795 + 7878308 * 2 ^ 59
def prefixEnd_7878308 : Nat := 4983230072969 + 3 ^ 40 * 7878308 * 2
def baseEnd_7878308 : Nat := 4045358748161867317418327

theorem tailTrace_7878308 : CollatzResearch.WordTrace tailWord_7878308 prefixEnd_7878308 4045358748161867317418327 := by
  unfold tailWord_7878308
  simp only [CollatzResearch.WordTrace]
  refine ⟨143672749571121549365077789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191563666094828732486770385 143672749571121549365077789)
  ·
    refine ⟨53877281089170581011904171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143672749571121549365077789 53877281089170581011904171)
    ·
      refine ⟨80815921633755871517856257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53877281089170581011904171 80815921633755871517856257)
      ·
        refine ⟨60611941225316903638392193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80815921633755871517856257 60611941225316903638392193)
        ·
          refine ⟨45458955918987677728794145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60611941225316903638392193 45458955918987677728794145)
          ·
            refine ⟨34094216939240758296595609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45458955918987677728794145 34094216939240758296595609)
            ·
              refine ⟨25570662704430568722446707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34094216939240758296595609 25570662704430568722446707)
              ·
                refine ⟨38355994056645853083670061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25570662704430568722446707 38355994056645853083670061)
                ·
                  refine ⟨14383497771242194906376273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38355994056645853083670061 14383497771242194906376273)
                  ·
                    refine ⟨10787623328431646179782205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14383497771242194906376273 10787623328431646179782205)
                    ·
                      refine ⟨4045358748161867317418327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10787623328431646179782205 4045358748161867317418327)
                      ·
                        rfl

theorem cell23_7878308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_7878308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878308 prefixEnd_7878308 := by exact prefixLift 7878308
  have htrace : WordTrace (prefixWord ++ tailWord_7878308) baseStart_7878308 baseEnd_7878308 := by
    simpa [prefixWord, tailWord_7878308, baseEnd_7878308] using wordTrace_append hprefix tailTrace_7878308
  have hstable : (prefixWord ++ tailWord_7878308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878308).length < 2 ^ (prefixWord ++ tailWord_7878308).sum := by decide
  have hdescent : baseEnd_7878308 < baseStart_7878308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878322 : List Nat := [3, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2]
def baseStart_7878322 : Nat := 118140960795 + 7878322 * 2 ^ 59
def prefixEnd_7878322 : Nat := 4983230072969 + 3 ^ 40 * 7878322 * 2
def baseEnd_7878322 : Nat := 4045365936891030262643263

theorem tailTrace_7878322 : CollatzResearch.WordTrace tailWord_7878322 prefixEnd_7878322 4045365936891030262643263 := by
  unfold tailWord_7878322
  simp only [CollatzResearch.WordTrace]
  refine ⟨71836502441048094780291305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191564006509461586080776813 71836502441048094780291305)
  ·
    refine ⟨53877376830786071085218479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71836502441048094780291305 53877376830786071085218479)
    ·
      refine ⟨80816065246179106627827719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53877376830786071085218479 80816065246179106627827719)
      ·
        refine ⟨121224097869268659941741579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80816065246179106627827719 121224097869268659941741579)
        ·
          refine ⟨181836146803902989912612369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121224097869268659941741579 181836146803902989912612369)
          ·
            refine ⟨136377110102927242434459277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181836146803902989912612369 136377110102927242434459277)
            ·
              refine ⟨51141416288597715912922229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136377110102927242434459277 51141416288597715912922229)
              ·
                refine ⟨4794507777056035866836459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51141416288597715912922229 4794507777056035866836459)
                ·
                  refine ⟨7191761665584053800254689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794507777056035866836459 7191761665584053800254689)
                  ·
                    refine ⟨5393821249188040350191017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7191761665584053800254689 5393821249188040350191017)
                    ·
                      refine ⟨4045365936891030262643263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393821249188040350191017 4045365936891030262643263)
                      ·
                        rfl

theorem cell23_7878322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_7878322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878322 prefixEnd_7878322 := by exact prefixLift 7878322
  have htrace : WordTrace (prefixWord ++ tailWord_7878322) baseStart_7878322 baseEnd_7878322 := by
    simpa [prefixWord, tailWord_7878322, baseEnd_7878322] using wordTrace_append hprefix tailTrace_7878322
  have hstable : (prefixWord ++ tailWord_7878322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878322).length < 2 ^ (prefixWord ++ tailWord_7878322).sum := by decide
  have hdescent : baseEnd_7878322 < baseStart_7878322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878342 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7878342 : Nat := 118140960795 + 7878342 * 2 ^ 59
def prefixEnd_7878342 : Nat := 4983230072969 + 3 ^ 40 * 7878342 * 2
def baseEnd_7878342 : Nat := 4045376206504120184393171

theorem tailTrace_7878342 : CollatzResearch.WordTrace tailWord_7878342 prefixEnd_7878342 4045376206504120184393171 := by
  unfold tailWord_7878342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8979585600753747579277915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191564492816079948357928853 8979585600753747579277915)
  ·
    refine ⟨13469378401130621368916873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8979585600753747579277915 13469378401130621368916873)
    ·
      refine ⟨10102033800847966026687655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13469378401130621368916873 10102033800847966026687655)
      ·
        refine ⟨15153050701271949040031483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10102033800847966026687655 15153050701271949040031483)
        ·
          refine ⟨22729576051907923560047225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15153050701271949040031483 22729576051907923560047225)
          ·
            refine ⟨17047182038930942670035419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22729576051907923560047225 17047182038930942670035419)
            ·
              refine ⟨25570773058396414005053129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17047182038930942670035419 25570773058396414005053129)
              ·
                refine ⟨19178079793797310503789847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25570773058396414005053129 19178079793797310503789847)
                ·
                  refine ⟨28767119690695965755684771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19178079793797310503789847 28767119690695965755684771)
                  ·
                    refine ⟨43150679536043948633527157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28767119690695965755684771 43150679536043948633527157)
                    ·
                      refine ⟨4045376206504120184393171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43150679536043948633527157 4045376206504120184393171)
                      ·
                        rfl

theorem cell23_7878342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7878342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878342 prefixEnd_7878342 := by exact prefixLift 7878342
  have htrace : WordTrace (prefixWord ++ tailWord_7878342) baseStart_7878342 baseEnd_7878342 := by
    simpa [prefixWord, tailWord_7878342, baseEnd_7878342] using wordTrace_append hprefix tailTrace_7878342
  have hstable : (prefixWord ++ tailWord_7878342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878342).length < 2 ^ (prefixWord ++ tailWord_7878342).sum := by decide
  have hdescent : baseEnd_7878342 < baseStart_7878342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878349 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_7878349 : Nat := 118140960795 + 7878349 * 2 ^ 59
def prefixEnd_7878349 : Nat := 4983230072969 + 3 ^ 40 * 7878349 * 2
def baseEnd_7878349 : Nat := 1348459933622900552335213

theorem tailTrace_7878349 : CollatzResearch.WordTrace tailWord_7878349 prefixEnd_7878349 1348459933622900552335213 := by
  unfold tailWord_7878349
  simp only [CollatzResearch.WordTrace]
  refine ⟨287346994535094562732398101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191564663023396375154932067 287346994535094562732398101)
  ·
    refine ⟨13469390368832557628081161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287346994535094562732398101 13469390368832557628081161)
    ·
      refine ⟨10102042776624418221060871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13469390368832557628081161 10102042776624418221060871)
      ·
        refine ⟨15153064164936627331591307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10102042776624418221060871 15153064164936627331591307)
        ·
          refine ⟨22729596247404940997386961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15153064164936627331591307 22729596247404940997386961)
          ·
            refine ⟨17047197185553705748040221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22729596247404940997386961 17047197185553705748040221)
            ·
              refine ⟨6392698944582639655515083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17047197185553705748040221 6392698944582639655515083)
              ·
                refine ⟨9589048416873959483272625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6392698944582639655515083 9589048416873959483272625)
                ·
                  refine ⟨7191786312655469612454469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9589048416873959483272625 7191786312655469612454469)
                  ·
                    refine ⟨1348459933622900552335213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191786312655469612454469 1348459933622900552335213)
                    ·
                      rfl

theorem cell23_7878349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_7878349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878349 prefixEnd_7878349 := by exact prefixLift 7878349
  have htrace : WordTrace (prefixWord ++ tailWord_7878349) baseStart_7878349 baseEnd_7878349 := by
    simpa [prefixWord, tailWord_7878349, baseEnd_7878349] using wordTrace_append hprefix tailTrace_7878349
  have hstable : (prefixWord ++ tailWord_7878349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878349).length < 2 ^ (prefixWord ++ tailWord_7878349).sum := by decide
  have hdescent : baseEnd_7878349 < baseStart_7878349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878391 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_7878391 : Nat := 118140960795 + 7878391 * 2 ^ 59
def prefixEnd_7878391 : Nat := 4983230072969 + 3 ^ 40 * 7878391 * 2
def baseEnd_7878391 : Nat := 4045401367056190492680445

theorem tailTrace_7878391 : CollatzResearch.WordTrace tailWord_7878391 prefixEnd_7878391 4045401367056190492680445 := by
  unfold tailWord_7878391
  simp only [CollatzResearch.WordTrace]
  refine ⟨287348526400942403905427027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191565684267294935936951351 287348526400942403905427027)
  ·
    refine ⟨431022789601413605858140541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287348526400942403905427027 431022789601413605858140541)
    ·
      refine ⟨161633546100530102196802703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431022789601413605858140541 161633546100530102196802703)
      ·
        refine ⟨242450319150795153295204055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161633546100530102196802703 242450319150795153295204055)
        ·
          refine ⟨363675478726192729942806083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242450319150795153295204055 363675478726192729942806083)
          ·
            refine ⟨545513218089289094914209125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363675478726192729942806083 545513218089289094914209125)
            ·
              refine ⟨102283728391741705296414211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 545513218089289094914209125 102283728391741705296414211)
              ·
                refine ⟨153425592587612557944621317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102283728391741705296414211 153425592587612557944621317)
                ·
                  refine ⟨28767298610177354614616497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153425592587612557944621317 28767298610177354614616497)
                  ·
                    refine ⟨21575473957633015960962373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28767298610177354614616497 21575473957633015960962373)
                    ·
                      refine ⟨4045401367056190492680445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21575473957633015960962373 4045401367056190492680445)
                      ·
                        rfl

theorem cell23_7878391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_7878391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878391 prefixEnd_7878391 := by exact prefixLift 7878391
  have htrace : WordTrace (prefixWord ++ tailWord_7878391) baseStart_7878391 baseEnd_7878391 := by
    simpa [prefixWord, tailWord_7878391, baseEnd_7878391] using wordTrace_append hprefix tailTrace_7878391
  have hstable : (prefixWord ++ tailWord_7878391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878391).length < 2 ^ (prefixWord ++ tailWord_7878391).sum := by decide
  have hdescent : baseEnd_7878391 < baseStart_7878391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878446 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_7878446 : Nat := 118140960795 + 7878446 * 2 ^ 59
def prefixEnd_7878446 : Nat := 4983230072969 + 3 ^ 40 * 7878446 * 2
def baseEnd_7878446 : Nat := 4045429608492187777492693

theorem tailTrace_7878446 : CollatzResearch.WordTrace tailWord_7878446 prefixEnd_7878446 4045429608492187777492693 := by
  unfold tailWord_7878446
  simp only [CollatzResearch.WordTrace]
  refine ⟨35918816551967893537334899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191567021610495432199119461 35918816551967893537334899)
  ·
    refine ⟨53878224827951840306002349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35918816551967893537334899 53878224827951840306002349)
    ·
      refine ⟨20204334310481940114750881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53878224827951840306002349 20204334310481940114750881)
      ·
        refine ⟨15153250732861455086063161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20204334310481940114750881 15153250732861455086063161)
        ·
          refine ⟨11364938049646091314547371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15153250732861455086063161 11364938049646091314547371)
          ·
            refine ⟨17047407074469136971821057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11364938049646091314547371 17047407074469136971821057)
            ·
              refine ⟨12785555305851852728865793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17047407074469136971821057 12785555305851852728865793)
              ·
                refine ⟨9589166479388889546649345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12785555305851852728865793 9589166479388889546649345)
                ·
                  refine ⟨7191874859541667159987009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9589166479388889546649345 7191874859541667159987009)
                  ·
                    refine ⟨5393906144656250369990257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7191874859541667159987009 5393906144656250369990257)
                    ·
                      refine ⟨4045429608492187777492693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393906144656250369990257 4045429608492187777492693)
                      ·
                        rfl

theorem cell23_7878446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_7878446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878446 prefixEnd_7878446 := by exact prefixLift 7878446
  have htrace : WordTrace (prefixWord ++ tailWord_7878446) baseStart_7878446 baseEnd_7878446 := by
    simpa [prefixWord, tailWord_7878446, baseEnd_7878446] using wordTrace_append hprefix tailTrace_7878446
  have hstable : (prefixWord ++ tailWord_7878446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878446).length < 2 ^ (prefixWord ++ tailWord_7878446).sum := by decide
  have hdescent : baseEnd_7878446 < baseStart_7878446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878452 : List Nat := [2, 5, 1, 1, 2, 2, 1, 4, 5]
def baseStart_7878452 : Nat := 118140960795 + 7878452 * 2 ^ 59
def prefixEnd_7878452 : Nat := 4983230072969 + 3 ^ 40 * 7878452 * 2
def baseEnd_7878452 : Nat := 449492521041790528224185

theorem tailTrace_7878452 : CollatzResearch.WordTrace tailWord_7878452 prefixEnd_7878452 449492521041790528224185 := by
  unfold tailWord_7878452
  simp only [CollatzResearch.WordTrace]
  refine ⟨143675375626860705661698805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191567167502480940882265073 143675375626860705661698805)
  ·
    refine ⟨13469566465018191155784263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143675375626860705661698805 13469566465018191155784263)
    ·
      refine ⟨20204349697527286733676395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13469566465018191155784263 20204349697527286733676395)
      ·
        refine ⟨30306524546290930100514593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20204349697527286733676395 30306524546290930100514593)
        ·
          refine ⟨22729893409718197575385945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30306524546290930100514593 22729893409718197575385945)
          ·
            refine ⟨17047420057288648181539459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22729893409718197575385945 17047420057288648181539459)
            ·
              refine ⟨25571130085932972272309189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17047420057288648181539459 25571130085932972272309189)
              ·
                refine ⟨4794586891112432301057973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25571130085932972272309189 4794586891112432301057973)
                ·
                  refine ⟨449492521041790528224185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4794586891112432301057973 449492521041790528224185)
                  ·
                    rfl

theorem cell23_7878452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_7878452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878452 prefixEnd_7878452 := by exact prefixLift 7878452
  have htrace : WordTrace (prefixWord ++ tailWord_7878452) baseStart_7878452 baseEnd_7878452 := by
    simpa [prefixWord, tailWord_7878452, baseEnd_7878452] using wordTrace_append hprefix tailTrace_7878452
  have hstable : (prefixWord ++ tailWord_7878452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878452).length < 2 ^ (prefixWord ++ tailWord_7878452).sum := by decide
  have hdescent : baseEnd_7878452 < baseStart_7878452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878458 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_7878458 : Nat := 118140960795 + 7878458 * 2 ^ 59
def prefixEnd_7878458 : Nat := 4983230072969 + 3 ^ 40 * 7878458 * 2
def baseEnd_7878458 : Nat := 4045435770260041730542637

theorem tailTrace_7878458 : CollatzResearch.WordTrace tailWord_7878458 prefixEnd_7878458 4045435770260041730542637 := by
  unfold tailWord_7878458
  simp only [CollatzResearch.WordTrace]
  refine ⟨71837742522924918587029007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191567313394466449565410685 71837742522924918587029007)
  ·
    refine ⟨107756613784387377880543511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71837742522924918587029007 107756613784387377880543511)
    ·
      refine ⟨161634920676581066820815267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107756613784387377880543511 161634920676581066820815267)
      ·
        refine ⟨242452381014871600231222901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161634920676581066820815267 242452381014871600231222901)
        ·
          refine ⟨22729910720144212521677147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242452381014871600231222901 22729910720144212521677147)
          ·
            refine ⟨34094866080216318782515721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22729910720144212521677147 34094866080216318782515721)
            ·
              refine ⟨25571149560162239086886791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34094866080216318782515721 25571149560162239086886791)
              ·
                refine ⟨38356724340243358630330187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25571149560162239086886791 38356724340243358630330187)
                ·
                  refine ⟨57535086510365037945495281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38356724340243358630330187 57535086510365037945495281)
                  ·
                    refine ⟨43151314882773778459121461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57535086510365037945495281 43151314882773778459121461)
                    ·
                      refine ⟨4045435770260041730542637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43151314882773778459121461 4045435770260041730542637)
                      ·
                        rfl

theorem cell23_7878458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_7878458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878458 prefixEnd_7878458 := by exact prefixLift 7878458
  have htrace : WordTrace (prefixWord ++ tailWord_7878458) baseStart_7878458 baseEnd_7878458 := by
    simpa [prefixWord, tailWord_7878458, baseEnd_7878458] using wordTrace_append hprefix tailTrace_7878458
  have hstable : (prefixWord ++ tailWord_7878458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878458).length < 2 ^ (prefixWord ++ tailWord_7878458).sum := by decide
  have hdescent : baseEnd_7878458 < baseStart_7878458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878485 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_7878485 : Nat := 118140960795 + 7878485 * 2 ^ 59
def prefixEnd_7878485 : Nat := 4983230072969 + 3 ^ 40 * 7878485 * 2
def baseEnd_7878485 : Nat := 4045449634237713124905013

theorem tailTrace_7878485 : CollatzResearch.WordTrace tailWord_7878485 prefixEnd_7878485 4045449634237713124905013 := by
  unfold tailWord_7878485
  simp only [CollatzResearch.WordTrace]
  refine ⟨287351954862601857959348909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191567969908401238639565939 287351954862601857959348909)
  ·
    refine ⟨107756983073475696734755841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287351954862601857959348909 107756983073475696734755841)
    ·
      refine ⟨80817737305106772551066881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107756983073475696734755841 80817737305106772551066881)
      ·
        refine ⟨60613302978830079413300161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80817737305106772551066881 60613302978830079413300161)
        ·
          refine ⟨45459977234122559559975121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60613302978830079413300161 45459977234122559559975121)
          ·
            refine ⟨34094982925591919669981341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45459977234122559559975121 34094982925591919669981341)
            ·
              refine ⟨12785618597096969876243003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34094982925591919669981341 12785618597096969876243003)
              ·
                refine ⟨19178427895645454814364505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12785618597096969876243003 19178427895645454814364505)
                ·
                  refine ⟨14383820921734091110773379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19178427895645454814364505 14383820921734091110773379)
                  ·
                    refine ⟨21575731382601136666160069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14383820921734091110773379 21575731382601136666160069)
                    ·
                      refine ⟨4045449634237713124905013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21575731382601136666160069 4045449634237713124905013)
                      ·
                        rfl

theorem cell23_7878485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_7878485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878485 prefixEnd_7878485 := by exact prefixLift 7878485
  have htrace : WordTrace (prefixWord ++ tailWord_7878485) baseStart_7878485 baseEnd_7878485 := by
    simpa [prefixWord, tailWord_7878485, baseEnd_7878485] using wordTrace_append hprefix tailTrace_7878485
  have hstable : (prefixWord ++ tailWord_7878485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878485).length < 2 ^ (prefixWord ++ tailWord_7878485).sum := by decide
  have hdescent : baseEnd_7878485 < baseStart_7878485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878508 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 8]
def baseStart_7878508 : Nat := 118140960795 + 7878508 * 2 ^ 59
def prefixEnd_7878508 : Nat := 4983230072969 + 3 ^ 40 * 7878508 * 2
def baseEnd_7878508 : Nat := 449495716032529614990823

theorem tailTrace_7878508 : CollatzResearch.WordTrace tailWord_7878508 prefixEnd_7878508 449495716032529614990823 := by
  unfold tailWord_7878508
  simp only [CollatzResearch.WordTrace]
  refine ⟨143676396870759266443718089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191568529161012355258290785 143676396870759266443718089)
  ·
    refine ⟨107757297653069449832788567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143676396870759266443718089 107757297653069449832788567)
    ·
      refine ⟨161635946479604174749182851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107757297653069449832788567 161635946479604174749182851)
      ·
        refine ⟨242453919719406262123774277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161635946479604174749182851 242453919719406262123774277)
        ·
          refine ⟨45460109947388674148207677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242453919719406262123774277 45460109947388674148207677)
          ·
            refine ⟨17047541230270752805577879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45460109947388674148207677 17047541230270752805577879)
            ·
              refine ⟨25571311845406129208366819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17047541230270752805577879 25571311845406129208366819)
              ·
                refine ⟨38356967768109193812550229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25571311845406129208366819 38356967768109193812550229)
                ·
                  refine ⟨449495716032529614990823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38356967768109193812550229 449495716032529614990823)
                  ·
                    rfl

theorem cell23_7878508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_7878508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878508 prefixEnd_7878508 := by exact prefixLift 7878508
  have htrace : WordTrace (prefixWord ++ tailWord_7878508) baseStart_7878508 baseEnd_7878508 := by
    simpa [prefixWord, tailWord_7878508, baseEnd_7878508] using wordTrace_append hprefix tailTrace_7878508
  have hstable : (prefixWord ++ tailWord_7878508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878508).length < 2 ^ (prefixWord ++ tailWord_7878508).sum := by decide
  have hdescent : baseEnd_7878508 < baseStart_7878508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878545 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 1, 5, 2]
def baseStart_7878545 : Nat := 118140960795 + 7878545 * 2 ^ 59
def prefixEnd_7878545 : Nat := 4983230072969 + 3 ^ 40 * 7878545 * 2
def baseEnd_7878545 : Nat := 4045480443076982890154737

theorem tailTrace_7878545 : CollatzResearch.WordTrace tailWord_7878545 prefixEnd_7878545 4045480443076982890154737 := by
  unfold tailWord_7878545
  simp only [CollatzResearch.WordTrace]
  refine ⟨287354143242384488206533089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191569428828256325471022059 287354143242384488206533089)
  ·
    refine ⟨215515607431788366154899817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287354143242384488206533089 215515607431788366154899817)
    ·
      refine ⟨161636705573841274616174863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215515607431788366154899817 161636705573841274616174863)
      ·
        refine ⟨242455058360761911924262295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161636705573841274616174863 242455058360761911924262295)
        ·
          refine ⟨363682587541142867886393443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242455058360761911924262295 363682587541142867886393443)
          ·
            refine ⟨545523881311714301829590165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363682587541142867886393443 545523881311714301829590165)
            ·
              refine ⟨25571431936486607898262039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 545523881311714301829590165 25571431936486607898262039)
              ·
                refine ⟨38357147904729911847393059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25571431936486607898262039 38357147904729911847393059)
                ·
                  refine ⟨57535721857094867771089589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38357147904729911847393059 57535721857094867771089589)
                  ·
                    refine ⟨5393973924102643853539649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57535721857094867771089589 5393973924102643853539649)
                    ·
                      refine ⟨4045480443076982890154737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393973924102643853539649 4045480443076982890154737)
                      ·
                        rfl

theorem cell23_7878545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_7878545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878545 prefixEnd_7878545 := by exact prefixLift 7878545
  have htrace : WordTrace (prefixWord ++ tailWord_7878545) baseStart_7878545 baseEnd_7878545 := by
    simpa [prefixWord, tailWord_7878545, baseEnd_7878545] using wordTrace_append hprefix tailTrace_7878545
  have hstable : (prefixWord ++ tailWord_7878545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878545).length < 2 ^ (prefixWord ++ tailWord_7878545).sum := by decide
  have hdescent : baseEnd_7878545 < baseStart_7878545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878546 : List Nat := [3, 2, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_7878546 : Nat := 118140960795 + 7878546 * 2 ^ 59
def prefixEnd_7878546 : Nat := 4983230072969 + 3 ^ 40 * 7878546 * 2
def baseEnd_7878546 : Nat := 1348493652185879128747411

theorem tailTrace_7878546 : CollatzResearch.WordTrace tailWord_7878546 prefixEnd_7878546 1348493652185879128747411 := by
  unfold tailWord_7878546
  simp only [CollatzResearch.WordTrace]
  refine ⟨71838544928845216344329873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191569453143587243584879661 71838544928845216344329873)
  ·
    refine ⟨53878908696633912258247405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71838544928845216344329873 53878908696633912258247405)
    ·
      refine ⟨20204590761237717096842777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53878908696633912258247405 20204590761237717096842777)
      ·
        refine ⟨15153443070928287822632083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20204590761237717096842777 15153443070928287822632083)
        ·
          refine ⟨22730164606392431733948125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15153443070928287822632083 22730164606392431733948125)
          ·
            refine ⟨8523811727397161900230547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22730164606392431733948125 8523811727397161900230547)
            ·
              refine ⟨12785717591095742850345821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8523811727397161900230547 12785717591095742850345821)
              ·
                refine ⟨4794644096660903568879683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12785717591095742850345821 4794644096660903568879683)
                ·
                  refine ⟨7191966144991355353319525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794644096660903568879683 7191966144991355353319525)
                  ·
                    refine ⟨1348493652185879128747411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191966144991355353319525 1348493652185879128747411)
                    ·
                      rfl

theorem cell23_7878546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_7878546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878546 prefixEnd_7878546 := by exact prefixLift 7878546
  have htrace : WordTrace (prefixWord ++ tailWord_7878546) baseStart_7878546 baseEnd_7878546 := by
    simpa [prefixWord, tailWord_7878546, baseEnd_7878546] using wordTrace_append hprefix tailTrace_7878546
  have hstable : (prefixWord ++ tailWord_7878546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878546).length < 2 ^ (prefixWord ++ tailWord_7878546).sum := by decide
  have hdescent : baseEnd_7878546 < baseStart_7878546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878592 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 5, 2, 2]
def baseStart_7878592 : Nat := 118140960795 + 7878592 * 2 ^ 59
def prefixEnd_7878592 : Nat := 4983230072969 + 3 ^ 40 * 7878592 * 2
def baseEnd_7878592 : Nat := 4045504576667744206267021

theorem tailTrace_7878592 : CollatzResearch.WordTrace tailWord_7878592 prefixEnd_7878592 4045504576667744206267021 := by
  unfold tailWord_7878592
  simp only [CollatzResearch.WordTrace]
  refine ⟨143677928736607107616747015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191570571648809476822329353 143677928736607107616747015)
  ·
    refine ⟨215516893104910661425120523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143677928736607107616747015 215516893104910661425120523)
    ·
      refine ⟨323275339657365992137680785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215516893104910661425120523 323275339657365992137680785)
      ·
        refine ⟨242456504743024494103260589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323275339657365992137680785 242456504743024494103260589)
        ·
          refine ⟨90921189278634185288722721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242456504743024494103260589 90921189278634185288722721)
          ·
            refine ⟨68190891958975638966542041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90921189278634185288722721 68190891958975638966542041)
            ·
              refine ⟨51143168969231729224906531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68190891958975638966542041 51143168969231729224906531)
              ·
                refine ⟨76714753453847593837359797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51143168969231729224906531 76714753453847593837359797)
                ·
                  refine ⟨7192008136298211922252481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76714753453847593837359797 7192008136298211922252481)
                  ·
                    refine ⟨5394006102223658941689361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7192008136298211922252481 5394006102223658941689361)
                    ·
                      refine ⟨4045504576667744206267021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394006102223658941689361 4045504576667744206267021)
                      ·
                        rfl

theorem cell23_7878592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_7878592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878592 prefixEnd_7878592 := by exact prefixLift 7878592
  have htrace : WordTrace (prefixWord ++ tailWord_7878592) baseStart_7878592 baseEnd_7878592 := by
    simpa [prefixWord, tailWord_7878592, baseEnd_7878592] using wordTrace_append hprefix tailTrace_7878592
  have hstable : (prefixWord ++ tailWord_7878592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878592).length < 2 ^ (prefixWord ++ tailWord_7878592).sum := by decide
  have hdescent : baseEnd_7878592 < baseStart_7878592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878620 : List Nat := [2, 2, 6, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7878620 : Nat := 118140960795 + 7878620 * 2 ^ 59
def prefixEnd_7878620 : Nat := 4983230072969 + 3 ^ 40 * 7878620 * 2
def baseEnd_7878620 : Nat := 4045518954126070096716893

theorem tailTrace_7878620 : CollatzResearch.WordTrace tailWord_7878620 prefixEnd_7878620 4045518954126070096716893 := by
  unfold tailWord_7878620
  simp only [CollatzResearch.WordTrace]
  refine ⟨143678439358556388007756657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191571252478075184010342209 143678439358556388007756657)
  ·
    refine ⟨107758829518917291005817493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143678439358556388007756657 107758829518917291005817493)
    ·
      refine ⟨5051195133699248015897695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107758829518917291005817493 5051195133699248015897695)
      ·
        refine ⟨7576792700548872023846543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5051195133699248015897695 7576792700548872023846543)
        ·
          refine ⟨11365189050823308035769815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7576792700548872023846543 11365189050823308035769815)
          ·
            refine ⟨17047783576234962053654723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11365189050823308035769815 17047783576234962053654723)
            ·
              refine ⟨25571675364352443080482085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17047783576234962053654723 25571675364352443080482085)
              ·
                refine ⟨4794689130816083077590391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25571675364352443080482085 4794689130816083077590391)
                ·
                  refine ⟨7192033696224124616385587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794689130816083077590391 7192033696224124616385587)
                  ·
                    refine ⟨10788050544336186924578381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7192033696224124616385587 10788050544336186924578381)
                    ·
                      refine ⟨4045518954126070096716893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10788050544336186924578381 4045518954126070096716893)
                      ·
                        rfl

theorem cell23_7878620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7878620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878620 prefixEnd_7878620 := by exact prefixLift 7878620
  have htrace : WordTrace (prefixWord ++ tailWord_7878620) baseStart_7878620 baseEnd_7878620 := by
    simpa [prefixWord, tailWord_7878620, baseEnd_7878620] using wordTrace_append hprefix tailTrace_7878620
  have hstable : (prefixWord ++ tailWord_7878620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878620).length < 2 ^ (prefixWord ++ tailWord_7878620).sum := by decide
  have hdescent : baseEnd_7878620 < baseStart_7878620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878628 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_7878628 : Nat := 118140960795 + 7878628 * 2 ^ 59
def prefixEnd_7878628 : Nat := 4983230072969 + 3 ^ 40 * 7878628 * 2
def baseEnd_7878628 : Nat := 1348507687323768688472285

theorem tailTrace_7878628 : CollatzResearch.WordTrace tailWord_7878628 prefixEnd_7878628 1348507687323768688472285 := by
  unfold tailWord_7878628
  simp only [CollatzResearch.WordTrace]
  refine ⟨143678585250541896690902269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191571447000722528921203025 143678585250541896690902269)
  ·
    refine ⟨53879469468953211259088351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143678585250541896690902269 53879469468953211259088351)
    ·
      refine ⟨80819204203429816888632527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53879469468953211259088351 80819204203429816888632527)
      ·
        refine ⟨121228806305144725332948791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80819204203429816888632527 121228806305144725332948791)
        ·
          refine ⟨181843209457717087999423187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121228806305144725332948791 181843209457717087999423187)
          ·
            refine ⟨272764814186575631999134781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181843209457717087999423187 272764814186575631999134781)
            ·
              refine ⟨102286805319965861999675543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272764814186575631999134781 102286805319965861999675543)
              ·
                refine ⟨153430207979948792999513315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102286805319965861999675543 153430207979948792999513315)
                ·
                  refine ⟨230145311969923189499269973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153430207979948792999513315 230145311969923189499269973)
                  ·
                    refine ⟨1348507687323768688472285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 230145311969923189499269973 1348507687323768688472285)
                    ·
                      rfl

theorem cell23_7878628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_7878628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878628 prefixEnd_7878628 := by exact prefixLift 7878628
  have htrace : WordTrace (prefixWord ++ tailWord_7878628) baseStart_7878628 baseEnd_7878628 := by
    simpa [prefixWord, tailWord_7878628, baseEnd_7878628] using wordTrace_append hprefix tailTrace_7878628
  have hstable : (prefixWord ++ tailWord_7878628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878628).length < 2 ^ (prefixWord ++ tailWord_7878628).sum := by decide
  have hdescent : baseEnd_7878628 < baseStart_7878628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878652 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_7878652 : Nat := 118140960795 + 7878652 * 2 ^ 59
def prefixEnd_7878652 : Nat := 4983230072969 + 3 ^ 40 * 7878652 * 2
def baseEnd_7878652 : Nat := 4045535385507013971516745

theorem tailTrace_7878652 : CollatzResearch.WordTrace tailWord_7878652 prefixEnd_7878652 4045535385507013971516745 := by
  unfold tailWord_7878652
  simp only [CollatzResearch.WordTrace]
  refine ⟨143679022926498422740339105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191572030568664563653785473 143679022926498422740339105)
  ·
    refine ⟨107759267194873817055254329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143679022926498422740339105 107759267194873817055254329)
    ·
      refine ⟨80819450396155362791440747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107759267194873817055254329 80819450396155362791440747)
      ·
        refine ⟨121229175594233044187161121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80819450396155362791440747 121229175594233044187161121)
        ·
          refine ⟨90921881695674783140370841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121229175594233044187161121 90921881695674783140370841)
          ·
            refine ⟨68191411271756087355278131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90921881695674783140370841 68191411271756087355278131)
            ·
              refine ⟨102287116907634131032917197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68191411271756087355278131 102287116907634131032917197)
              ·
                refine ⟨38357668840362799137343949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102287116907634131032917197 38357668840362799137343949)
                ·
                  refine ⟨14384125815136049676503981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38357668840362799137343949 14384125815136049676503981)
                  ·
                    refine ⟨5394047180676018628688993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14384125815136049676503981 5394047180676018628688993)
                    ·
                      refine ⟨4045535385507013971516745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394047180676018628688993 4045535385507013971516745)
                      ·
                        rfl

theorem cell23_7878652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_7878652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878652 prefixEnd_7878652 := by exact prefixLift 7878652
  have htrace : WordTrace (prefixWord ++ tailWord_7878652) baseStart_7878652 baseEnd_7878652 := by
    simpa [prefixWord, tailWord_7878652, baseEnd_7878652] using wordTrace_append hprefix tailTrace_7878652
  have hstable : (prefixWord ++ tailWord_7878652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878652).length < 2 ^ (prefixWord ++ tailWord_7878652).sum := by decide
  have hdescent : baseEnd_7878652 < baseStart_7878652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878660 : List Nat := [2, 3, 2, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7878660 : Nat := 118140960795 + 7878660 * 2 ^ 59
def prefixEnd_7878660 : Nat := 4983230072969 + 3 ^ 40 * 7878660 * 2
def baseEnd_7878660 : Nat := 4045539493352249940216709

theorem tailTrace_7878660 : CollatzResearch.WordTrace tailWord_7878660 prefixEnd_7878660 4045539493352249940216709 := by
  unfold tailWord_7878660
  simp only [CollatzResearch.WordTrace]
  refine ⟨143679168818483931423484717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191572225091311908564646289 143679168818483931423484717)
  ·
    refine ⟨53879688306931474283806769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143679168818483931423484717 53879688306931474283806769)
    ·
      refine ⟨40409766230198605712855077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53879688306931474283806769 40409766230198605712855077)
      ·
        refine ⟨7576831168162238571160327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40409766230198605712855077 7576831168162238571160327)
        ·
          refine ⟨11365246752243357856740491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7576831168162238571160327 11365246752243357856740491)
          ·
            refine ⟨17047870128365036785110737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11365246752243357856740491 17047870128365036785110737)
            ·
              refine ⟨12785902596273777588833053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17047870128365036785110737 12785902596273777588833053)
              ·
                refine ⟨4794713473602666595812395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12785902596273777588833053 4794713473602666595812395)
                ·
                  refine ⟨7192070210403999893718593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794713473602666595812395 7192070210403999893718593)
                  ·
                    refine ⟨5394052657802999920288945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7192070210403999893718593 5394052657802999920288945)
                    ·
                      refine ⟨4045539493352249940216709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394052657802999920288945 4045539493352249940216709)
                      ·
                        rfl

theorem cell23_7878660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7878660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878660 prefixEnd_7878660 := by exact prefixLift 7878660
  have htrace : WordTrace (prefixWord ++ tailWord_7878660) baseStart_7878660 baseEnd_7878660 := by
    simpa [prefixWord, tailWord_7878660, baseEnd_7878660] using wordTrace_append hprefix tailTrace_7878660
  have hstable : (prefixWord ++ tailWord_7878660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878660).length < 2 ^ (prefixWord ++ tailWord_7878660).sum := by decide
  have hdescent : baseEnd_7878660 < baseStart_7878660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878705 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 7]
def baseStart_7878705 : Nat := 118140960795 + 7878705 * 2 ^ 59
def prefixEnd_7878705 : Nat := 4983230072969 + 3 ^ 40 * 7878705 * 2
def baseEnd_7878705 : Nat := 449506955553522473794889

theorem tailTrace_7878705 : CollatzResearch.WordTrace tailWord_7878705 prefixEnd_7878705 449506955553522473794889 := by
  unfold tailWord_7878705
  simp only [CollatzResearch.WordTrace]
  refine ⟨287359978921804835532357569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191573319281203223688238379 287359978921804835532357569)
  ·
    refine ⟨215519984191353626649268177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287359978921804835532357569 215519984191353626649268177)
    ·
      refine ⟨161639988143515219986951133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215519984191353626649268177 161639988143515219986951133)
      ·
        refine ⟨60614995553818207495106675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161639988143515219986951133 60614995553818207495106675)
        ·
          refine ⟨90922493330727311242660013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60614995553818207495106675 90922493330727311242660013)
          ·
            refine ⟨34095934999022741715997505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90922493330727311242660013 34095934999022741715997505)
            ·
              refine ⟨25571951249267056286998129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34095934999022741715997505 25571951249267056286998129)
              ·
                refine ⟨19178963436950292215248597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25571951249267056286998129 19178963436950292215248597)
                ·
                  refine ⟨449506955553522473794889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19178963436950292215248597 449506955553522473794889)
                  ·
                    rfl

theorem cell23_7878705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 7].length) (baseStart_7878705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878705 prefixEnd_7878705 := by exact prefixLift 7878705
  have htrace : WordTrace (prefixWord ++ tailWord_7878705) baseStart_7878705 baseEnd_7878705 := by
    simpa [prefixWord, tailWord_7878705, baseEnd_7878705] using wordTrace_append hprefix tailTrace_7878705
  have hstable : (prefixWord ++ tailWord_7878705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878705).length < 2 ^ (prefixWord ++ tailWord_7878705).sum := by decide
  have hdescent : baseEnd_7878705 < baseStart_7878705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878735 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 2, 5]
def baseStart_7878735 : Nat := 118140960795 + 7878735 * 2 ^ 59
def prefixEnd_7878735 : Nat := 4983230072969 + 3 ^ 40 * 7878735 * 2
def baseEnd_7878735 : Nat := 1348526001467112382259621

theorem tailTrace_7878735 : CollatzResearch.WordTrace tailWord_7878735 prefixEnd_7878735 1348526001467112382259621 := by
  unfold tailWord_7878735
  simp only [CollatzResearch.WordTrace]
  refine ⟨287361073111696150655949659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191574048741130767103966439 287361073111696150655949659)
  ·
    refine ⟨431041609667544225983924489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287361073111696150655949659 431041609667544225983924489)
    ·
      refine ⟨323281207250658169487943367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431041609667544225983924489 323281207250658169487943367)
      ·
        refine ⟨484921810875987254231915051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323281207250658169487943367 484921810875987254231915051)
        ·
          refine ⟨727382716313980881347872577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484921810875987254231915051 727382716313980881347872577)
          ·
            refine ⟨545537037235485661010904433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727382716313980881347872577 545537037235485661010904433)
            ·
              refine ⟨409152777926614245758178325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545537037235485661010904433 409152777926614245758178325)
              ·
                refine ⟨19179036465310042769914609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 409152777926614245758178325 19179036465310042769914609)
                ·
                  refine ⟨14384277348982532077435957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19179036465310042769914609 14384277348982532077435957)
                  ·
                    refine ⟨1348526001467112382259621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14384277348982532077435957 1348526001467112382259621)
                    ·
                      rfl

theorem cell23_7878735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_7878735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878735 prefixEnd_7878735 := by exact prefixLift 7878735
  have htrace : WordTrace (prefixWord ++ tailWord_7878735) baseStart_7878735 baseEnd_7878735 := by
    simpa [prefixWord, tailWord_7878735, baseEnd_7878735] using wordTrace_append hprefix tailTrace_7878735
  have hstable : (prefixWord ++ tailWord_7878735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878735).length < 2 ^ (prefixWord ++ tailWord_7878735).sum := by decide
  have hdescent : baseEnd_7878735 < baseStart_7878735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878745 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_7878745 : Nat := 118140960795 + 7878745 * 2 ^ 59
def prefixEnd_7878745 : Nat := 4983230072969 + 3 ^ 40 * 7878745 * 2
def baseEnd_7878745 : Nat := 4045583139207882107653817

theorem tailTrace_7878745 : CollatzResearch.WordTrace tailWord_7878745 prefixEnd_7878745 4045583139207882107653817 := by
  unfold tailWord_7878745
  simp only [CollatzResearch.WordTrace]
  refine ⟨287361437841659922363813689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191574291894439948242542459 287361437841659922363813689)
  ·
    refine ⟨215521078381244941772860267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287361437841659922363813689 215521078381244941772860267)
    ·
      refine ⟨323281617571867412659290401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215521078381244941772860267 323281617571867412659290401)
      ·
        refine ⟨242461213178900559494467801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323281617571867412659290401 242461213178900559494467801)
        ·
          refine ⟨181845909884175419620850851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242461213178900559494467801 181845909884175419620850851)
          ·
            refine ⟨272768864826263129431276277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181845909884175419620850851 272768864826263129431276277)
            ·
              refine ⟨25572081077462168384182151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272768864826263129431276277 25572081077462168384182151)
              ·
                refine ⟨38358121616193252576273227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25572081077462168384182151 38358121616193252576273227)
                ·
                  refine ⟨57537182424289878864409841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38358121616193252576273227 57537182424289878864409841)
                  ·
                    refine ⟨43152886818217409148307381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57537182424289878864409841 43152886818217409148307381)
                    ·
                      refine ⟨4045583139207882107653817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43152886818217409148307381 4045583139207882107653817)
                      ·
                        rfl

theorem cell23_7878745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_7878745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878745 prefixEnd_7878745 := by exact prefixLift 7878745
  have htrace : WordTrace (prefixWord ++ tailWord_7878745) baseStart_7878745 baseEnd_7878745 := by
    simpa [prefixWord, tailWord_7878745, baseEnd_7878745] using wordTrace_append hprefix tailTrace_7878745
  have hstable : (prefixWord ++ tailWord_7878745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878745).length < 2 ^ (prefixWord ++ tailWord_7878745).sum := by decide
  have hdescent : baseEnd_7878745 < baseStart_7878745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878755 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7878755 : Nat := 118140960795 + 7878755 * 2 ^ 59
def prefixEnd_7878755 : Nat := 4983230072969 + 3 ^ 40 * 7878755 * 2
def baseEnd_7878755 : Nat := 4045588274014427068528771

theorem tailTrace_7878755 : CollatzResearch.WordTrace tailWord_7878755 prefixEnd_7878755 4045588274014427068528771 := by
  unfold tailWord_7878755
  simp only [CollatzResearch.WordTrace]
  refine ⟨287361802571623694071677719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191574535047749129381118479 287361802571623694071677719)
  ·
    refine ⟨431042703857435541107516579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287361802571623694071677719 431042703857435541107516579)
    ·
      refine ⟨646564055786153311661274869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431042703857435541107516579 646564055786153311661274869)
      ·
        refine ⟨60615380229951872968244519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 646564055786153311661274869 60615380229951872968244519)
        ·
          refine ⟨90923070344927809452366779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60615380229951872968244519 90923070344927809452366779)
          ·
            refine ⟨136384605517391714178550169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90923070344927809452366779 136384605517391714178550169)
            ·
              refine ⟨102288454138043785633912627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136384605517391714178550169 102288454138043785633912627)
              ·
                refine ⟨153432681207065678450868941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102288454138043785633912627 153432681207065678450868941)
                ·
                  refine ⟨57537255452649629419075853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153432681207065678450868941 57537255452649629419075853)
                  ·
                    refine ⟨21576470794743611032153445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57537255452649629419075853 21576470794743611032153445)
                    ·
                      refine ⟨4045588274014427068528771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21576470794743611032153445 4045588274014427068528771)
                      ·
                        rfl

theorem cell23_7878755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7878755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878755 prefixEnd_7878755 := by exact prefixLift 7878755
  have htrace : WordTrace (prefixWord ++ tailWord_7878755) baseStart_7878755 baseEnd_7878755 := by
    simpa [prefixWord, tailWord_7878755, baseEnd_7878755] using wordTrace_append hprefix tailTrace_7878755
  have hstable : (prefixWord ++ tailWord_7878755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878755).length < 2 ^ (prefixWord ++ tailWord_7878755).sum := by decide
  have hdescent : baseEnd_7878755 < baseStart_7878755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878812 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 6]
def baseStart_7878812 : Nat := 118140960795 + 7878812 * 2 ^ 59
def prefixEnd_7878812 : Nat := 4983230072969 + 3 ^ 40 * 7878812 * 2
def baseEnd_7878812 : Nat := 449513060267970371724001

theorem tailTrace_7878812 : CollatzResearch.WordTrace tailWord_7878812 prefixEnd_7878812 449513060267970371724001 := by
  unfold tailWord_7878812
  simp only [CollatzResearch.WordTrace]
  refine ⟨143681940766208596403251345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191575921021611461871001793 143681940766208596403251345)
  ·
    refine ⟨107761455574656447302438509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143681940766208596403251345 107761455574656447302438509)
    ·
      refine ⟨40410545840496167738414441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107761455574656447302438509 40410545840496167738414441)
      ·
        refine ⟨30307909380372125803810831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40410545840496167738414441 30307909380372125803810831)
        ·
          refine ⟨45461864070558188705716247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30307909380372125803810831 45461864070558188705716247)
          ·
            refine ⟨68192796105837283058574371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45461864070558188705716247 68192796105837283058574371)
            ·
              refine ⟨102289194158755924587861557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68192796105837283058574371 102289194158755924587861557)
              ·
                refine ⟨9589611952383367930112021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102289194158755924587861557 9589611952383367930112021)
                ·
                  refine ⟨449513060267970371724001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9589611952383367930112021 449513060267970371724001)
                  ·
                    rfl

theorem cell23_7878812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_7878812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878812 prefixEnd_7878812 := by exact prefixLift 7878812
  have htrace : WordTrace (prefixWord ++ tailWord_7878812) baseStart_7878812 baseEnd_7878812 := by
    simpa [prefixWord, tailWord_7878812, baseEnd_7878812] using wordTrace_append hprefix tailTrace_7878812
  have hstable : (prefixWord ++ tailWord_7878812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878812).length < 2 ^ (prefixWord ++ tailWord_7878812).sum := by decide
  have hdescent : baseEnd_7878812 < baseStart_7878812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878823 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_7878823 : Nat := 118140960795 + 7878823 * 2 ^ 59
def prefixEnd_7878823 : Nat := 4983230072969 + 3 ^ 40 * 7878823 * 2
def baseEnd_7878823 : Nat := 4045623190698932802478459

theorem tailTrace_7878823 : CollatzResearch.WordTrace tailWord_7878823 prefixEnd_7878823 4045623190698932802478459 := by
  unfold tailWord_7878823
  simp only [CollatzResearch.WordTrace]
  refine ⟨287364282735377341685153123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191576188490251561123435415 287364282735377341685153123)
  ·
    refine ⟨431046424103066012527729685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287364282735377341685153123 431046424103066012527729685)
    ·
      refine ⟨20205301129831219337237329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 431046424103066012527729685 20205301129831219337237329)
      ·
        refine ⟨15153975847373414502927997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20205301129831219337237329 15153975847373414502927997)
        ·
          refine ⟨5682740942765030438597999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15153975847373414502927997 5682740942765030438597999)
          ·
            refine ⟨8524111414147545657896999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5682740942765030438597999 8524111414147545657896999)
            ·
              refine ⟨12786167121221318486845499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524111414147545657896999 12786167121221318486845499)
              ·
                refine ⟨19179250681831977730268249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12786167121221318486845499 19179250681831977730268249)
                ·
                  refine ⟨14384438011373983297701187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19179250681831977730268249 14384438011373983297701187)
                  ·
                    refine ⟨21576657017060974946551781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14384438011373983297701187 21576657017060974946551781)
                    ·
                      refine ⟨4045623190698932802478459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21576657017060974946551781 4045623190698932802478459)
                      ·
                        rfl

theorem cell23_7878823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_7878823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878823 prefixEnd_7878823 := by exact prefixLift 7878823
  have htrace : WordTrace (prefixWord ++ tailWord_7878823) baseStart_7878823 baseEnd_7878823 := by
    simpa [prefixWord, tailWord_7878823, baseEnd_7878823] using wordTrace_append hprefix tailTrace_7878823
  have hstable : (prefixWord ++ tailWord_7878823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878823).length < 2 ^ (prefixWord ++ tailWord_7878823).sum := by decide
  have hdescent : baseEnd_7878823 < baseStart_7878823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878826 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7878826 : Nat := 118140960795 + 7878826 * 2 ^ 59
def prefixEnd_7878826 : Nat := 4983230072969 + 3 ^ 40 * 7878826 * 2
def baseEnd_7878826 : Nat := 4045624731140896290740945

theorem tailTrace_7878826 : CollatzResearch.WordTrace tailWord_7878826 prefixEnd_7878826 4045624731140896290740945 := by
  unfold tailWord_7878826
  simp only [CollatzResearch.WordTrace]
  refine ⟨71841098038591618299378083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191576261436244315465008221 71841098038591618299378083)
  ·
    refine ⟨107761647057887427449067125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71841098038591618299378083 107761647057887427449067125)
    ·
      refine ⟨10102654411676946323350043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107761647057887427449067125 10102654411676946323350043)
      ·
        refine ⟨15153981617515419485025065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10102654411676946323350043 15153981617515419485025065)
        ·
          refine ⟨11365486213136564613768799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15153981617515419485025065 11365486213136564613768799)
          ·
            refine ⟨17048229319704846920653199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11365486213136564613768799 17048229319704846920653199)
            ·
              refine ⟨25572343979557270380979799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17048229319704846920653199 25572343979557270380979799)
              ·
                refine ⟨38358515969335905571469699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25572343979557270380979799 38358515969335905571469699)
                ·
                  refine ⟨57537773954003858357204549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38358515969335905571469699 57537773954003858357204549)
                  ·
                    refine ⟨10788332616375723441975853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57537773954003858357204549 10788332616375723441975853)
                    ·
                      refine ⟨4045624731140896290740945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10788332616375723441975853 4045624731140896290740945)
                      ·
                        rfl

theorem cell23_7878826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7878826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878826 prefixEnd_7878826 := by exact prefixLift 7878826
  have htrace : WordTrace (prefixWord ++ tailWord_7878826) baseStart_7878826 baseEnd_7878826 := by
    simpa [prefixWord, tailWord_7878826, baseEnd_7878826] using wordTrace_append hprefix tailTrace_7878826
  have hstable : (prefixWord ++ tailWord_7878826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878826).length < 2 ^ (prefixWord ++ tailWord_7878826).sum := by decide
  have hdescent : baseEnd_7878826 < baseStart_7878826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878833 : List Nat := [1, 2, 2, 5, 2, 1, 2, 3, 1, 4]
def baseStart_7878833 : Nat := 118140960795 + 7878833 * 2 ^ 59
def prefixEnd_7878833 : Nat := 4983230072969 + 3 ^ 40 * 7878833 * 2
def baseEnd_7878833 : Nat := 1348542775168492587784471

theorem tailTrace_7878833 : CollatzResearch.WordTrace tailWord_7878833 prefixEnd_7878833 1348542775168492587784471 := by
  unfold tailWord_7878833
  simp only [CollatzResearch.WordTrace]
  refine ⟨287364647465341113393017153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191576431643560742262011435 287364647465341113393017153)
  ·
    refine ⟨215523485599005835044762865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287364647465341113393017153 215523485599005835044762865)
    ·
      refine ⟨161642614199254376283572149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215523485599005835044762865 161642614199254376283572149)
      ·
        refine ⟨15153995081180097776584889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161642614199254376283572149 15153995081180097776584889)
        ·
          refine ⟨11365496310885073332438667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15153995081180097776584889 11365496310885073332438667)
          ·
            refine ⟨17048244466327609998658001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11365496310885073332438667 17048244466327609998658001)
            ·
              refine ⟨12786183349745707498993501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17048244466327609998658001 12786183349745707498993501)
              ·
                refine ⟨4794818756154640312122563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12786183349745707498993501 4794818756154640312122563)
                ·
                  refine ⟨7192228134231960468183845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794818756154640312122563 7192228134231960468183845)
                  ·
                    refine ⟨1348542775168492587784471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7192228134231960468183845 1348542775168492587784471)
                    ·
                      rfl

theorem cell23_7878833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_7878833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878833 prefixEnd_7878833 := by exact prefixLift 7878833
  have htrace : WordTrace (prefixWord ++ tailWord_7878833) baseStart_7878833 baseEnd_7878833 := by
    simpa [prefixWord, tailWord_7878833, baseEnd_7878833] using wordTrace_append hprefix tailTrace_7878833
  have hstable : (prefixWord ++ tailWord_7878833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878833).length < 2 ^ (prefixWord ++ tailWord_7878833).sum := by decide
  have hdescent : baseEnd_7878833 < baseStart_7878833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878835 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 5]
def baseStart_7878835 : Nat := 118140960795 + 7878835 * 2 ^ 59
def prefixEnd_7878835 : Nat := 4983230072969 + 3 ^ 40 * 7878835 * 2
def baseEnd_7878835 : Nat := 4045629352466786755528403

theorem tailTrace_7878835 : CollatzResearch.WordTrace tailWord_7878835 prefixEnd_7878835 4045629352466786755528403 := by
  unfold tailWord_7878835
  simp only [CollatzResearch.WordTrace]
  refine ⟨287364720411333867734589959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191576480274222578489726639 287364720411333867734589959)
  ·
    refine ⟨431047080617000801601884939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287364720411333867734589959 431047080617000801601884939)
    ·
      refine ⟨646570620925501202402827409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431047080617000801601884939 646570620925501202402827409)
      ·
        refine ⟨484927965694125901802120557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646570620925501202402827409 484927965694125901802120557)
        ·
          refine ⟨181847987135297213175795209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484927965694125901802120557 181847987135297213175795209)
          ·
            refine ⟨136385990351472909881846407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181847987135297213175795209 136385990351472909881846407)
            ·
              refine ⟨204578985527209364822769611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136385990351472909881846407 204578985527209364822769611)
              ·
                refine ⟨306868478290814047234154417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204578985527209364822769611 306868478290814047234154417)
                ·
                  refine ⟨230151358718110535425615813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306868478290814047234154417 230151358718110535425615813)
                  ·
                    refine ⟨43153379759645725392302965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230151358718110535425615813 43153379759645725392302965)
                    ·
                      refine ⟨4045629352466786755528403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43153379759645725392302965 4045629352466786755528403)
                      ·
                        rfl

theorem cell23_7878835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_7878835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878835 prefixEnd_7878835 := by exact prefixLift 7878835
  have htrace : WordTrace (prefixWord ++ tailWord_7878835) baseStart_7878835 baseEnd_7878835 := by
    simpa [prefixWord, tailWord_7878835, baseEnd_7878835] using wordTrace_append hprefix tailTrace_7878835
  have hstable : (prefixWord ++ tailWord_7878835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878835).length < 2 ^ (prefixWord ++ tailWord_7878835).sum := by decide
  have hdescent : baseEnd_7878835 < baseStart_7878835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878846 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_7878846 : Nat := 118140960795 + 7878846 * 2 ^ 59
def prefixEnd_7878846 : Nat := 4983230072969 + 3 ^ 40 * 7878846 * 2
def baseEnd_7878846 : Nat := 449515000083776245832317

theorem tailTrace_7878846 : CollatzResearch.WordTrace tailWord_7878846 prefixEnd_7878846 449515000083776245832317 := by
  unfold tailWord_7878846
  simp only [CollatzResearch.WordTrace]
  refine ⟨35920640201786752076655049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191576747742862677742160261 35920640201786752076655049)
  ·
    refine ⟨26940480151340064057491287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35920640201786752076655049 26940480151340064057491287)
    ·
      refine ⟨40410720227010096086236931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26940480151340064057491287 40410720227010096086236931)
      ·
        refine ⟨60616080340515144129355397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40410720227010096086236931 60616080340515144129355397)
        ·
          refine ⟨11365515063846589524254137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60616080340515144129355397 11365515063846589524254137)
          ·
            refine ⟨8524136297884942143190603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11365515063846589524254137 8524136297884942143190603)
            ·
              refine ⟨12786204446827413214785905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524136297884942143190603 12786204446827413214785905)
              ·
                refine ⟨9589653335120559911089429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12786204446827413214785905 9589653335120559911089429)
                ·
                  refine ⟨449515000083776245832317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9589653335120559911089429 449515000083776245832317)
                  ·
                    rfl

theorem cell23_7878846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_7878846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878846 prefixEnd_7878846 := by exact prefixLift 7878846
  have htrace : WordTrace (prefixWord ++ tailWord_7878846) baseStart_7878846 baseEnd_7878846 := by
    simpa [prefixWord, tailWord_7878846, baseEnd_7878846] using wordTrace_append hprefix tailTrace_7878846
  have hstable : (prefixWord ++ tailWord_7878846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878846).length < 2 ^ (prefixWord ++ tailWord_7878846).sum := by decide
  have hdescent : baseEnd_7878846 < baseStart_7878846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878850 : List Nat := [3, 5, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_7878850 : Nat := 118140960795 + 7878850 * 2 ^ 59
def prefixEnd_7878850 : Nat := 4983230072969 + 3 ^ 40 * 7878850 * 2
def baseEnd_7878850 : Nat := 1348545684892201398946945

theorem tailTrace_7878850 : CollatzResearch.WordTrace tailWord_7878850 prefixEnd_7878850 1348545684892201398946945 := by
  unfold tailWord_7878850
  simp only [CollatzResearch.WordTrace]
  refine ⟨71841316876569881324096501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191576845004186350197590669 71841316876569881324096501)
  ·
    refine ⟨6735123457178426374134047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71841316876569881324096501 6735123457178426374134047)
    ·
      refine ⟨10102685185767639561201071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6735123457178426374134047 10102685185767639561201071)
      ·
        refine ⟨15154027778651459341801607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10102685185767639561201071 15154027778651459341801607)
        ·
          refine ⟨22731041667977189012702411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15154027778651459341801607 22731041667977189012702411)
          ·
            refine ⟨34096562501965783519053617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22731041667977189012702411 34096562501965783519053617)
            ·
              refine ⟨25572421876474337639290213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34096562501965783519053617 25572421876474337639290213)
              ·
                refine ⟨4794829101838938307366915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25572421876474337639290213 4794829101838938307366915)
                ·
                  refine ⟨7192243652758407461050373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794829101838938307366915 7192243652758407461050373)
                  ·
                    refine ⟨1348545684892201398946945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7192243652758407461050373 1348545684892201398946945)
                    ·
                      rfl

theorem cell23_7878850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_7878850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878850 prefixEnd_7878850 := by exact prefixLift 7878850
  have htrace : WordTrace (prefixWord ++ tailWord_7878850) baseStart_7878850 baseEnd_7878850 := by
    simpa [prefixWord, tailWord_7878850, baseEnd_7878850] using wordTrace_append hprefix tailTrace_7878850
  have hstable : (prefixWord ++ tailWord_7878850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878850).length < 2 ^ (prefixWord ++ tailWord_7878850).sum := by decide
  have hdescent : baseEnd_7878850 < baseStart_7878850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878855 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 2, 10]
def baseStart_7878855 : Nat := 118140960795 + 7878855 * 2 ^ 59
def prefixEnd_7878855 : Nat := 4983230072969 + 3 ^ 40 * 7878855 * 2
def baseEnd_7878855 : Nat := 1348546540693292225759437

theorem tailTrace_7878855 : CollatzResearch.WordTrace tailWord_7878855 prefixEnd_7878855 1348546540693292225759437 := by
  unfold tailWord_7878855
  simp only [CollatzResearch.WordTrace]
  refine ⟨287365449871261411150318019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191576966580840940766878679 287365449871261411150318019)
  ·
    refine ⟨431048174806892116725477029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287365449871261411150318019 431048174806892116725477029)
    ·
      refine ⟨80821532776292271886026943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431048174806892116725477029 80821532776292271886026943)
      ·
        refine ⟨121232299164438407829040415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80821532776292271886026943 121232299164438407829040415)
        ·
          refine ⟨181848448746657611743560623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121232299164438407829040415 181848448746657611743560623)
          ·
            refine ⟨272772673119986417615340935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181848448746657611743560623 272772673119986417615340935)
            ·
              refine ⟨409159009679979626423011403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272772673119986417615340935 409159009679979626423011403)
              ·
                refine ⟨613738514519969439634517105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409159009679979626423011403 613738514519969439634517105)
                ·
                  refine ⟨460303885889977079725887829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613738514519969439634517105 460303885889977079725887829)
                  ·
                    refine ⟨1348546540693292225759437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 460303885889977079725887829 1348546540693292225759437)
                    ·
                      rfl

theorem cell23_7878855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_7878855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878855 prefixEnd_7878855 := by exact prefixLift 7878855
  have htrace : WordTrace (prefixWord ++ tailWord_7878855) baseStart_7878855 baseEnd_7878855 := by
    simpa [prefixWord, tailWord_7878855, baseEnd_7878855] using wordTrace_append hprefix tailTrace_7878855
  have hstable : (prefixWord ++ tailWord_7878855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878855).length < 2 ^ (prefixWord ++ tailWord_7878855).sum := by decide
  have hdescent : baseEnd_7878855 < baseStart_7878855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878892 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_7878892 : Nat := 118140960795 + 7878892 * 2 ^ 59
def prefixEnd_7878892 : Nat := 4983230072969 + 3 ^ 40 * 7878892 * 2
def baseEnd_7878892 : Nat := 4045658620864093032515641

theorem tailTrace_7878892 : CollatzResearch.WordTrace tailWord_7878892 prefixEnd_7878892 4045658620864093032515641 := by
  unfold tailWord_7878892
  simp only [CollatzResearch.WordTrace]
  refine ⟨143683399686063683234707465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191577866248084910979609953 143683399686063683234707465)
  ·
    refine ⟨107762549764547762426030599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143683399686063683234707465 107762549764547762426030599)
    ·
      refine ⟨161643824646821643639045899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107762549764547762426030599 161643824646821643639045899)
      ·
        refine ⟨242465736970232465458568849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161643824646821643639045899 242465736970232465458568849)
        ·
          refine ⟨181849302727674349093926637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242465736970232465458568849 181849302727674349093926637)
          ·
            refine ⟨68193488522877880910222489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181849302727674349093926637 68193488522877880910222489)
            ·
              refine ⟨51145116392158410682666867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68193488522877880910222489 51145116392158410682666867)
              ·
                refine ⟨76717674588237616024000301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51145116392158410682666867 76717674588237616024000301)
                ·
                  refine ⟨28769127970589106009000113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76717674588237616024000301 28769127970589106009000113)
                  ·
                    refine ⟨21576845977941829506750085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28769127970589106009000113 21576845977941829506750085)
                    ·
                      refine ⟨4045658620864093032515641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21576845977941829506750085 4045658620864093032515641)
                      ·
                        rfl

theorem cell23_7878892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_7878892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878892 prefixEnd_7878892 := by exact prefixLift 7878892
  have htrace : WordTrace (prefixWord ++ tailWord_7878892) baseStart_7878892 baseEnd_7878892 := by
    simpa [prefixWord, tailWord_7878892, baseEnd_7878892] using wordTrace_append hprefix tailTrace_7878892
  have hstable : (prefixWord ++ tailWord_7878892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878892).length < 2 ^ (prefixWord ++ tailWord_7878892).sum := by decide
  have hdescent : baseEnd_7878892 < baseStart_7878892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878899 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 3]
def baseStart_7878899 : Nat := 118140960795 + 7878899 * 2 ^ 59
def prefixEnd_7878899 : Nat := 4983230072969 + 3 ^ 40 * 7878899 * 2
def baseEnd_7878899 : Nat := 4045662215228674505128109

theorem tailTrace_7878899 : CollatzResearch.WordTrace tailWord_7878899 prefixEnd_7878899 4045662215228674505128109 := by
  unfold tailWord_7878899
  simp only [CollatzResearch.WordTrace]
  refine ⟨287367054683102006664919751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191578036455401337776613167 287367054683102006664919751)
  ·
    refine ⟨431050582024653009997379627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287367054683102006664919751 431050582024653009997379627)
    ·
      refine ⟨646575873036979514996069441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431050582024653009997379627 646575873036979514996069441)
      ·
        refine ⟨484931904777734636247052081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646575873036979514996069441 484931904777734636247052081)
        ·
          refine ⟨363698928583300977185289061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484931904777734636247052081 363698928583300977185289061)
          ·
            refine ⟨68193549109368933222241699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363698928583300977185289061 68193549109368933222241699)
            ·
              refine ⟨102290323664053399833362549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68193549109368933222241699 102290323664053399833362549)
              ·
                refine ⟨9589717843505006234377739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102290323664053399833362549 9589717843505006234377739)
                ·
                  refine ⟨14384576765257509351566609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9589717843505006234377739 14384576765257509351566609)
                  ·
                    refine ⟨10788432573943132013674957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14384576765257509351566609 10788432573943132013674957)
                    ·
                      refine ⟨4045662215228674505128109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10788432573943132013674957 4045662215228674505128109)
                      ·
                        rfl

theorem cell23_7878899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 3].length) (baseStart_7878899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878899 prefixEnd_7878899 := by exact prefixLift 7878899
  have htrace : WordTrace (prefixWord ++ tailWord_7878899) baseStart_7878899 baseEnd_7878899 := by
    simpa [prefixWord, tailWord_7878899, baseEnd_7878899] using wordTrace_append hprefix tailTrace_7878899
  have hstable : (prefixWord ++ tailWord_7878899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878899).length < 2 ^ (prefixWord ++ tailWord_7878899).sum := by decide
  have hdescent : baseEnd_7878899 < baseStart_7878899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878902 : List Nat := [5, 1, 1, 1, 1, 1, 13]
def baseStart_7878902 : Nat := 118140960795 + 7878902 * 2 ^ 59
def prefixEnd_7878902 : Nat := 4983230072969 + 3 ^ 40 * 7878902 * 2
def baseEnd_7878902 : Nat := 49946466119390592510995

theorem tailTrace_7878902 : CollatzResearch.WordTrace tailWord_7878902 prefixEnd_7878902 49946466119390592510995 := by
  unfold tailWord_7878902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17960447756380696136079935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191578109401394092118185973 17960447756380696136079935)
  ·
    refine ⟨26940671634571044204119903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17960447756380696136079935 26940671634571044204119903)
    ·
      refine ⟨40411007451856566306179855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26940671634571044204119903 40411007451856566306179855)
      ·
        refine ⟨60616511177784849459269783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40411007451856566306179855 60616511177784849459269783)
        ·
          refine ⟨90924766766677274188904675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60616511177784849459269783 90924766766677274188904675)
          ·
            refine ⟨136387150150015911283357013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90924766766677274188904675 136387150150015911283357013)
            ·
              refine ⟨49946466119390592510995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 136387150150015911283357013 49946466119390592510995)
              ·
                rfl

theorem cell23_7878902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 13].length) (baseStart_7878902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878902 prefixEnd_7878902 := by exact prefixLift 7878902
  have htrace : WordTrace (prefixWord ++ tailWord_7878902) baseStart_7878902 baseEnd_7878902 := by
    simpa [prefixWord, tailWord_7878902, baseEnd_7878902] using wordTrace_append hprefix tailTrace_7878902
  have hstable : (prefixWord ++ tailWord_7878902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878902).length < 2 ^ (prefixWord ++ tailWord_7878902).sum := by decide
  have hdescent : baseEnd_7878902 < baseStart_7878902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878946 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_7878946 : Nat := 118140960795 + 7878946 * 2 ^ 59
def prefixEnd_7878946 : Nat := 4983230072969 + 3 ^ 40 * 7878946 * 2
def baseEnd_7878946 : Nat := 4045686348819435821240393

theorem tailTrace_7878946 : CollatzResearch.WordTrace tailWord_7878946 prefixEnd_7878946 4045686348819435821240393 := by
  unfold tailWord_7878946
  simp only [CollatzResearch.WordTrace]
  refine ⟨71842192228482933422970173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191579179275954489127920461 71842192228482933422970173)
  ·
    refine ⟨26940822085681100033613815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71842192228482933422970173 26940822085681100033613815)
    ·
      refine ⟨40411233128521650050420723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26940822085681100033613815 40411233128521650050420723)
      ·
        refine ⟨60616849692782475075631085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40411233128521650050420723 60616849692782475075631085)
        ·
          refine ⟨22731318634793428153361657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60616849692782475075631085 22731318634793428153361657)
          ·
            refine ⟨17048488976095071115021243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22731318634793428153361657 17048488976095071115021243)
            ·
              refine ⟨25572733464142606672531865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17048488976095071115021243 25572733464142606672531865)
              ·
                refine ⟨19179550098106955004398899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25572733464142606672531865 19179550098106955004398899)
                ·
                  refine ⟨28769325147160432506598349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19179550098106955004398899 28769325147160432506598349)
                  ·
                    refine ⟨10788496930185162189974381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28769325147160432506598349 10788496930185162189974381)
                    ·
                      refine ⟨4045686348819435821240393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10788496930185162189974381 4045686348819435821240393)
                      ·
                        rfl

theorem cell23_7878946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_7878946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878946 prefixEnd_7878946 := by exact prefixLift 7878946
  have htrace : WordTrace (prefixWord ++ tailWord_7878946) baseStart_7878946 baseEnd_7878946 := by
    simpa [prefixWord, tailWord_7878946, baseEnd_7878946] using wordTrace_append hprefix tailTrace_7878946
  have hstable : (prefixWord ++ tailWord_7878946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878946).length < 2 ^ (prefixWord ++ tailWord_7878946).sum := by decide
  have hdescent : baseEnd_7878946 < baseStart_7878946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878956 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 1, 3, 2]
def baseStart_7878956 : Nat := 118140960795 + 7878956 * 2 ^ 59
def prefixEnd_7878956 : Nat := 4983230072969 + 3 ^ 40 * 7878956 * 2
def baseEnd_7878956 : Nat := 4045691483625980782115347

theorem tailTrace_7878956 : CollatzResearch.WordTrace tailWord_7878956 prefixEnd_7878956 4045691483625980782115347 := by
  unfold tailWord_7878956
  simp only [CollatzResearch.WordTrace]
  refine ⟨143684566821947752699872361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191579422429263670266496481 143684566821947752699872361)
  ·
    refine ⟨107763425116460814524904271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143684566821947752699872361 107763425116460814524904271)
    ·
      refine ⟨161645137674691221787356407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107763425116460814524904271 161645137674691221787356407)
      ·
        refine ⟨242467706512036832681034611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161645137674691221787356407 242467706512036832681034611)
        ·
          refine ⟨363701559768055249021551917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242467706512036832681034611 363701559768055249021551917)
          ·
            refine ⟨136388084913020718383081969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363701559768055249021551917 136388084913020718383081969)
            ·
              refine ⟨102291063684765538787311477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136388084913020718383081969 102291063684765538787311477)
              ·
                refine ⟨9589787220446769261310451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102291063684765538787311477 9589787220446769261310451)
                ·
                  refine ⟨14384680830670153891965677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9589787220446769261310451 14384680830670153891965677)
                  ·
                    refine ⟨5394255311501307709487129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14384680830670153891965677 5394255311501307709487129)
                    ·
                      refine ⟨4045691483625980782115347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394255311501307709487129 4045691483625980782115347)
                      ·
                        rfl

theorem cell23_7878956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_7878956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878956 prefixEnd_7878956 := by exact prefixLift 7878956
  have htrace : WordTrace (prefixWord ++ tailWord_7878956) baseStart_7878956 baseEnd_7878956 := by
    simpa [prefixWord, tailWord_7878956, baseEnd_7878956] using wordTrace_append hprefix tailTrace_7878956
  have hstable : (prefixWord ++ tailWord_7878956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878956).length < 2 ^ (prefixWord ++ tailWord_7878956).sum := by decide
  have hdescent : baseEnd_7878956 < baseStart_7878956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878964 : List Nat := [2, 5, 1, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_7878964 : Nat := 118140960795 + 7878964 * 2 ^ 59
def prefixEnd_7878964 : Nat := 4983230072969 + 3 ^ 40 * 7878964 * 2
def baseEnd_7878964 : Nat := 4045695591471216750815311

theorem tailTrace_7878964 : CollatzResearch.WordTrace tailWord_7878964 prefixEnd_7878964 4045695591471216750815311 := by
  unfold tailWord_7878964
  simp only [CollatzResearch.WordTrace]
  refine ⟨143684712713933261383017973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191579616951911015177357297 143684712713933261383017973)
  ·
    refine ⟨13470441816931243254657935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143684712713933261383017973 13470441816931243254657935)
    ·
      refine ⟨20205662725396864881986903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13470441816931243254657935 20205662725396864881986903)
      ·
        refine ⟨30308494088095297322980355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20205662725396864881986903 30308494088095297322980355)
        ·
          refine ⟨45462741132142945984470533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30308494088095297322980355 45462741132142945984470533)
          ·
            refine ⟨8524263962276802372088225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45462741132142945984470533 8524263962276802372088225)
            ·
              refine ⟨6393197971707601779066169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8524263962276802372088225 6393197971707601779066169)
              ·
                refine ⟨4794898478780701334299627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6393197971707601779066169 4794898478780701334299627)
                ·
                  refine ⟨7192347718171052001449441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794898478780701334299627 7192347718171052001449441)
                  ·
                    refine ⟨5394260788628289001087081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7192347718171052001449441 5394260788628289001087081)
                    ·
                      refine ⟨4045695591471216750815311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394260788628289001087081 4045695591471216750815311)
                      ·
                        rfl

theorem cell23_7878964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_7878964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878964 prefixEnd_7878964 := by exact prefixLift 7878964
  have htrace : WordTrace (prefixWord ++ tailWord_7878964) baseStart_7878964 baseEnd_7878964 := by
    simpa [prefixWord, tailWord_7878964, baseEnd_7878964] using wordTrace_append hprefix tailTrace_7878964
  have hstable : (prefixWord ++ tailWord_7878964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878964).length < 2 ^ (prefixWord ++ tailWord_7878964).sum := by decide
  have hdescent : baseEnd_7878964 < baseStart_7878964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878969 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7878969 : Nat := 118140960795 + 7878969 * 2 ^ 59
def prefixEnd_7878969 : Nat := 4983230072969 + 3 ^ 40 * 7878969 * 2
def baseEnd_7878969 : Nat := 4045698158874489231252787

theorem tailTrace_7878969 : CollatzResearch.WordTrace tailWord_7878969 prefixEnd_7878969 4045698158874489231252787 := by
  unfold tailWord_7878969
  simp only [CollatzResearch.WordTrace]
  refine ⟨287369607792848408619967961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191579738528565605746645307 287369607792848408619967961)
  ·
    refine ⟨215527205844636306464975971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287369607792848408619967961 215527205844636306464975971)
    ·
      refine ⟨323290808766954459697463957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215527205844636306464975971 323290808766954459697463957)
      ·
        refine ⟨15154256660950990298318623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 323290808766954459697463957 15154256660950990298318623)
        ·
          refine ⟨22731384991426485447477935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15154256660950990298318623 22731384991426485447477935)
          ·
            refine ⟨34097077487139728171216903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22731384991426485447477935 34097077487139728171216903)
            ·
              refine ⟨51145616230709592256825355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34097077487139728171216903 51145616230709592256825355)
              ·
                refine ⟨76718424346064388385238033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51145616230709592256825355 76718424346064388385238033)
                ·
                  refine ⟨57538818259548291288928525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76718424346064388385238033 57538818259548291288928525)
                  ·
                    refine ⟨21577056847330609233348197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57538818259548291288928525 21577056847330609233348197)
                    ·
                      refine ⟨4045698158874489231252787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21577056847330609233348197 4045698158874489231252787)
                      ·
                        rfl

theorem cell23_7878969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7878969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878969 prefixEnd_7878969 := by exact prefixLift 7878969
  have htrace : WordTrace (prefixWord ++ tailWord_7878969) baseStart_7878969 baseEnd_7878969 := by
    simpa [prefixWord, tailWord_7878969, baseEnd_7878969] using wordTrace_append hprefix tailTrace_7878969
  have hstable : (prefixWord ++ tailWord_7878969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878969).length < 2 ^ (prefixWord ++ tailWord_7878969).sum := by decide
  have hdescent : baseEnd_7878969 < baseStart_7878969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878986 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_7878986 : Nat := 118140960795 + 7878986 * 2 ^ 59
def prefixEnd_7878986 : Nat := 4983230072969 + 3 ^ 40 * 7878986 * 2
def baseEnd_7878986 : Nat := 4045706888045615664740209

theorem tailTrace_7878986 : CollatzResearch.WordTrace tailWord_7878986 prefixEnd_7878986 4045706888045615664740209 := by
  unfold tailWord_7878986
  simp only [CollatzResearch.WordTrace]
  refine ⟨71842556958446705130834203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191580151889191213682224541 71842556958446705130834203)
  ·
    refine ⟨107763835437670057696251305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71842556958446705130834203 107763835437670057696251305)
    ·
      refine ⟨80822876578252543272188479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107763835437670057696251305 80822876578252543272188479)
      ·
        refine ⟨121234314867378814908282719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80822876578252543272188479 121234314867378814908282719)
        ·
          refine ⟨181851472301068222362424079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121234314867378814908282719 181851472301068222362424079)
          ·
            refine ⟨272777208451602333543636119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181851472301068222362424079 272777208451602333543636119)
            ·
              refine ⟨409165812677403500315454179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272777208451602333543636119 409165812677403500315454179)
              ·
                refine ⟨613748719016105250473181269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409165812677403500315454179 613748719016105250473181269)
                ·
                  refine ⟨7192367800969983403982593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 613748719016105250473181269 7192367800969983403982593)
                  ·
                    refine ⟨5394275850727487552986945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7192367800969983403982593 5394275850727487552986945)
                    ·
                      refine ⟨4045706888045615664740209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394275850727487552986945 4045706888045615664740209)
                      ·
                        rfl

theorem cell23_7878986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_7878986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878986 prefixEnd_7878986 := by exact prefixLift 7878986
  have htrace : WordTrace (prefixWord ++ tailWord_7878986) baseStart_7878986 baseEnd_7878986 := by
    simpa [prefixWord, tailWord_7878986, baseEnd_7878986] using wordTrace_append hprefix tailTrace_7878986
  have hstable : (prefixWord ++ tailWord_7878986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878986).length < 2 ^ (prefixWord ++ tailWord_7878986).sum := by decide
  have hdescent : baseEnd_7878986 < baseStart_7878986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7878992 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 9]
def baseStart_7878992 : Nat := 118140960795 + 7878992 * 2 ^ 59
def prefixEnd_7878992 : Nat := 4983230072969 + 3 ^ 40 * 7878992 * 2
def baseEnd_7878992 : Nat := 449523329881060293473909

theorem tailTrace_7878992 : CollatzResearch.WordTrace tailWord_7878992 prefixEnd_7878992 449523329881060293473909 := by
  unfold tailWord_7878992
  simp only [CollatzResearch.WordTrace]
  refine ⟨143685223335882541774027615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191580297781176722365370153 143685223335882541774027615)
  ·
    refine ⟨215527835003823812661041423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143685223335882541774027615 215527835003823812661041423)
    ·
      refine ⟨323291752505735718991562135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215527835003823812661041423 323291752505735718991562135)
      ·
        refine ⟨484937628758603578487343203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323291752505735718991562135 484937628758603578487343203)
        ·
          refine ⟨727406443137905367731014805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484937628758603578487343203 727406443137905367731014805)
          ·
            refine ⟨34097177022089314112391319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 727406443137905367731014805 34097177022089314112391319)
            ·
              refine ⟨51145765533133971168586979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34097177022089314112391319 51145765533133971168586979)
              ·
                refine ⟨76718648299700956752880469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51145765533133971168586979 76718648299700956752880469)
                ·
                  refine ⟨449523329881060293473909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76718648299700956752880469 449523329881060293473909)
                  ·
                    rfl

theorem cell23_7878992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 9].length) (baseStart_7878992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7878992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7878992 prefixEnd_7878992 := by exact prefixLift 7878992
  have htrace : WordTrace (prefixWord ++ tailWord_7878992) baseStart_7878992 baseEnd_7878992 := by
    simpa [prefixWord, tailWord_7878992, baseEnd_7878992] using wordTrace_append hprefix tailTrace_7878992
  have hstable : (prefixWord ++ tailWord_7878992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7878992).length < 2 ^ (prefixWord ++ tailWord_7878992).sum := by decide
  have hdescent : baseEnd_7878992 < baseStart_7878992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7878992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879002 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_7879002 : Nat := 118140960795 + 7879002 * 2 ^ 59
def prefixEnd_7879002 : Nat := 4983230072969 + 3 ^ 40 * 7879002 * 2
def baseEnd_7879002 : Nat := 4045715103736087602140135

theorem tailTrace_7879002 : CollatzResearch.WordTrace tailWord_7879002 prefixEnd_7879002 4045715103736087602140135 := by
  unfold tailWord_7879002
  simp only [CollatzResearch.WordTrace]
  refine ⟨71842702850432213813979815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191580540934485903503946173 71842702850432213813979815)
  ·
    refine ⟨107764054275648320720969723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71842702850432213813979815 107764054275648320720969723)
    ·
      refine ⟨161646081413472481081454585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107764054275648320720969723 161646081413472481081454585)
      ·
        refine ⟨121234561060104360811090939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161646081413472481081454585 121234561060104360811090939)
        ·
          refine ⟨181851841590156541216636409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121234561060104360811090939 181851841590156541216636409)
          ·
            refine ⟨136388881192617405912477307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181851841590156541216636409 136388881192617405912477307)
            ·
              refine ⟨204583321788926108868715961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136388881192617405912477307 204583321788926108868715961)
              ·
                refine ⟨153437491341694581651536971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204583321788926108868715961 153437491341694581651536971)
                ·
                  refine ⟨230156237012541872477305457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153437491341694581651536971 230156237012541872477305457)
                  ·
                    refine ⟨172617177759406404357979093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230156237012541872477305457 172617177759406404357979093)
                    ·
                      refine ⟨4045715103736087602140135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172617177759406404357979093 4045715103736087602140135)
                      ·
                        rfl

theorem cell23_7879002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_7879002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879002 prefixEnd_7879002 := by exact prefixLift 7879002
  have htrace : WordTrace (prefixWord ++ tailWord_7879002) baseStart_7879002 baseEnd_7879002 := by
    simpa [prefixWord, tailWord_7879002, baseEnd_7879002] using wordTrace_append hprefix tailTrace_7879002
  have hstable : (prefixWord ++ tailWord_7879002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879002).length < 2 ^ (prefixWord ++ tailWord_7879002).sum := by decide
  have hdescent : baseEnd_7879002 < baseStart_7879002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879026 : List Nat := [3, 2, 1, 2, 1, 3, 2, 4, 5]
def baseStart_7879026 : Nat := 118140960795 + 7879026 * 2 ^ 59
def prefixEnd_7879026 : Nat := 4983230072969 + 3 ^ 40 * 7879026 * 2
def baseEnd_7879026 : Nat := 449525269696866167582225

theorem tailTrace_7879026 : CollatzResearch.WordTrace tailWord_7879026 prefixEnd_7879026 449525269696866167582225 := by
  unfold tailWord_7879026
  simp only [CollatzResearch.WordTrace]
  refine ⟨71842921688410476838698233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191581124502427938236528621 71842921688410476838698233)
  ·
    refine ⟨53882191266307857629023675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71842921688410476838698233 53882191266307857629023675)
    ·
      refine ⟨80823286899461786443535513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53882191266307857629023675 80823286899461786443535513)
      ·
        refine ⟨60617465174596339832651635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80823286899461786443535513 60617465174596339832651635)
        ·
          refine ⟨90926197761894509748977453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60617465174596339832651635 90926197761894509748977453)
          ·
            refine ⟨34097324160710441155866545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90926197761894509748977453 34097324160710441155866545)
            ·
              refine ⟨25572993120532830866899909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34097324160710441155866545 25572993120532830866899909)
              ·
                refine ⟨4794936210099905787543733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25572993120532830866899909 4794936210099905787543733)
                ·
                  refine ⟨449525269696866167582225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4794936210099905787543733 449525269696866167582225)
                  ·
                    rfl

theorem cell23_7879026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_7879026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879026 prefixEnd_7879026 := by exact prefixLift 7879026
  have htrace : WordTrace (prefixWord ++ tailWord_7879026) baseStart_7879026 baseEnd_7879026 := by
    simpa [prefixWord, tailWord_7879026, baseEnd_7879026] using wordTrace_append hprefix tailTrace_7879026
  have hstable : (prefixWord ++ tailWord_7879026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879026).length < 2 ^ (prefixWord ++ tailWord_7879026).sum := by decide
  have hdescent : baseEnd_7879026 < baseStart_7879026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879060 : List Nat := [2, 4, 2, 1, 3, 2, 1, 3, 5]
def baseStart_7879060 : Nat := 118140960795 + 7879060 * 2 ^ 59
def prefixEnd_7879060 : Nat := 4983230072969 + 3 ^ 40 * 7879060 * 2
def baseEnd_7879060 : Nat := 449527209512672041690541

theorem tailTrace_7879060 : CollatzResearch.WordTrace tailWord_7879060 prefixEnd_7879060 449527209512672041690541 := by
  unfold tailWord_7879060
  simp only [CollatzResearch.WordTrace]
  refine ⟨143686463417759365580765317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191581951223679154107687089 143686463417759365580765317)
  ·
    refine ⟨26941211890829881046393497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143686463417759365580765317 26941211890829881046393497)
    ·
      refine ⟨20205908918122410784795123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26941211890829881046393497 20205908918122410784795123)
      ·
        refine ⟨30308863377183616177192685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20205908918122410784795123 30308863377183616177192685)
        ·
          refine ⟨11365823766443856066447257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30308863377183616177192685 11365823766443856066447257)
          ·
            refine ⟨8524367824832892049835443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11365823766443856066447257 8524367824832892049835443)
            ·
              refine ⟨12786551737249338074753165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524367824832892049835443 12786551737249338074753165)
              ·
                refine ⟨4794956901468501778032437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12786551737249338074753165 4794956901468501778032437)
                ·
                  refine ⟨449527209512672041690541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4794956901468501778032437 449527209512672041690541)
                  ·
                    rfl

theorem cell23_7879060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_7879060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879060 prefixEnd_7879060 := by exact prefixLift 7879060
  have htrace : WordTrace (prefixWord ++ tailWord_7879060) baseStart_7879060 baseEnd_7879060 := by
    simpa [prefixWord, tailWord_7879060, baseEnd_7879060] using wordTrace_append hprefix tailTrace_7879060
  have hstable : (prefixWord ++ tailWord_7879060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879060).length < 2 ^ (prefixWord ++ tailWord_7879060).sum := by decide
  have hdescent : baseEnd_7879060 < baseStart_7879060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879073 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 2, 5]
def baseStart_7879073 : Nat := 118140960795 + 7879073 * 2 ^ 59
def prefixEnd_7879073 : Nat := 4983230072969 + 3 ^ 40 * 7879073 * 2
def baseEnd_7879073 : Nat := 1348583853620852274784103

theorem tailTrace_7879073 : CollatzResearch.WordTrace tailWord_7879073 prefixEnd_7879073 1348583853620852274784103 := by
  unfold tailWord_7879073
  simp only [CollatzResearch.WordTrace]
  refine ⟨287373400984471634381753873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191582267322981089587835915 287373400984471634381753873)
  ·
    refine ⟨215530050738353725786315405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287373400984471634381753873 215530050738353725786315405)
    ·
      refine ⟨80823769026882647169868277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215530050738353725786315405 80823769026882647169868277)
      ·
        refine ⟨7577228346270248172175151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80823769026882647169868277 7577228346270248172175151)
        ·
          refine ⟨11365842519405372258262727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7577228346270248172175151 11365842519405372258262727)
          ·
            refine ⟨17048763779108058387394091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11365842519405372258262727 17048763779108058387394091)
            ·
              refine ⟨25573145668662087581091137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17048763779108058387394091 25573145668662087581091137)
              ·
                refine ⟨19179859251496565685818353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25573145668662087581091137 19179859251496565685818353)
                ·
                  refine ⟨14384894438622424264363765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19179859251496565685818353 14384894438622424264363765)
                  ·
                    refine ⟨1348583853620852274784103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14384894438622424264363765 1348583853620852274784103)
                    ·
                      rfl

theorem cell23_7879073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_7879073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879073 prefixEnd_7879073 := by exact prefixLift 7879073
  have htrace : WordTrace (prefixWord ++ tailWord_7879073) baseStart_7879073 baseEnd_7879073 := by
    simpa [prefixWord, tailWord_7879073, baseEnd_7879073] using wordTrace_append hprefix tailTrace_7879073
  have hstable : (prefixWord ++ tailWord_7879073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879073).length < 2 ^ (prefixWord ++ tailWord_7879073).sum := by decide
  have hdescent : baseEnd_7879073 < baseStart_7879073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879076 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_7879076 : Nat := 118140960795 + 7879076 * 2 ^ 59
def prefixEnd_7879076 : Nat := 4983230072969 + 3 ^ 40 * 7879076 * 2
def baseEnd_7879076 : Nat := 4045753101304520312614795

theorem tailTrace_7879076 : CollatzResearch.WordTrace tailWord_7879076 prefixEnd_7879076 4045753101304520312614795 := by
  unfold tailWord_7879076
  simp only [CollatzResearch.WordTrace]
  refine ⟨143686755201730382947056541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191582340268973843929408721 143686755201730382947056541)
  ·
    refine ⟨53882533200648893605146203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143686755201730382947056541 53882533200648893605146203)
    ·
      refine ⟨80823799800973340407719305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53882533200648893605146203 80823799800973340407719305)
      ·
        refine ⟨60617849850730005305789479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80823799800973340407719305 60617849850730005305789479)
        ·
          refine ⟨90926774776095007958684219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60617849850730005305789479 90926774776095007958684219)
          ·
            refine ⟨136390162164142511938026329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90926774776095007958684219 136390162164142511938026329)
            ·
              refine ⟨102292621623106883953519747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136390162164142511938026329 102292621623106883953519747)
              ·
                refine ⟨153438932434660325930279621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102292621623106883953519747 153438932434660325930279621)
                ·
                  refine ⟨28769799831498811111927429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153438932434660325930279621 28769799831498811111927429)
                  ·
                    refine ⟨5394337468406027083486393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28769799831498811111927429 5394337468406027083486393)
                    ·
                      refine ⟨4045753101304520312614795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394337468406027083486393 4045753101304520312614795)
                      ·
                        rfl

theorem cell23_7879076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_7879076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879076 prefixEnd_7879076 := by exact prefixLift 7879076
  have htrace : WordTrace (prefixWord ++ tailWord_7879076) baseStart_7879076 baseEnd_7879076 := by
    simpa [prefixWord, tailWord_7879076, baseEnd_7879076] using wordTrace_append hprefix tailTrace_7879076
  have hstable : (prefixWord ++ tailWord_7879076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879076).length < 2 ^ (prefixWord ++ tailWord_7879076).sum := by decide
  have hdescent : baseEnd_7879076 < baseStart_7879076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879143 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_7879143 : Nat := 118140960795 + 7879143 * 2 ^ 59
def prefixEnd_7879143 : Nat := 4983230072969 + 3 ^ 40 * 7879143 * 2
def baseEnd_7879143 : Nat := 4045787504508371550476987

theorem tailTrace_7879143 : CollatzResearch.WordTrace tailWord_7879143 prefixEnd_7879143 4045787504508371550476987 := by
  unfold tailWord_7879143
  simp only [CollatzResearch.WordTrace]
  refine ⟨287375954094218036336802083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191583969396145357557868055 287375954094218036336802083)
  ·
    refine ⟨431063931141327054505203125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287375954094218036336802083 431063931141327054505203125)
    ·
      refine ⟨40412243544499411359862793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 431063931141327054505203125 40412243544499411359862793)
      ·
        refine ⟨30309182658374558519897095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40412243544499411359862793 30309182658374558519897095)
        ·
          refine ⟨45463773987561837779845643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30309182658374558519897095 45463773987561837779845643)
          ·
            refine ⟨68195660981342756669768465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45463773987561837779845643 68195660981342756669768465)
            ·
              refine ⟨51146745736007067502326349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68195660981342756669768465 51146745736007067502326349)
              ·
                refine ⟨19180029651002650313372381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51146745736007067502326349 19180029651002650313372381)
                ·
                  refine ⟨7192511119125993867514643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19180029651002650313372381 7192511119125993867514643)
                  ·
                    refine ⟨10788766678688990801271965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7192511119125993867514643 10788766678688990801271965)
                    ·
                      refine ⟨4045787504508371550476987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10788766678688990801271965 4045787504508371550476987)
                      ·
                        rfl

theorem cell23_7879143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_7879143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879143 prefixEnd_7879143 := by exact prefixLift 7879143
  have htrace : WordTrace (prefixWord ++ tailWord_7879143) baseStart_7879143 baseEnd_7879143 := by
    simpa [prefixWord, tailWord_7879143, baseEnd_7879143] using wordTrace_append hprefix tailTrace_7879143
  have hstable : (prefixWord ++ tailWord_7879143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879143).length < 2 ^ (prefixWord ++ tailWord_7879143).sum := by decide
  have hdescent : baseEnd_7879143 < baseStart_7879143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879146 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_7879146 : Nat := 118140960795 + 7879146 * 2 ^ 59
def prefixEnd_7879146 : Nat := 4983230072969 + 3 ^ 40 * 7879146 * 2
def baseEnd_7879146 : Nat := 1348596348316778346246491

theorem tailTrace_7879146 : CollatzResearch.WordTrace tailWord_7879146 prefixEnd_7879146 1348596348316778346246491 := by
  unfold tailWord_7879146
  simp only [CollatzResearch.WordTrace]
  refine ⟨71844015878301791962290323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191584042342138111899440861 71844015878301791962290323)
  ·
    refine ⟨107766023817452687943435485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71844015878301791962290323 107766023817452687943435485)
    ·
      refine ⟨40412258931544757978788307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107766023817452687943435485 40412258931544757978788307)
      ·
        refine ⟨60618388397317136968182461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40412258931544757978788307 60618388397317136968182461)
        ·
          refine ⟨22731895648993926363068423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60618388397317136968182461 22731895648993926363068423)
          ·
            refine ⟨34097843473490889544602635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22731895648993926363068423 34097843473490889544602635)
            ·
              refine ⟨51146765210236334316903953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34097843473490889544602635 51146765210236334316903953)
              ·
                refine ⟨38360073907677250737677965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51146765210236334316903953 38360073907677250737677965)
                ·
                  refine ⟨14385027715378969026629237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38360073907677250737677965 14385027715378969026629237)
                  ·
                    refine ⟨1348596348316778346246491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14385027715378969026629237 1348596348316778346246491)
                    ·
                      rfl

theorem cell23_7879146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_7879146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879146 prefixEnd_7879146 := by exact prefixLift 7879146
  have htrace : WordTrace (prefixWord ++ tailWord_7879146) baseStart_7879146 baseEnd_7879146 := by
    simpa [prefixWord, tailWord_7879146, baseEnd_7879146] using wordTrace_append hprefix tailTrace_7879146
  have hstable : (prefixWord ++ tailWord_7879146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879146).length < 2 ^ (prefixWord ++ tailWord_7879146).sum := by decide
  have hdescent : baseEnd_7879146 < baseStart_7879146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879176 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 4, 4]
def baseStart_7879176 : Nat := 118140960795 + 7879176 * 2 ^ 59
def prefixEnd_7879176 : Nat := 4983230072969 + 3 ^ 40 * 7879176 * 2
def baseEnd_7879176 : Nat := 1348601483123323307121445

theorem tailTrace_7879176 : CollatzResearch.WordTrace tailWord_7879176 prefixEnd_7879176 1348601483123323307121445 := by
  unfold tailWord_7879176
  simp only [CollatzResearch.WordTrace]
  refine ⟨143688578851549241486376691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191584771802065655315168921 143688578851549241486376691)
  ·
    refine ⟨215532868277323862229565037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143688578851549241486376691 215532868277323862229565037)
    ·
      refine ⟨80824825603996448336086889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215532868277323862229565037 80824825603996448336086889)
      ·
        refine ⟨60618619202997336252065167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80824825603996448336086889 60618619202997336252065167)
        ·
          refine ⟨90927928804496004378097751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60618619202997336252065167 90927928804496004378097751)
          ·
            refine ⟨136391893206744006567146627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90927928804496004378097751 136391893206744006567146627)
            ·
              refine ⟨204587839810116009850719941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136391893206744006567146627 204587839810116009850719941)
              ·
                refine ⟨38360219964396751847009989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204587839810116009850719941 38360219964396751847009989)
                ·
                  refine ⟨7192541243324390971314373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38360219964396751847009989 7192541243324390971314373)
                  ·
                    refine ⟨1348601483123323307121445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7192541243324390971314373 1348601483123323307121445)
                    ·
                      rfl

theorem cell23_7879176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_7879176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879176 prefixEnd_7879176 := by exact prefixLift 7879176
  have htrace : WordTrace (prefixWord ++ tailWord_7879176) baseStart_7879176 baseEnd_7879176 := by
    simpa [prefixWord, tailWord_7879176, baseEnd_7879176] using wordTrace_append hprefix tailTrace_7879176
  have hstable : (prefixWord ++ tailWord_7879176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879176).length < 2 ^ (prefixWord ++ tailWord_7879176).sum := by decide
  have hdescent : baseEnd_7879176 < baseStart_7879176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879180 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_7879180 : Nat := 118140960795 + 7879180 * 2 ^ 59
def prefixEnd_7879180 : Nat := 4983230072969 + 3 ^ 40 * 7879180 * 2
def baseEnd_7879180 : Nat := 1348602167764195968571439

theorem tailTrace_7879180 : CollatzResearch.WordTrace tailWord_7879180 prefixEnd_7879180 1348602167764195968571439 := by
  unfold tailWord_7879180
  simp only [CollatzResearch.WordTrace]
  refine ⟨143688651797541995827949497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191584869063389327770599329 143688651797541995827949497)
  ·
    refine ⟨107766488848156496870962123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143688651797541995827949497 107766488848156496870962123)
    ·
      refine ⟨161649733272234745306443185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107766488848156496870962123 161649733272234745306443185)
      ·
        refine ⟨121237299954176058979832389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161649733272234745306443185 121237299954176058979832389)
        ·
          refine ⟨22731993741408011058718573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121237299954176058979832389 22731993741408011058718573)
          ·
            refine ⟨8524497653028004147019465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22731993741408011058718573 8524497653028004147019465)
            ·
              refine ⟨6393373239771003110264599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8524497653028004147019465 6393373239771003110264599)
              ·
                refine ⟨9590059859656504665396899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6393373239771003110264599 9590059859656504665396899)
                ·
                  refine ⟨14385089789484756998095349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590059859656504665396899 14385089789484756998095349)
                  ·
                    refine ⟨1348602167764195968571439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14385089789484756998095349 1348602167764195968571439)
                    ·
                      rfl

theorem cell23_7879180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_7879180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879180 prefixEnd_7879180 := by exact prefixLift 7879180
  have htrace : WordTrace (prefixWord ++ tailWord_7879180) baseStart_7879180 baseEnd_7879180 := by
    simpa [prefixWord, tailWord_7879180, baseEnd_7879180] using wordTrace_append hprefix tailTrace_7879180
  have hstable : (prefixWord ++ tailWord_7879180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879180).length < 2 ^ (prefixWord ++ tailWord_7879180).sum := by decide
  have hdescent : baseEnd_7879180 < baseStart_7879180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879189 : List Nat := [1, 3, 2, 1, 3, 1, 12]
def baseStart_7879189 : Nat := 118140960795 + 7879189 * 2 ^ 59
def prefixEnd_7879189 : Nat := 4983230072969 + 3 ^ 40 * 7879189 * 2
def baseEnd_7879189 : Nat := 49948285489117016919775

theorem tailTrace_7879189 : CollatzResearch.WordTrace tailWord_7879189 prefixEnd_7879189 49948285489117016919775 := by
  unfold tailWord_7879189
  simp only [CollatzResearch.WordTrace]
  refine ⟨287377631852051386192976621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191585087901367590795317747 287377631852051386192976621)
  ·
    refine ⟨107766611944519269822366233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287377631852051386192976621 107766611944519269822366233)
    ·
      refine ⟨80824958958389452366774675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107766611944519269822366233 80824958958389452366774675)
      ·
        refine ⟨121237438437584178550162013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80824958958389452366774675 121237438437584178550162013)
        ·
          refine ⟨45464039414094066956310755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121237438437584178550162013 45464039414094066956310755)
          ·
            refine ⟨68196059121141100434466133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45464039414094066956310755 68196059121141100434466133)
            ·
              refine ⟨49948285489117016919775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 68196059121141100434466133 49948285489117016919775)
              ·
                rfl

theorem cell23_7879189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 12].length) (baseStart_7879189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879189 prefixEnd_7879189 := by exact prefixLift 7879189
  have htrace : WordTrace (prefixWord ++ tailWord_7879189) baseStart_7879189 baseEnd_7879189 := by
    simpa [prefixWord, tailWord_7879189, baseEnd_7879189] using wordTrace_append hprefix tailTrace_7879189
  have hstable : (prefixWord ++ tailWord_7879189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879189).length < 2 ^ (prefixWord ++ tailWord_7879189).sum := by decide
  have hdescent : baseEnd_7879189 < baseStart_7879189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879199 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_7879199 : Nat := 118140960795 + 7879199 * 2 ^ 59
def prefixEnd_7879199 : Nat := 4983230072969 + 3 ^ 40 * 7879199 * 2
def baseEnd_7879199 : Nat := 4045816259425023331376729

theorem tailTrace_7879199 : CollatzResearch.WordTrace tailWord_7879199 prefixEnd_7879199 4045816259425023331376729 := by
  unfold tailWord_7879199
  simp only [CollatzResearch.WordTrace]
  refine ⟨287377996582015157900840651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191585331054676771933893767 287377996582015157900840651)
  ·
    refine ⟨431066994873022736851260977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287377996582015157900840651 431066994873022736851260977)
    ·
      refine ⟨323300246154767052638445733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431066994873022736851260977 323300246154767052638445733)
      ·
        refine ⟨60618796154018822369708575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323300246154767052638445733 60618796154018822369708575)
        ·
          refine ⟨90928194231028233554562863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60618796154018822369708575 90928194231028233554562863)
          ·
            refine ⟨136392291346542350331844295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90928194231028233554562863 136392291346542350331844295)
            ·
              refine ⟨204588437019813525497766443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136392291346542350331844295 204588437019813525497766443)
              ·
                refine ⟨306882655529720288246649665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204588437019813525497766443 306882655529720288246649665)
                ·
                  refine ⟨230161991647290216184987249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306882655529720288246649665 230161991647290216184987249)
                  ·
                    refine ⟨172621493735467662138740437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230161991647290216184987249 172621493735467662138740437)
                    ·
                      refine ⟨4045816259425023331376729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172621493735467662138740437 4045816259425023331376729)
                      ·
                        rfl

theorem cell23_7879199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_7879199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879199 prefixEnd_7879199 := by exact prefixLift 7879199
  have htrace : WordTrace (prefixWord ++ tailWord_7879199) baseStart_7879199 baseEnd_7879199 := by
    simpa [prefixWord, tailWord_7879199, baseEnd_7879199] using wordTrace_append hprefix tailTrace_7879199
  have hstable : (prefixWord ++ tailWord_7879199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879199).length < 2 ^ (prefixWord ++ tailWord_7879199).sum := by decide
  have hdescent : baseEnd_7879199 < baseStart_7879199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879250 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_7879250 : Nat := 118140960795 + 7879250 * 2 ^ 59
def prefixEnd_7879250 : Nat := 4983230072969 + 3 ^ 40 * 7879250 * 2
def baseEnd_7879250 : Nat := 4045842446938402631838995

theorem tailTrace_7879250 : CollatzResearch.WordTrace tailWord_7879250 prefixEnd_7879250 4045842446938402631838995 := by
  unfold tailWord_7879250
  simp only [CollatzResearch.WordTrace]
  refine ⟨71844964176207598402736801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191586571136553595740631469 71844964176207598402736801)
  ·
    refine ⟨53883723132155698802052601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71844964176207598402736801 53883723132155698802052601)
    ·
      refine ⟨40412792349116774101539451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53883723132155698802052601 40412792349116774101539451)
      ·
        refine ⟨60619188523675161152309177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40412792349116774101539451 60619188523675161152309177)
        ·
          refine ⟨45464391392756370864231883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60619188523675161152309177 45464391392756370864231883)
          ·
            refine ⟨68196587089134556296347825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45464391392756370864231883 68196587089134556296347825)
            ·
              refine ⟨51147440316850917222260869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68196587089134556296347825 51147440316850917222260869)
              ·
                refine ⟨9590145059409546979173913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51147440316850917222260869 9590145059409546979173913)
                ·
                  refine ⟨7192608794557160234380435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9590145059409546979173913 7192608794557160234380435)
                  ·
                    refine ⟨10788913191835740351570653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7192608794557160234380435 10788913191835740351570653)
                    ·
                      refine ⟨4045842446938402631838995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10788913191835740351570653 4045842446938402631838995)
                      ·
                        rfl

theorem cell23_7879250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_7879250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879250 prefixEnd_7879250 := by exact prefixLift 7879250
  have htrace : WordTrace (prefixWord ++ tailWord_7879250) baseStart_7879250 baseEnd_7879250 := by
    simpa [prefixWord, tailWord_7879250, baseEnd_7879250] using wordTrace_append hprefix tailTrace_7879250
  have hstable : (prefixWord ++ tailWord_7879250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879250).length < 2 ^ (prefixWord ++ tailWord_7879250).sum := by decide
  have hdescent : baseEnd_7879250 < baseStart_7879250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879273 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 1, 4, 2]
def baseStart_7879273 : Nat := 118140960795 + 7879273 * 2 ^ 59
def prefixEnd_7879273 : Nat := 4983230072969 + 3 ^ 40 * 7879273 * 2
def baseEnd_7879273 : Nat := 4045854256993456041851389

theorem tailTrace_7879273 : CollatzResearch.WordTrace tailWord_7879273 prefixEnd_7879273 4045854256993456041851389 := by
  unfold tailWord_7879273
  simp only [CollatzResearch.WordTrace]
  refine ⟨287380695583747068539034473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191587130389164712359356315 287380695583747068539034473)
  ·
    refine ⟨215535521687810301404275855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287380695583747068539034473 215535521687810301404275855)
    ·
      refine ⟨323303282531715452106413783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215535521687810301404275855 323303282531715452106413783)
      ·
        refine ⟨484954923797573178159620675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323303282531715452106413783 484954923797573178159620675)
        ·
          refine ⟨727432385696359767239431013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484954923797573178159620675 727432385696359767239431013)
          ·
            refine ⟨136393572318067456357393315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 727432385696359767239431013 136393572318067456357393315)
            ·
              refine ⟨204590358477101184536089973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136393572318067456357393315 204590358477101184536089973)
              ·
                refine ⟨19180346107228236050258435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204590358477101184536089973 19180346107228236050258435)
                ·
                  refine ⟨28770519160842354075387653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19180346107228236050258435 28770519160842354075387653)
                  ·
                    refine ⟨5394472342657941389135185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28770519160842354075387653 5394472342657941389135185)
                    ·
                      refine ⟨4045854256993456041851389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394472342657941389135185 4045854256993456041851389)
                      ·
                        rfl

theorem cell23_7879273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 4, 2].length) (baseStart_7879273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879273 prefixEnd_7879273 := by exact prefixLift 7879273
  have htrace : WordTrace (prefixWord ++ tailWord_7879273) baseStart_7879273 baseEnd_7879273 := by
    simpa [prefixWord, tailWord_7879273, baseEnd_7879273] using wordTrace_append hprefix tailTrace_7879273
  have hstable : (prefixWord ++ tailWord_7879273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879273).length < 2 ^ (prefixWord ++ tailWord_7879273).sum := by decide
  have hdescent : baseEnd_7879273 < baseStart_7879273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879276 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_7879276 : Nat := 118140960795 + 7879276 * 2 ^ 59
def prefixEnd_7879276 : Nat := 4983230072969 + 3 ^ 40 * 7879276 * 2
def baseEnd_7879276 : Nat := 4045855797435419530113875

theorem tailTrace_7879276 : CollatzResearch.WordTrace tailWord_7879276 prefixEnd_7879276 4045855797435419530113875 := by
  unfold tailWord_7879276
  simp only [CollatzResearch.WordTrace]
  refine ⟨143690402501368100025696841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191587203335157466700929121 143690402501368100025696841)
  ·
    refine ⟨107767801876026075019272631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143690402501368100025696841 107767801876026075019272631)
    ·
      refine ⟨161651702814039112528908947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107767801876026075019272631 161651702814039112528908947)
      ·
        refine ⟨242477554221058668793363421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161651702814039112528908947 242477554221058668793363421)
        ·
          refine ⟨90929082832897000797511283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242477554221058668793363421 90929082832897000797511283)
          ·
            refine ⟨136393624249345501196266925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90929082832897000797511283 136393624249345501196266925)
            ·
              refine ⟨51147609093504562948600097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136393624249345501196266925 51147609093504562948600097)
              ·
                refine ⟨38360706820128422211450073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51147609093504562948600097 38360706820128422211450073)
                ·
                  refine ⟨28770530115096316658587555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38360706820128422211450073 28770530115096316658587555)
                  ·
                    refine ⟨43155795172644474987881333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28770530115096316658587555 43155795172644474987881333)
                    ·
                      refine ⟨4045855797435419530113875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43155795172644474987881333 4045855797435419530113875)
                      ·
                        rfl

theorem cell23_7879276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_7879276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879276 prefixEnd_7879276 := by exact prefixLift 7879276
  have htrace : WordTrace (prefixWord ++ tailWord_7879276) baseStart_7879276 baseEnd_7879276 := by
    simpa [prefixWord, tailWord_7879276, baseEnd_7879276] using wordTrace_append hprefix tailTrace_7879276
  have hstable : (prefixWord ++ tailWord_7879276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879276).length < 2 ^ (prefixWord ++ tailWord_7879276).sum := by decide
  have hdescent : baseEnd_7879276 < baseStart_7879276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879277 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_7879277 : Nat := 118140960795 + 7879277 * 2 ^ 59
def prefixEnd_7879277 : Nat := 4983230072969 + 3 ^ 40 * 7879277 * 2
def baseEnd_7879277 : Nat := 4045856310916074026201371

theorem tailTrace_7879277 : CollatzResearch.WordTrace tailWord_7879277 prefixEnd_7879277 4045856310916074026201371 := by
  unfold tailWord_7879277
  simp only [CollatzResearch.WordTrace]
  refine ⟨287380841475732577222180085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191587227650488384814786723 287380841475732577222180085)
  ·
    refine ⟨26941953888349929114579383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287380841475732577222180085 26941953888349929114579383)
    ·
      refine ⟨40412930832524893671869075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26941953888349929114579383 40412930832524893671869075)
      ·
        refine ⟨60619396248787340507803613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40412930832524893671869075 60619396248787340507803613)
        ·
          refine ⟨22732273593295252690426355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60619396248787340507803613 22732273593295252690426355)
          ·
            refine ⟨34098410389942879035639533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22732273593295252690426355 34098410389942879035639533)
            ·
              refine ⟨12786903896228579638364825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34098410389942879035639533 12786903896228579638364825)
              ·
                refine ⟨9590177922171434728773619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12786903896228579638364825 9590177922171434728773619)
                ·
                  refine ⟨14385266883257152093160429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590177922171434728773619 14385266883257152093160429)
                  ·
                    refine ⟨5394475081221432034935161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14385266883257152093160429 5394475081221432034935161)
                    ·
                      refine ⟨4045856310916074026201371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394475081221432034935161 4045856310916074026201371)
                      ·
                        rfl

theorem cell23_7879277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_7879277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879277 prefixEnd_7879277 := by exact prefixLift 7879277
  have htrace : WordTrace (prefixWord ++ tailWord_7879277) baseStart_7879277 baseEnd_7879277 := by
    simpa [prefixWord, tailWord_7879277, baseEnd_7879277] using wordTrace_append hprefix tailTrace_7879277
  have hstable : (prefixWord ++ tailWord_7879277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879277).length < 2 ^ (prefixWord ++ tailWord_7879277).sum := by decide
  have hdescent : baseEnd_7879277 < baseStart_7879277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879333 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 4, 5, 2]
def baseStart_7879333 : Nat := 118140960795 + 7879333 * 2 ^ 59
def prefixEnd_7879333 : Nat := 4983230072969 + 3 ^ 40 * 7879333 * 2
def baseEnd_7879333 : Nat := 4045885065832725807101113

theorem tailTrace_7879333 : CollatzResearch.WordTrace tailWord_7879333 prefixEnd_7879333 4045885065832725807101113 := by
  unfold tailWord_7879333
  simp only [CollatzResearch.WordTrace]
  refine ⟨287382883963529698786218653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191588589309019799190812435 287382883963529698786218653)
  ·
    refine ⟨107768581486323637044831995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287382883963529698786218653 107768581486323637044831995)
    ·
      refine ⟨161652872229485455567247993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107768581486323637044831995 161652872229485455567247993)
      ·
        refine ⟨121239654172114091675435995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161652872229485455567247993 121239654172114091675435995)
        ·
          refine ⟨181859481258171137513153993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121239654172114091675435995 181859481258171137513153993)
          ·
            refine ⟨136394610943628353134865495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181859481258171137513153993 136394610943628353134865495)
            ·
              refine ⟨204591916415442529702298243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136394610943628353134865495 204591916415442529702298243)
              ·
                refine ⟨306887874623163794553447365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204591916415442529702298243 306887874623163794553447365)
                ·
                  refine ⟨57541476491843211478771381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306887874623163794553447365 57541476491843211478771381)
                  ·
                    refine ⟨5394513421110301076134817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57541476491843211478771381 5394513421110301076134817)
                    ·
                      refine ⟨4045885065832725807101113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394513421110301076134817 4045885065832725807101113)
                      ·
                        rfl

theorem cell23_7879333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_7879333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879333 prefixEnd_7879333 := by exact prefixLift 7879333
  have htrace : WordTrace (prefixWord ++ tailWord_7879333) baseStart_7879333 baseEnd_7879333 := by
    simpa [prefixWord, tailWord_7879333, baseEnd_7879333] using wordTrace_append hprefix tailTrace_7879333
  have hstable : (prefixWord ++ tailWord_7879333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879333).length < 2 ^ (prefixWord ++ tailWord_7879333).sum := by decide
  have hdescent : baseEnd_7879333 < baseStart_7879333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879343 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 2, 5]
def baseStart_7879343 : Nat := 118140960795 + 7879343 * 2 ^ 59
def prefixEnd_7879343 : Nat := 4983230072969 + 3 ^ 40 * 7879343 * 2
def baseEnd_7879343 : Nat := 1348630066879756922658689

theorem tailTrace_7879343 : CollatzResearch.WordTrace tailWord_7879343 prefixEnd_7879343 1348630066879756922658689 := by
  unfold tailWord_7879343
  simp only [CollatzResearch.WordTrace]
  refine ⟨287383248693493470494082683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191588832462328980329388455 287383248693493470494082683)
  ·
    refine ⟨431074873040240205741124025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287383248693493470494082683 431074873040240205741124025)
    ·
      refine ⟨323306154780180154305843019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431074873040240205741124025 323306154780180154305843019)
      ·
        refine ⟨484959232170270231458764529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323306154780180154305843019 484959232170270231458764529)
        ·
          refine ⟨363719424127702673594073397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484959232170270231458764529 363719424127702673594073397)
          ·
            refine ⟨34098696011972125649444381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 363719424127702673594073397 34098696011972125649444381)
            ·
              refine ⟨12787011004489547118541643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34098696011972125649444381 12787011004489547118541643)
              ·
                refine ⟨19180516506734320677812465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12787011004489547118541643 19180516506734320677812465)
                ·
                  refine ⟨14385387380050740508359349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19180516506734320677812465 14385387380050740508359349)
                  ·
                    refine ⟨1348630066879756922658689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14385387380050740508359349 1348630066879756922658689)
                    ·
                      rfl

theorem cell23_7879343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_7879343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879343 prefixEnd_7879343 := by exact prefixLift 7879343
  have htrace : WordTrace (prefixWord ++ tailWord_7879343) baseStart_7879343 baseEnd_7879343 := by
    simpa [prefixWord, tailWord_7879343, baseEnd_7879343] using wordTrace_append hprefix tailTrace_7879343
  have hstable : (prefixWord ++ tailWord_7879343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879343).length < 2 ^ (prefixWord ++ tailWord_7879343).sum := by decide
  have hdescent : baseEnd_7879343 < baseStart_7879343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879383 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_7879383 : Nat := 118140960795 + 7879383 * 2 ^ 59
def prefixEnd_7879383 : Nat := 4983230072969 + 3 ^ 40 * 7879383 * 2
def baseEnd_7879383 : Nat := 4045910739865450611475883

theorem tailTrace_7879383 : CollatzResearch.WordTrace tailWord_7879383 prefixEnd_7879383 4045910739865450611475883 := by
  unfold tailWord_7879383
  simp only [CollatzResearch.WordTrace]
  refine ⟨287384707613348557325538803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191589805075565704883692535 287384707613348557325538803)
  ·
    refine ⟨431077061420022835988308205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287384707613348557325538803 431077061420022835988308205)
    ·
      refine ⟨161653898032508563495615577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431077061420022835988308205 161653898032508563495615577)
      ·
        refine ⟨121240423524381422621711683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161653898032508563495615577 121240423524381422621711683)
        ·
          refine ⟨181860635286572133932567525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121240423524381422621711683 181860635286572133932567525)
          ·
            refine ⟨34098869116232275112356411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181860635286572133932567525 34098869116232275112356411)
            ·
              refine ⟨51148303674348412668534617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34098869116232275112356411 51148303674348412668534617)
              ·
                refine ⟨38361227755761309501400963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51148303674348412668534617 38361227755761309501400963)
                ·
                  refine ⟨57541841633641964252101445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38361227755761309501400963 57541841633641964252101445)
                  ·
                    refine ⟨10789095306307868297269021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57541841633641964252101445 10789095306307868297269021)
                    ·
                      refine ⟨4045910739865450611475883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789095306307868297269021 4045910739865450611475883)
                      ·
                        rfl

theorem cell23_7879383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_7879383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879383 prefixEnd_7879383 := by exact prefixLift 7879383
  have htrace : WordTrace (prefixWord ++ tailWord_7879383) baseStart_7879383 baseEnd_7879383 := by
    simpa [prefixWord, tailWord_7879383, baseEnd_7879383] using wordTrace_append hprefix tailTrace_7879383
  have hstable : (prefixWord ++ tailWord_7879383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879383).length < 2 ^ (prefixWord ++ tailWord_7879383).sum := by decide
  have hdescent : baseEnd_7879383 < baseStart_7879383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879407 : List Nat := [1, 1, 2, 1, 5, 2, 3, 3, 1, 4]
def baseStart_7879407 : Nat := 118140960795 + 7879407 * 2 ^ 59
def prefixEnd_7879407 : Nat := 4983230072969 + 3 ^ 40 * 7879407 * 2
def baseEnd_7879407 : Nat := 1348641021133719505858591

theorem tailTrace_7879407 : CollatzResearch.WordTrace tailWord_7879407 prefixEnd_7879407 1348641021133719505858591 := by
  unfold tailWord_7879407
  simp only [CollatzResearch.WordTrace]
  refine ⟨287385582965261609424412475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191590388643507739616274983 287385582965261609424412475)
  ·
    refine ⟨431078374447892414136618713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287385582965261609424412475 431078374447892414136618713)
    ·
      refine ⟨323308780835919310602464035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431078374447892414136618713 323308780835919310602464035)
      ·
        refine ⟨484963171253878965903696053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323308780835919310602464035 484963171253878965903696053)
        ·
          refine ⟨45465297305051153053471505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 484963171253878965903696053 45465297305051153053471505)
          ·
            refine ⟨34098972978788364790103629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45465297305051153053471505 34098972978788364790103629)
            ·
              refine ⟨12787114867045636796288861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34098972978788364790103629 12787114867045636796288861)
              ·
                refine ⟨4795168075142113798608323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12787114867045636796288861 4795168075142113798608323)
                ·
                  refine ⟨7192752112713170697912485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795168075142113798608323 7192752112713170697912485)
                  ·
                    refine ⟨1348641021133719505858591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7192752112713170697912485 1348641021133719505858591)
                    ·
                      rfl

theorem cell23_7879407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 4].length) (baseStart_7879407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879407 prefixEnd_7879407 := by exact prefixLift 7879407
  have htrace : WordTrace (prefixWord ++ tailWord_7879407) baseStart_7879407 baseEnd_7879407 := by
    simpa [prefixWord, tailWord_7879407, baseEnd_7879407] using wordTrace_append hprefix tailTrace_7879407
  have hstable : (prefixWord ++ tailWord_7879407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879407).length < 2 ^ (prefixWord ++ tailWord_7879407).sum := by decide
  have hdescent : baseEnd_7879407 < baseStart_7879407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879457 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_7879457 : Nat := 118140960795 + 7879457 * 2 ^ 59
def prefixEnd_7879457 : Nat := 4983230072969 + 3 ^ 40 * 7879457 * 2
def baseEnd_7879457 : Nat := 4045948737433883321950543

theorem tailTrace_7879457 : CollatzResearch.WordTrace tailWord_7879457 prefixEnd_7879457 4045948737433883321950543 := by
  unfold tailWord_7879457
  simp only [CollatzResearch.WordTrace]
  refine ⟨287387406615080467963732625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191591604410053645309155083 287387406615080467963732625)
  ·
    refine ⟨215540554961310350972799469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287387406615080467963732625 215540554961310350972799469)
    ·
      refine ⟨80827708110491381614799801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215540554961310350972799469 80827708110491381614799801)
      ·
        refine ⟨60620781082868536211099851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80827708110491381614799801 60620781082868536211099851)
        ·
          refine ⟨90931171624302804316649777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60620781082868536211099851 90931171624302804316649777)
          ·
            refine ⟨68198378718227103237487333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90931171624302804316649777 68198378718227103237487333)
            ·
              refine ⟨12787196009667581857028875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68198378718227103237487333 12787196009667581857028875)
              ·
                refine ⟨19180794014501372785543313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12787196009667581857028875 19180794014501372785543313)
                ·
                  refine ⟨14385595510876029589157485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19180794014501372785543313 14385595510876029589157485)
                  ·
                    refine ⟨5394598316578511095934057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14385595510876029589157485 5394598316578511095934057)
                    ·
                      refine ⟨4045948737433883321950543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394598316578511095934057 4045948737433883321950543)
                      ·
                        rfl

theorem cell23_7879457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_7879457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879457 prefixEnd_7879457 := by exact prefixLift 7879457
  have htrace : WordTrace (prefixWord ++ tailWord_7879457) baseStart_7879457 baseEnd_7879457 := by
    simpa [prefixWord, tailWord_7879457, baseEnd_7879457] using wordTrace_append hprefix tailTrace_7879457
  have hstable : (prefixWord ++ tailWord_7879457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879457).length < 2 ^ (prefixWord ++ tailWord_7879457).sum := by decide
  have hdescent : baseEnd_7879457 < baseStart_7879457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879464 : List Nat := [2, 1, 5, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_7879464 : Nat := 118140960795 + 7879464 * 2 ^ 59
def prefixEnd_7879464 : Nat := 4983230072969 + 3 ^ 40 * 7879464 * 2
def baseEnd_7879464 : Nat := 4045952331798464794563011

theorem tailTrace_7879464 : CollatzResearch.WordTrace tailWord_7879464 prefixEnd_7879464 4045952331798464794563011 := by
  unfold tailWord_7879464
  simp only [CollatzResearch.WordTrace]
  refine ⟨143693830963027554079618723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191591774617370072106158297 143693830963027554079618723)
  ·
    refine ⟨215540746444541331119428085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143693830963027554079618723 215540746444541331119428085)
    ·
      refine ⟨20206944979175749792446383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215540746444541331119428085 20206944979175749792446383)
      ·
        refine ⟨30310417468763624688669575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20206944979175749792446383 30310417468763624688669575)
        ·
          refine ⟨45465626203145437033004363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30310417468763624688669575 45465626203145437033004363)
          ·
            refine ⟨68198439304718155549506545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45465626203145437033004363 68198439304718155549506545)
            ·
              refine ⟨51148829478538616662129909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68198439304718155549506545 51148829478538616662129909)
              ·
                refine ⟨4795202763612995312074679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51148829478538616662129909 4795202763612995312074679)
                ·
                  refine ⟨7192804145419492968112019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795202763612995312074679 7192804145419492968112019)
                  ·
                    refine ⟨10789206218129239452168029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7192804145419492968112019 10789206218129239452168029)
                    ·
                      refine ⟨4045952331798464794563011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789206218129239452168029 4045952331798464794563011)
                      ·
                        rfl

theorem cell23_7879464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_7879464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879464 prefixEnd_7879464 := by exact prefixLift 7879464
  have htrace : WordTrace (prefixWord ++ tailWord_7879464) baseStart_7879464 baseEnd_7879464 := by
    simpa [prefixWord, tailWord_7879464, baseEnd_7879464] using wordTrace_append hprefix tailTrace_7879464
  have hstable : (prefixWord ++ tailWord_7879464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879464).length < 2 ^ (prefixWord ++ tailWord_7879464).sum := by decide
  have hdescent : baseEnd_7879464 < baseStart_7879464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879500 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_7879500 : Nat := 118140960795 + 7879500 * 2 ^ 59
def prefixEnd_7879500 : Nat := 4983230072969 + 3 ^ 40 * 7879500 * 2
def baseEnd_7879500 : Nat := 4045970817102026653712845

theorem tailTrace_7879500 : CollatzResearch.WordTrace tailWord_7879500 prefixEnd_7879500 4045970817102026653712845 := by
  unfold tailWord_7879500
  simp only [CollatzResearch.WordTrace]
  refine ⟨143694487476962343153773977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191592649969283124205031969 143694487476962343153773977)
  ·
    refine ⟨107770865607721757365330483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143694487476962343153773977 107770865607721757365330483)
    ·
      refine ⟨161656298411582636047995725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107770865607721757365330483 161656298411582636047995725)
      ·
        refine ⟨60621111904343488517998397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161656298411582636047995725 60621111904343488517998397)
        ·
          refine ⟨22732916964128808194249399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60621111904343488517998397 22732916964128808194249399)
          ·
            refine ⟨34099375446193212291374099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22732916964128808194249399 34099375446193212291374099)
            ·
              refine ⟨51149063169289818437061149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34099375446193212291374099 51149063169289818437061149)
              ·
                refine ⟨19180898688483681913897931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51149063169289818437061149 19180898688483681913897931)
                ·
                  refine ⟨28771348032725522870846897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19180898688483681913897931 28771348032725522870846897)
                  ·
                    refine ⟨21578511024544142153135173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28771348032725522870846897 21578511024544142153135173)
                    ·
                      refine ⟨4045970817102026653712845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21578511024544142153135173 4045970817102026653712845)
                      ·
                        rfl

theorem cell23_7879500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_7879500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879500 prefixEnd_7879500 := by exact prefixLift 7879500
  have htrace : WordTrace (prefixWord ++ tailWord_7879500) baseStart_7879500 baseEnd_7879500 := by
    simpa [prefixWord, tailWord_7879500, baseEnd_7879500] using wordTrace_append hprefix tailTrace_7879500
  have hstable : (prefixWord ++ tailWord_7879500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879500).length < 2 ^ (prefixWord ++ tailWord_7879500).sum := by decide
  have hdescent : baseEnd_7879500 < baseStart_7879500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879520 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 3]
def baseStart_7879520 : Nat := 118140960795 + 7879520 * 2 ^ 59
def prefixEnd_7879520 : Nat := 4983230072969 + 3 ^ 40 * 7879520 * 2
def baseEnd_7879520 : Nat := 4045981086715116575462753

theorem tailTrace_7879520 : CollatzResearch.WordTrace tailWord_7879520 prefixEnd_7879520 4045981086715116575462753 := by
  unfold tailWord_7879520
  simp only [CollatzResearch.WordTrace]
  refine ⟨143694852206926114861638007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191593136275901486482184009 143694852206926114861638007)
  ·
    refine ⟨215542278310389172292457011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143694852206926114861638007 215542278310389172292457011)
    ·
      refine ⟨323313417465583758438685517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215542278310389172292457011 323313417465583758438685517)
      ·
        refine ⟨121242531549593909414507069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323313417465583758438685517 121242531549593909414507069)
        ·
          refine ⟨45465949331097716030440151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121242531549593909414507069 45465949331097716030440151)
          ·
            refine ⟨68198923996646574045660227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45465949331097716030440151 68198923996646574045660227)
            ·
              refine ⟨102298385994969861068490341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68198923996646574045660227 102298385994969861068490341)
              ·
                refine ⟨19180947374056848950341939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102298385994969861068490341 19180947374056848950341939)
                ·
                  refine ⟨28771421061085273425512909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19180947374056848950341939 28771421061085273425512909)
                  ·
                    refine ⟨10789282897906977534567341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28771421061085273425512909 10789282897906977534567341)
                    ·
                      refine ⟨4045981086715116575462753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789282897906977534567341 4045981086715116575462753)
                      ·
                        rfl

theorem cell23_7879520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_7879520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879520 prefixEnd_7879520 := by exact prefixLift 7879520
  have htrace : WordTrace (prefixWord ++ tailWord_7879520) baseStart_7879520 baseEnd_7879520 := by
    simpa [prefixWord, tailWord_7879520, baseEnd_7879520] using wordTrace_append hprefix tailTrace_7879520
  have hstable : (prefixWord ++ tailWord_7879520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879520).length < 2 ^ (prefixWord ++ tailWord_7879520).sum := by decide
  have hdescent : baseEnd_7879520 < baseStart_7879520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879524 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_7879524 : Nat := 118140960795 + 7879524 * 2 ^ 59
def prefixEnd_7879524 : Nat := 4983230072969 + 3 ^ 40 * 7879524 * 2
def baseEnd_7879524 : Nat := 4045983140637734559812735

theorem tailTrace_7879524 : CollatzResearch.WordTrace tailWord_7879524 prefixEnd_7879524 4045983140637734559812735 := by
  unfold tailWord_7879524
  simp only [CollatzResearch.WordTrace]
  refine ⟨143694925152918869203210813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191593233537225158937614417 143694925152918869203210813)
  ·
    refine ⟨53885596932344575951204055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143694925152918869203210813 53885596932344575951204055)
    ·
      refine ⟨80828395398516863926806083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53885596932344575951204055 80828395398516863926806083)
      ·
        refine ⟨121242593097775295890209125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80828395398516863926806083 121242593097775295890209125)
        ·
          refine ⟨22732986205832867979414211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121242593097775295890209125 22732986205832867979414211)
          ·
            refine ⟨34099479308749301969121317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22732986205832867979414211 34099479308749301969121317)
            ·
              refine ⟨6393652370390494119210247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34099479308749301969121317 6393652370390494119210247)
              ·
                refine ⟨9590478555585741178815371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6393652370390494119210247 9590478555585741178815371)
                ·
                  refine ⟨14385717833378611768223057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590478555585741178815371 14385717833378611768223057)
                  ·
                    refine ⟨10789288375033958826167293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14385717833378611768223057 10789288375033958826167293)
                    ·
                      refine ⟨4045983140637734559812735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789288375033958826167293 4045983140637734559812735)
                      ·
                        rfl

theorem cell23_7879524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_7879524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879524 prefixEnd_7879524 := by exact prefixLift 7879524
  have htrace : WordTrace (prefixWord ++ tailWord_7879524) baseStart_7879524 baseEnd_7879524 := by
    simpa [prefixWord, tailWord_7879524, baseEnd_7879524] using wordTrace_append hprefix tailTrace_7879524
  have hstable : (prefixWord ++ tailWord_7879524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879524).length < 2 ^ (prefixWord ++ tailWord_7879524).sum := by decide
  have hdescent : baseEnd_7879524 < baseStart_7879524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879537 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 3]
def baseStart_7879537 : Nat := 118140960795 + 7879537 * 2 ^ 59
def prefixEnd_7879537 : Nat := 4983230072969 + 3 ^ 40 * 7879537 * 2
def baseEnd_7879537 : Nat := 4045989815886243008950175

theorem tailTrace_7879537 : CollatzResearch.WordTrace tailWord_7879537 prefixEnd_7879537 4045989815886243008950175 := by
  unfold tailWord_7879537
  simp only [CollatzResearch.WordTrace]
  refine ⟨287390324454790641626644865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191593549636527094417763243 287390324454790641626644865)
  ·
    refine ⟨215542743341092981219983649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287390324454790641626644865 215542743341092981219983649)
    ·
      refine ⟨161657057505819735914987737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215542743341092981219983649 161657057505819735914987737)
      ·
        refine ⟨121242793129364801936240803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161657057505819735914987737 121242793129364801936240803)
        ·
          refine ⟨181864189694047202904361205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121242793129364801936240803 181864189694047202904361205)
          ·
            refine ⟨17049767783816925272283863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181864189694047202904361205 17049767783816925272283863)
            ·
              refine ⟨25574651675725387908425795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17049767783816925272283863 25574651675725387908425795)
              ·
                refine ⟨38361977513588081862638693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25574651675725387908425795 38361977513588081862638693)
                ·
                  refine ⟨7192870783797765349244755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38361977513588081862638693 7192870783797765349244755)
                  ·
                    refine ⟨10789306175696648023867133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7192870783797765349244755 10789306175696648023867133)
                    ·
                      refine ⟨4045989815886243008950175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789306175696648023867133 4045989815886243008950175)
                      ·
                        rfl

theorem cell23_7879537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_7879537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879537 prefixEnd_7879537 := by exact prefixLift 7879537
  have htrace : WordTrace (prefixWord ++ tailWord_7879537) baseStart_7879537 baseEnd_7879537 := by
    simpa [prefixWord, tailWord_7879537, baseEnd_7879537] using wordTrace_append hprefix tailTrace_7879537
  have hstable : (prefixWord ++ tailWord_7879537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879537).length < 2 ^ (prefixWord ++ tailWord_7879537).sum := by decide
  have hdescent : baseEnd_7879537 < baseStart_7879537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879543 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_7879543 : Nat := 118140960795 + 7879543 * 2 ^ 59
def prefixEnd_7879543 : Nat := 4983230072969 + 3 ^ 40 * 7879543 * 2
def baseEnd_7879543 : Nat := 4045992896770169985475147

theorem tailTrace_7879543 : CollatzResearch.WordTrace tailWord_7879543 prefixEnd_7879543 4045992896770169985475147 := by
  unfold tailWord_7879543
  simp only [CollatzResearch.WordTrace]
  refine ⟨287390543292768904651363283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191593695528512603100908855 287390543292768904651363283)
  ·
    refine ⟨431085814939153356977044925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287390543292768904651363283 431085814939153356977044925)
    ·
      refine ⟨161657180602182508866391847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431085814939153356977044925 161657180602182508866391847)
      ·
        refine ⟨242485770903273763299587771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161657180602182508866391847 242485770903273763299587771)
        ·
          refine ⟨363728656354910644949381657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242485770903273763299587771 363728656354910644949381657)
          ·
            refine ⟨272796492266182983712036243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363728656354910644949381657 272796492266182983712036243)
            ·
              refine ⟨409194738399274475568054365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272796492266182983712036243 409194738399274475568054365)
              ·
                refine ⟨153448026899727928338020387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409194738399274475568054365 153448026899727928338020387)
                ·
                  refine ⟨230172040349591892507030581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153448026899727928338020387 230172040349591892507030581)
                  ·
                    refine ⟨21578628782774239922534117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 230172040349591892507030581 21578628782774239922534117)
                    ·
                      refine ⟨4045992896770169985475147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21578628782774239922534117 4045992896770169985475147)
                      ·
                        rfl

theorem cell23_7879543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_7879543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879543 prefixEnd_7879543 := by exact prefixLift 7879543
  have htrace : WordTrace (prefixWord ++ tailWord_7879543) baseStart_7879543 baseEnd_7879543 := by
    simpa [prefixWord, tailWord_7879543, baseEnd_7879543] using wordTrace_append hprefix tailTrace_7879543
  have hstable : (prefixWord ++ tailWord_7879543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879543).length < 2 ^ (prefixWord ++ tailWord_7879543).sum := by decide
  have hdescent : baseEnd_7879543 < baseStart_7879543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879593 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_7879593 : Nat := 118140960795 + 7879593 * 2 ^ 59
def prefixEnd_7879593 : Nat := 4983230072969 + 3 ^ 40 * 7879593 * 2
def baseEnd_7879593 : Nat := 4046018570802894789849917

theorem tailTrace_7879593 : CollatzResearch.WordTrace tailWord_7879593 prefixEnd_7879593 4046018570802894789849917 := by
  unfold tailWord_7879593
  simp only [CollatzResearch.WordTrace]
  refine ⟨287392366942587763190683433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191594911295058508793788955 287392366942587763190683433)
  ·
    refine ⟨215544275206940822393012575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287392366942587763190683433 215544275206940822393012575)
    ·
      refine ⟨323316412810411233589518863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215544275206940822393012575 323316412810411233589518863)
      ·
        refine ⟨484974619215616850384278295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323316412810411233589518863 484974619215616850384278295)
        ·
          refine ⟨727461928823425275576417443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484974619215616850384278295 727461928823425275576417443)
          ·
            refine ⟨1091192893235137913364626165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727461928823425275576417443 1091192893235137913364626165)
            ·
              refine ⟨102299333740794179377933703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1091192893235137913364626165 102299333740794179377933703)
              ·
                refine ⟨153449000611191269066900555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102299333740794179377933703 153449000611191269066900555)
                ·
                  refine ⟨230173500916786903600350833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153449000611191269066900555 230173500916786903600350833)
                  ·
                    refine ⟨172630125687590177700263125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230173500916786903600350833 172630125687590177700263125)
                    ·
                      refine ⟨4046018570802894789849917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172630125687590177700263125 4046018570802894789849917)
                      ·
                        rfl

theorem cell23_7879593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_7879593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879593 prefixEnd_7879593 := by exact prefixLift 7879593
  have htrace : WordTrace (prefixWord ++ tailWord_7879593) baseStart_7879593 baseEnd_7879593 := by
    simpa [prefixWord, tailWord_7879593, baseEnd_7879593] using wordTrace_append hprefix tailTrace_7879593
  have hstable : (prefixWord ++ tailWord_7879593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879593).length < 2 ^ (prefixWord ++ tailWord_7879593).sum := by decide
  have hdescent : baseEnd_7879593 < baseStart_7879593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879603 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 8]
def baseStart_7879603 : Nat := 118140960795 + 7879603 * 2 ^ 59
def prefixEnd_7879603 : Nat := 4983230072969 + 3 ^ 40 * 7879603 * 2
def baseEnd_7879603 : Nat := 4046023705609439750724871

theorem tailTrace_7879603 : CollatzResearch.WordTrace tailWord_7879603 prefixEnd_7879603 4046023705609439750724871 := by
  unfold tailWord_7879603
  simp only [CollatzResearch.WordTrace]
  refine ⟨287392731672551534898547463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191595154448367689932364975 287392731672551534898547463)
  ·
    refine ⟨431089097508827302347821195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287392731672551534898547463 431089097508827302347821195)
    ·
      refine ⟨646633646263240953521731793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431089097508827302347821195 646633646263240953521731793)
      ·
        refine ⟨484975234697430715141298845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646633646263240953521731793 484975234697430715141298845)
        ·
          refine ⟨181865713011536518177987067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484975234697430715141298845 181865713011536518177987067)
          ·
            refine ⟨272798569517304777266980601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181865713011536518177987067 272798569517304777266980601)
            ·
              refine ⟨204598927137978582950235451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272798569517304777266980601 204598927137978582950235451)
              ·
                refine ⟨306898390706967874425353177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204598927137978582950235451 306898390706967874425353177)
                ·
                  refine ⟨230173793030225905819014883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306898390706967874425353177 230173793030225905819014883)
                  ·
                    refine ⟨345260689545338858728522325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230173793030225905819014883 345260689545338858728522325)
                    ·
                      refine ⟨4046023705609439750724871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 345260689545338858728522325 4046023705609439750724871)
                      ·
                        rfl

theorem cell23_7879603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_7879603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879603 prefixEnd_7879603 := by exact prefixLift 7879603
  have htrace : WordTrace (prefixWord ++ tailWord_7879603) baseStart_7879603 baseEnd_7879603 := by
    simpa [prefixWord, tailWord_7879603, baseEnd_7879603] using wordTrace_append hprefix tailTrace_7879603
  have hstable : (prefixWord ++ tailWord_7879603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879603).length < 2 ^ (prefixWord ++ tailWord_7879603).sum := by decide
  have hdescent : baseEnd_7879603 < baseStart_7879603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879610 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_7879610 : Nat := 118140960795 + 7879610 * 2 ^ 59
def prefixEnd_7879610 : Nat := 4983230072969 + 3 ^ 40 * 7879610 * 2
def baseEnd_7879610 : Nat := 4046027299974021223337339

theorem tailTrace_7879610 : CollatzResearch.WordTrace tailWord_7879610 prefixEnd_7879610 4046027299974021223337339 := by
  unfold tailWord_7879610
  simp only [CollatzResearch.WordTrace]
  refine ⟨71848246745881543773513071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191595324655684116729368189 71848246745881543773513071)
  ·
    refine ⟨107772370118822315660269607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71848246745881543773513071 107772370118822315660269607)
    ·
      refine ⟨161658555178233473490404411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107772370118822315660269607 161658555178233473490404411)
      ·
        refine ⟨242487832767350210235606617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161658555178233473490404411 242487832767350210235606617)
        ·
          refine ⟨181865874575512657676704963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242487832767350210235606617 181865874575512657676704963)
          ·
            refine ⟨272798811863268986515057445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181865874575512657676704963 272798811863268986515057445)
            ·
              refine ⟨51149777224362934971573271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272798811863268986515057445 51149777224362934971573271)
              ·
                refine ⟨76724665836544402457359907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51149777224362934971573271 76724665836544402457359907)
                ·
                  refine ⟨115086998754816603686039861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76724665836544402457359907 115086998754816603686039861)
                  ·
                    refine ⟨10789406133264056595566237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115086998754816603686039861 10789406133264056595566237)
                    ·
                      refine ⟨4046027299974021223337339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789406133264056595566237 4046027299974021223337339)
                      ·
                        rfl

theorem cell23_7879610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_7879610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879610 prefixEnd_7879610 := by exact prefixLift 7879610
  have htrace : WordTrace (prefixWord ++ tailWord_7879610) baseStart_7879610 baseEnd_7879610 := by
    simpa [prefixWord, tailWord_7879610, baseEnd_7879610] using wordTrace_append hprefix tailTrace_7879610
  have hstable : (prefixWord ++ tailWord_7879610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879610).length < 2 ^ (prefixWord ++ tailWord_7879610).sum := by decide
  have hdescent : baseEnd_7879610 < baseStart_7879610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879640 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_7879640 : Nat := 118140960795 + 7879640 * 2 ^ 59
def prefixEnd_7879640 : Nat := 4983230072969 + 3 ^ 40 * 7879640 * 2
def baseEnd_7879640 : Nat := 4046042704393656105962201

theorem tailTrace_7879640 : CollatzResearch.WordTrace tailWord_7879640 prefixEnd_7879640 4046042704393656105962201 := by
  unfold tailWord_7879640
  simp only [CollatzResearch.WordTrace]
  refine ⟨143697040586708745108822187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191596054115611660145096249 143697040586708745108822187)
  ·
    refine ⟨215545560880063117663233281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143697040586708745108822187 215545560880063117663233281)
    ·
      refine ⟨161659170660047338247424961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215545560880063117663233281 161659170660047338247424961)
      ·
        refine ⟨121244377995035503685568721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161659170660047338247424961 121244377995035503685568721)
        ·
          refine ⟨90933283496276627764176541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121244377995035503685568721 90933283496276627764176541)
          ·
            refine ⟨34099981311103735411566203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90933283496276627764176541 34099981311103735411566203)
            ·
              refine ⟨51149971966655603117349305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34099981311103735411566203 51149971966655603117349305)
              ·
                refine ⟨38362478974991702338011979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51149971966655603117349305 38362478974991702338011979)
                ·
                  refine ⟨57543718462487553507017969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38362478974991702338011979 57543718462487553507017969)
                  ·
                    refine ⟨43157788846865665130263477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57543718462487553507017969 43157788846865665130263477)
                    ·
                      refine ⟨4046042704393656105962201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43157788846865665130263477 4046042704393656105962201)
                      ·
                        rfl

theorem cell23_7879640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_7879640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879640 prefixEnd_7879640 := by exact prefixLift 7879640
  have htrace : WordTrace (prefixWord ++ tailWord_7879640) baseStart_7879640 baseEnd_7879640 := by
    simpa [prefixWord, tailWord_7879640, baseEnd_7879640] using wordTrace_append hprefix tailTrace_7879640
  have hstable : (prefixWord ++ tailWord_7879640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879640).length < 2 ^ (prefixWord ++ tailWord_7879640).sum := by decide
  have hdescent : baseEnd_7879640 < baseStart_7879640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879668 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 7]
def baseStart_7879668 : Nat := 118140960795 + 7879668 * 2 ^ 59
def prefixEnd_7879668 : Nat := 4983230072969 + 3 ^ 40 * 7879668 * 2
def baseEnd_7879668 : Nat := 449561897983553555156897

theorem tailTrace_7879668 : CollatzResearch.WordTrace tailWord_7879668 prefixEnd_7879668 449561897983553555156897 := by
  unfold tailWord_7879668
  simp only [CollatzResearch.WordTrace]
  refine ⟨143697551208658025499831829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191596734944877367333109105 143697551208658025499831829)
  ·
    refine ⟨6735822712905844945304617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143697551208658025499831829 6735822712905844945304617)
    ·
      refine ⟨5051867034679383708978463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6735822712905844945304617 5051867034679383708978463)
      ·
        refine ⟨7577800552019075563467695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5051867034679383708978463 7577800552019075563467695)
        ·
          refine ⟨11366700828028613345201543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7577800552019075563467695 11366700828028613345201543)
          ·
            refine ⟨17050051242042920017802315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11366700828028613345201543 17050051242042920017802315)
            ·
              refine ⟨25575076863064380026703473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17050051242042920017802315 25575076863064380026703473)
              ·
                refine ⟨19181307647298285020027605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25575076863064380026703473 19181307647298285020027605)
                ·
                  refine ⟨449561897983553555156897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19181307647298285020027605 449561897983553555156897)
                  ·
                    rfl

theorem cell23_7879668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_7879668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879668 prefixEnd_7879668 := by exact prefixLift 7879668
  have htrace : WordTrace (prefixWord ++ tailWord_7879668) baseStart_7879668 baseEnd_7879668 := by
    simpa [prefixWord, tailWord_7879668, baseEnd_7879668] using wordTrace_append hprefix tailTrace_7879668
  have hstable : (prefixWord ++ tailWord_7879668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879668).length < 2 ^ (prefixWord ++ tailWord_7879668).sum := by decide
  have hdescent : baseEnd_7879668 < baseStart_7879668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879687 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_7879687 : Nat := 118140960795 + 7879687 * 2 ^ 59
def prefixEnd_7879687 : Nat := 4983230072969 + 3 ^ 40 * 7879687 * 2
def baseEnd_7879687 : Nat := 4046066837984417422074485

theorem tailTrace_7879687 : CollatzResearch.WordTrace tailWord_7879687 prefixEnd_7879687 4046066837984417422074485 := by
  unfold tailWord_7879687
  simp only [CollatzResearch.WordTrace]
  refine ⟨287395795404247217244605315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191597196936164811496403543 287395795404247217244605315)
  ·
    refine ⟨431093693106370825866907973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287395795404247217244605315 431093693106370825866907973)
    ·
      refine ⟨80830067457444529850045245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431093693106370825866907973 80830067457444529850045245)
      ·
        refine ⟨30311275296541698693766967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80830067457444529850045245 30311275296541698693766967)
        ·
          refine ⟨45466912944812548040650451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30311275296541698693766967 45466912944812548040650451)
          ·
            refine ⟨68200369417218822060975677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45466912944812548040650451 68200369417218822060975677)
            ·
              refine ⟨25575138531457058272865879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68200369417218822060975677 25575138531457058272865879)
              ·
                refine ⟨38362707797185587409298819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25575138531457058272865879 38362707797185587409298819)
                ·
                  refine ⟨57544061695778381113948229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38362707797185587409298819 57544061695778381113948229)
                  ·
                    refine ⟨10789511567958446458865293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57544061695778381113948229 10789511567958446458865293)
                    ·
                      refine ⟨4046066837984417422074485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789511567958446458865293 4046066837984417422074485)
                      ·
                        rfl

theorem cell23_7879687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_7879687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879687 prefixEnd_7879687 := by exact prefixLift 7879687
  have htrace : WordTrace (prefixWord ++ tailWord_7879687) baseStart_7879687 baseEnd_7879687 := by
    simpa [prefixWord, tailWord_7879687, baseEnd_7879687] using wordTrace_append hprefix tailTrace_7879687
  have hstable : (prefixWord ++ tailWord_7879687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879687).length < 2 ^ (prefixWord ++ tailWord_7879687).sum := by decide
  have hdescent : baseEnd_7879687 < baseStart_7879687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879744 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 2, 3, 2]
def baseStart_7879744 : Nat := 118140960795 + 7879744 * 2 ^ 59
def prefixEnd_7879744 : Nat := 4983230072969 + 3 ^ 40 * 7879744 * 2
def baseEnd_7879744 : Nat := 4046096106381723699061723

theorem tailTrace_7879744 : CollatzResearch.WordTrace tailWord_7879744 prefixEnd_7879744 4046096106381723699061723 := by
  unfold tailWord_7879744
  simp only [CollatzResearch.WordTrace]
  refine ⟨143698937182520357989715143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191598582910027143986286857 143698937182520357989715143)
  ·
    refine ⟨215548405773780536984572715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143698937182520357989715143 215548405773780536984572715)
    ·
      refine ⟨323322608660670805476859073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215548405773780536984572715 323322608660670805476859073)
      ·
        refine ⟨242491956495503104107644305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323322608660670805476859073 242491956495503104107644305)
        ·
          refine ⟨181868967371627328080733229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242491956495503104107644305 181868967371627328080733229)
          ·
            refine ⟨68200862764360248030274961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181868967371627328080733229 68200862764360248030274961)
            ·
              refine ⟨51150647073270186022706221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68200862764360248030274961 51150647073270186022706221)
              ·
                refine ⟨19181492652476319758514833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51150647073270186022706221 19181492652476319758514833)
                ·
                  refine ⟨14386119489357239818886125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19181492652476319758514833 14386119489357239818886125)
                  ·
                    refine ⟨5394794808508964932082297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14386119489357239818886125 5394794808508964932082297)
                    ·
                      refine ⟨4046096106381723699061723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394794808508964932082297 4046096106381723699061723)
                      ·
                        rfl

theorem cell23_7879744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_7879744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879744 prefixEnd_7879744 := by exact prefixLift 7879744
  have htrace : WordTrace (prefixWord ++ tailWord_7879744) baseStart_7879744 baseEnd_7879744 := by
    simpa [prefixWord, tailWord_7879744, baseEnd_7879744] using wordTrace_append hprefix tailTrace_7879744
  have hstable : (prefixWord ++ tailWord_7879744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879744).length < 2 ^ (prefixWord ++ tailWord_7879744).sum := by decide
  have hdescent : baseEnd_7879744 < baseStart_7879744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879745 : List Nat := [1, 2, 5, 1, 4, 1, 1, 3, 1, 4]
def baseStart_7879745 : Nat := 118140960795 + 7879745 * 2 ^ 59
def prefixEnd_7879745 : Nat := 4983230072969 + 3 ^ 40 * 7879745 * 2
def baseEnd_7879745 : Nat := 1348698873287459398383073

theorem tailTrace_7879745 : CollatzResearch.WordTrace tailWord_7879745 prefixEnd_7879745 1348698873287459398383073 := by
  unfold tailWord_7879745
  simp only [CollatzResearch.WordTrace]
  refine ⟨287397910838037093150216689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191598607225358062100144459 287397910838037093150216689)
  ·
    refine ⟨215548433128527819862662517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287397910838037093150216689 215548433128527819862662517)
    ·
      refine ⟨20207665605799483112124611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215548433128527819862662517 20207665605799483112124611)
      ·
        refine ⟨30311498408699224668186917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20207665605799483112124611 30311498408699224668186917)
        ·
          refine ⟨5683405951631104625285047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30311498408699224668186917 5683405951631104625285047)
          ·
            refine ⟨8525108927446656937927571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5683405951631104625285047 8525108927446656937927571)
            ·
              refine ⟨12787663391169985406891357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8525108927446656937927571 12787663391169985406891357)
              ·
                refine ⟨4795373771688744527584259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12787663391169985406891357 4795373771688744527584259)
                ·
                  refine ⟨7193060657533116791376389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795373771688744527584259 7193060657533116791376389)
                  ·
                    refine ⟨1348698873287459398383073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7193060657533116791376389 1348698873287459398383073)
                    ·
                      rfl

theorem cell23_7879745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_7879745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879745 prefixEnd_7879745 := by exact prefixLift 7879745
  have htrace : WordTrace (prefixWord ++ tailWord_7879745) baseStart_7879745 baseEnd_7879745 := by
    simpa [prefixWord, tailWord_7879745, baseEnd_7879745] using wordTrace_append hprefix tailTrace_7879745
  have hstable : (prefixWord ++ tailWord_7879745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879745).length < 2 ^ (prefixWord ++ tailWord_7879745).sum := by decide
  have hdescent : baseEnd_7879745 < baseStart_7879745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879768 : List Nat := [2, 1, 2, 2, 1, 3, 5, 2, 1, 1, 3]
def baseStart_7879768 : Nat := 118140960795 + 7879768 * 2 ^ 59
def prefixEnd_7879768 : Nat := 4983230072969 + 3 ^ 40 * 7879768 * 2
def baseEnd_7879768 : Nat := 4046108429917431605161613

theorem tailTrace_7879768 : CollatzResearch.WordTrace tailWord_7879768 prefixEnd_7879768 4046108429917431605161613 := by
  unfold tailWord_7879768
  simp only [CollatzResearch.WordTrace]
  refine ⟨143699374858476884039151979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191599166477969178718869305 143699374858476884039151979)
  ·
    refine ⟨215549062287715326058727969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143699374858476884039151979 215549062287715326058727969)
    ·
      refine ⟨161661796715786494544045977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215549062287715326058727969 161661796715786494544045977)
      ·
        refine ⟨121246347536839870908034483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161661796715786494544045977 121246347536839870908034483)
        ·
          refine ⟨181869521305259806362051725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121246347536839870908034483 181869521305259806362051725)
          ·
            refine ⟨68201070489472427385769397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181869521305259806362051725 68201070489472427385769397)
            ·
              refine ⟨6393850358388040067415881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68201070489472427385769397 6393850358388040067415881)
              ·
                refine ⟨4795387768791030050561911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6393850358388040067415881 4795387768791030050561911)
                ·
                  refine ⟨7193081653186545075842867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795387768791030050561911 7193081653186545075842867)
                  ·
                    refine ⟨10789622479779817613764301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7193081653186545075842867 10789622479779817613764301)
                    ·
                      refine ⟨4046108429917431605161613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789622479779817613764301 4046108429917431605161613)
                      ·
                        rfl

theorem cell23_7879768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_7879768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879768 prefixEnd_7879768 := by exact prefixLift 7879768
  have htrace : WordTrace (prefixWord ++ tailWord_7879768) baseStart_7879768 baseEnd_7879768 := by
    simpa [prefixWord, tailWord_7879768, baseEnd_7879768] using wordTrace_append hprefix tailTrace_7879768
  have hstable : (prefixWord ++ tailWord_7879768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879768).length < 2 ^ (prefixWord ++ tailWord_7879768).sum := by decide
  have hdescent : baseEnd_7879768 < baseStart_7879768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879777 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_7879777 : Nat := 118140960795 + 7879777 * 2 ^ 59
def prefixEnd_7879777 : Nat := 4983230072969 + 3 ^ 40 * 7879777 * 2
def baseEnd_7879777 : Nat := 4046113051243322069949071

theorem tailTrace_7879777 : CollatzResearch.WordTrace tailWord_7879777 prefixEnd_7879777 4046113051243322069949071 := by
  unfold tailWord_7879777
  simp only [CollatzResearch.WordTrace]
  refine ⟨287399077973921162615381585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191599385315947441743587723 287399077973921162615381585)
  ·
    refine ⟨215549308480440871961536189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287399077973921162615381585 215549308480440871961536189)
    ·
      refine ⟨80830990680165326985576071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215549308480440871961536189 80830990680165326985576071)
      ·
        refine ⟨121246486020247990478364107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80830990680165326985576071 121246486020247990478364107)
        ·
          refine ⟨181869729030371985717546161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121246486020247990478364107 181869729030371985717546161)
          ·
            refine ⟨136402296772778989288159621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181869729030371985717546161 136402296772778989288159621)
            ·
              refine ⟨25575430644896060491529929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136402296772778989288159621 25575430644896060491529929)
              ·
                refine ⟨19181572983672045368647447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25575430644896060491529929 19181572983672045368647447)
                ·
                  refine ⟨28772359475508068052971171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19181572983672045368647447 28772359475508068052971171)
                  ·
                    refine ⟨43158539213262102079456757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28772359475508068052971171 43158539213262102079456757)
                    ·
                      refine ⟨4046113051243322069949071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43158539213262102079456757 4046113051243322069949071)
                      ·
                        rfl

theorem cell23_7879777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_7879777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879777 prefixEnd_7879777 := by exact prefixLift 7879777
  have htrace : WordTrace (prefixWord ++ tailWord_7879777) baseStart_7879777 baseEnd_7879777 := by
    simpa [prefixWord, tailWord_7879777, baseEnd_7879777] using wordTrace_append hprefix tailTrace_7879777
  have hstable : (prefixWord ++ tailWord_7879777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879777).length < 2 ^ (prefixWord ++ tailWord_7879777).sum := by decide
  have hdescent : baseEnd_7879777 < baseStart_7879777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879794 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_7879794 : Nat := 118140960795 + 7879794 * 2 ^ 59
def prefixEnd_7879794 : Nat := 4983230072969 + 3 ^ 40 * 7879794 * 2
def baseEnd_7879794 : Nat := 4046121780414448503436493

theorem tailTrace_7879794 : CollatzResearch.WordTrace tailWord_7879794 prefixEnd_7879794 4046121780414448503436493 := by
  unfold tailWord_7879794
  simp only [CollatzResearch.WordTrace]
  refine ⟨71849924503714893629687609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191599798676573049679166957 71849924503714893629687609)
  ·
    refine ⟨53887443377786170222265707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71849924503714893629687609 53887443377786170222265707)
    ·
      refine ⟨80831165066679255333398561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53887443377786170222265707 80831165066679255333398561)
      ·
        refine ⟨60623373800009441500048921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80831165066679255333398561 60623373800009441500048921)
        ·
          refine ⟨45467530350007081125036691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60623373800009441500048921 45467530350007081125036691)
          ·
            refine ⟨68201295525010621687555037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45467530350007081125036691 68201295525010621687555037)
            ·
              refine ⟨25575485821878983132833139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68201295525010621687555037 25575485821878983132833139)
              ·
                refine ⟨38363228732818474699249709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25575485821878983132833139 38363228732818474699249709)
                ·
                  refine ⟨14386210774806928012218641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38363228732818474699249709 14386210774806928012218641)
                  ·
                    refine ⟨10789658081105196009163981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14386210774806928012218641 10789658081105196009163981)
                    ·
                      refine ⟨4046121780414448503436493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789658081105196009163981 4046121780414448503436493)
                      ·
                        rfl

theorem cell23_7879794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_7879794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879794 prefixEnd_7879794 := by exact prefixLift 7879794
  have htrace : WordTrace (prefixWord ++ tailWord_7879794) baseStart_7879794 baseEnd_7879794 := by
    simpa [prefixWord, tailWord_7879794, baseEnd_7879794] using wordTrace_append hprefix tailTrace_7879794
  have hstable : (prefixWord ++ tailWord_7879794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879794).length < 2 ^ (prefixWord ++ tailWord_7879794).sum := by decide
  have hdescent : baseEnd_7879794 < baseStart_7879794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879811 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 1, 2, 3]
def baseStart_7879811 : Nat := 118140960795 + 7879811 * 2 ^ 59
def prefixEnd_7879811 : Nat := 4983230072969 + 3 ^ 40 * 7879811 * 2
def baseEnd_7879811 : Nat := 4046130509585574936923915

theorem tailTrace_7879811 : CollatzResearch.WordTrace tailWord_7879811 prefixEnd_7879811 4046130509585574936923915 := by
  unfold tailWord_7879811
  simp only [CollatzResearch.WordTrace]
  refine ⟨287400318055797986422119287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191600212037198657614746191 287400318055797986422119287)
  ·
    refine ⟨431100477083696979633178931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287400318055797986422119287 431100477083696979633178931)
    ·
      refine ⟨646650715625545469449768397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431100477083696979633178931 646650715625545469449768397)
      ·
        refine ⟨242494018359579551043663149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 646650715625545469449768397 242494018359579551043663149)
        ·
          refine ⟨90935256884842331641373681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242494018359579551043663149 90935256884842331641373681)
          ·
            refine ⟨68201442663631748731030261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90935256884842331641373681 68201442663631748731030261)
            ·
              refine ⟨6393885249715476443534087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68201442663631748731030261 6393885249715476443534087)
              ·
                refine ⟨9590827874573214665301131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6393885249715476443534087 9590827874573214665301131)
                ·
                  refine ⟨14386241811859821997951697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590827874573214665301131 14386241811859821997951697)
                  ·
                    refine ⟨10789681358894866498463773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14386241811859821997951697 10789681358894866498463773)
                    ·
                      refine ⟨4046130509585574936923915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789681358894866498463773 4046130509585574936923915)
                      ·
                        rfl

theorem cell23_7879811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_7879811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879811 prefixEnd_7879811 := by exact prefixLift 7879811
  have htrace : WordTrace (prefixWord ++ tailWord_7879811) baseStart_7879811 baseEnd_7879811 := by
    simpa [prefixWord, tailWord_7879811, baseEnd_7879811] using wordTrace_append hprefix tailTrace_7879811
  have hstable : (prefixWord ++ tailWord_7879811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879811).length < 2 ^ (prefixWord ++ tailWord_7879811).sum := by decide
  have hdescent : baseEnd_7879811 < baseStart_7879811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879841 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_7879841 : Nat := 118140960795 + 7879841 * 2 ^ 59
def prefixEnd_7879841 : Nat := 4983230072969 + 3 ^ 40 * 7879841 * 2
def baseEnd_7879841 : Nat := 4046145914005209819548777

theorem tailTrace_7879841 : CollatzResearch.WordTrace tailWord_7879841 prefixEnd_7879841 4046145914005209819548777 := by
  unfold tailWord_7879841
  simp only [CollatzResearch.WordTrace]
  refine ⟨287401412245689301545711377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191600941497126201030474251 287401412245689301545711377)
  ·
    refine ⟨215551059184266976159283533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287401412245689301545711377 215551059184266976159283533)
    ·
      refine ⟨80831647194100116059731325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215551059184266976159283533 80831647194100116059731325)
      ·
        refine ⟨30311867697787543522399247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80831647194100116059731325 30311867697787543522399247)
        ·
          refine ⟨45467801546681315283598871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30311867697787543522399247 45467801546681315283598871)
          ·
            refine ⟨68201702320021972925398307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45467801546681315283598871 68201702320021972925398307)
            ·
              refine ⟨102302553480032959388097461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68201702320021972925398307 102302553480032959388097461)
              ·
                refine ⟨9590864388753089942634137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102302553480032959388097461 9590864388753089942634137)
                ·
                  refine ⟨7193148291564817456975603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9590864388753089942634137 7193148291564817456975603)
                  ·
                    refine ⟨10789722437347226185463405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7193148291564817456975603 10789722437347226185463405)
                    ·
                      refine ⟨4046145914005209819548777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789722437347226185463405 4046145914005209819548777)
                      ·
                        rfl

theorem cell23_7879841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_7879841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879841 prefixEnd_7879841 := by exact prefixLift 7879841
  have htrace : WordTrace (prefixWord ++ tailWord_7879841) baseStart_7879841 baseEnd_7879841 := by
    simpa [prefixWord, tailWord_7879841, baseEnd_7879841] using wordTrace_append hprefix tailTrace_7879841
  have hstable : (prefixWord ++ tailWord_7879841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879841).length < 2 ^ (prefixWord ++ tailWord_7879841).sum := by decide
  have hdescent : baseEnd_7879841 < baseStart_7879841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879864 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 3, 4, 2]
def baseStart_7879864 : Nat := 118140960795 + 7879864 * 2 ^ 59
def prefixEnd_7879864 : Nat := 4983230072969 + 3 ^ 40 * 7879864 * 2
def baseEnd_7879864 : Nat := 4046157724060263229561171

theorem tailTrace_7879864 : CollatzResearch.WordTrace tailWord_7879864 prefixEnd_7879864 4046157724060263229561171 := by
  unfold tailWord_7879864
  simp only [CollatzResearch.WordTrace]
  refine ⟨143701125562302988236899323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191601500749737317649199097 143701125562302988236899323)
  ·
    refine ⟨215551688343454482355348985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143701125562302988236899323 215551688343454482355348985)
    ·
      refine ⟨161663766257590861766511739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215551688343454482355348985 161663766257590861766511739)
      ·
        refine ⟨242495649386386292649767609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161663766257590861766511739 242495649386386292649767609)
        ·
          refine ⟨181871737039789719487325707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242495649386386292649767609 181871737039789719487325707)
          ·
            refine ⟨272807605559684579230988561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181871737039789719487325707 272807605559684579230988561)
            ·
              refine ⟨204605704169763434423241421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272807605559684579230988561 204605704169763434423241421)
              ·
                refine ⟨76727139063661287908715533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204605704169763434423241421 76727139063661287908715533)
                ·
                  refine ⟨28772677148872982965768325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76727139063661287908715533 28772677148872982965768325)
                  ·
                    refine ⟨5394876965413684306081561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28772677148872982965768325 5394876965413684306081561)
                    ·
                      refine ⟨4046157724060263229561171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394876965413684306081561 4046157724060263229561171)
                      ·
                        rfl

theorem cell23_7879864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_7879864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879864 prefixEnd_7879864 := by exact prefixLift 7879864
  have htrace : WordTrace (prefixWord ++ tailWord_7879864) baseStart_7879864 baseEnd_7879864 := by
    simpa [prefixWord, tailWord_7879864, baseEnd_7879864] using wordTrace_append hprefix tailTrace_7879864
  have hstable : (prefixWord ++ tailWord_7879864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879864).length < 2 ^ (prefixWord ++ tailWord_7879864).sum := by decide
  have hdescent : baseEnd_7879864 < baseStart_7879864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879867 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 3]
def baseStart_7879867 : Nat := 118140960795 + 7879867 * 2 ^ 59
def prefixEnd_7879867 : Nat := 4983230072969 + 3 ^ 40 * 7879867 * 2
def baseEnd_7879867 : Nat := 4046159264502226717823657

theorem tailTrace_7879867 : CollatzResearch.WordTrace tailWord_7879867 prefixEnd_7879867 4046159264502226717823657 := by
  unfold tailWord_7879867
  simp only [CollatzResearch.WordTrace]
  refine ⟨287402360543595107986157855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191601573695730071990771903 287402360543595107986157855)
  ·
    refine ⟨431103540815392661979236783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287402360543595107986157855 431103540815392661979236783)
    ·
      refine ⟨646655311223088992968855175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431103540815392661979236783 646655311223088992968855175)
      ·
        refine ⟨969982966834633489453282763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646655311223088992968855175 969982966834633489453282763)
        ·
          refine ⟨1454974450251950234179924145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969982966834633489453282763 1454974450251950234179924145)
          ·
            refine ⟨1091230837688962675634943109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454974450251950234179924145 1091230837688962675634943109)
            ·
              refine ⟨204605782066680501681551833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1091230837688962675634943109 204605782066680501681551833)
              ·
                refine ⟨153454336550010376261163875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204605782066680501681551833 153454336550010376261163875)
                ·
                  refine ⟨230181504825015564391745813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153454336550010376261163875 230181504825015564391745813)
                  ·
                    refine ⟨10789758038672604580863085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 230181504825015564391745813 10789758038672604580863085)
                    ·
                      refine ⟨4046159264502226717823657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789758038672604580863085 4046159264502226717823657)
                      ·
                        rfl

theorem cell23_7879867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 3].length) (baseStart_7879867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879867 prefixEnd_7879867 := by exact prefixLift 7879867
  have htrace : WordTrace (prefixWord ++ tailWord_7879867) baseStart_7879867 baseEnd_7879867 := by
    simpa [prefixWord, tailWord_7879867, baseEnd_7879867] using wordTrace_append hprefix tailTrace_7879867
  have hstable : (prefixWord ++ tailWord_7879867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879867).length < 2 ^ (prefixWord ++ tailWord_7879867).sum := by decide
  have hdescent : baseEnd_7879867 < baseStart_7879867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879868 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_7879868 : Nat := 118140960795 + 7879868 * 2 ^ 59
def prefixEnd_7879868 : Nat := 4983230072969 + 3 ^ 40 * 7879868 * 2
def baseEnd_7879868 : Nat := 4046159777982881213911153

theorem tailTrace_7879868 : CollatzResearch.WordTrace tailWord_7879868 prefixEnd_7879868 4046159777982881213911153 := by
  unfold tailWord_7879868
  simp only [CollatzResearch.WordTrace]
  refine ⟨143701198508295742578472129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191601598011060990104629505 143701198508295742578472129)
  ·
    refine ⟨107775898881221806933854097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143701198508295742578472129 107775898881221806933854097)
    ·
      refine ⟨80831924160916355200390573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107775898881221806933854097 80831924160916355200390573)
      ·
        refine ⟨30311971560343633200146465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80831924160916355200390573 30311971560343633200146465)
        ·
          refine ⟨22733978670257724900109849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30311971560343633200146465 22733978670257724900109849)
          ·
            refine ⟨17050484002693293675082387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22733978670257724900109849 17050484002693293675082387)
            ·
              refine ⟨25575726004039940512623581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17050484002693293675082387 25575726004039940512623581)
              ·
                refine ⟨9590897251514977692233843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25575726004039940512623581 9590897251514977692233843)
                ·
                  refine ⟨14386345877272466538350765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590897251514977692233843 14386345877272466538350765)
                  ·
                    refine ⟨5394879703977174951881537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14386345877272466538350765 5394879703977174951881537)
                    ·
                      refine ⟨4046159777982881213911153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394879703977174951881537 4046159777982881213911153)
                      ·
                        rfl

theorem cell23_7879868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_7879868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879868 prefixEnd_7879868 := by exact prefixLift 7879868
  have htrace : WordTrace (prefixWord ++ tailWord_7879868) baseStart_7879868 baseEnd_7879868 := by
    simpa [prefixWord, tailWord_7879868, baseEnd_7879868] using wordTrace_append hprefix tailTrace_7879868
  have hstable : (prefixWord ++ tailWord_7879868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879868).length < 2 ^ (prefixWord ++ tailWord_7879868).sum := by decide
  have hdescent : baseEnd_7879868 < baseStart_7879868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879892 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7879892 : Nat := 118140960795 + 7879892 * 2 ^ 59
def prefixEnd_7879892 : Nat := 4983230072969 + 3 ^ 40 * 7879892 * 2
def baseEnd_7879892 : Nat := 4046172101518589120011043

theorem tailTrace_7879892 : CollatzResearch.WordTrace tailWord_7879892 prefixEnd_7879892 4046172101518589120011043 := by
  unfold tailWord_7879892
  simp only [CollatzResearch.WordTrace]
  refine ⟨143701636184252268627908965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191602181579003024837211953 143701636184252268627908965)
  ·
    refine ⟨26944056784547300367732931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143701636184252268627908965 26944056784547300367732931)
    ·
      refine ⟨40416085176820950551599397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26944056784547300367732931 40416085176820950551599397)
      ·
        refine ⟨7578015970653928228424887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40416085176820950551599397 7578015970653928228424887)
        ·
          refine ⟨11367023955980892342637331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578015970653928228424887 11367023955980892342637331)
          ·
            refine ⟨17050535933971338513955997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367023955980892342637331 17050535933971338513955997)
            ·
              refine ⟨6393950975239251942733499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17050535933971338513955997 6393950975239251942733499)
              ·
                refine ⟨9590926462858877914100249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6393950975239251942733499 9590926462858877914100249)
                ·
                  refine ⟨7193194847144158435575187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9590926462858877914100249 7193194847144158435575187)
                  ·
                    refine ⟨10789792270716237653362781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7193194847144158435575187 10789792270716237653362781)
                    ·
                      refine ⟨4046172101518589120011043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10789792270716237653362781 4046172101518589120011043)
                      ·
                        rfl

theorem cell23_7879892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7879892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879892 prefixEnd_7879892 := by exact prefixLift 7879892
  have htrace : WordTrace (prefixWord ++ tailWord_7879892) baseStart_7879892 baseEnd_7879892 := by
    simpa [prefixWord, tailWord_7879892, baseEnd_7879892] using wordTrace_append hprefix tailTrace_7879892
  have hstable : (prefixWord ++ tailWord_7879892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879892).length < 2 ^ (prefixWord ++ tailWord_7879892).sum := by decide
  have hdescent : baseEnd_7879892 < baseStart_7879892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879927 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_7879927 : Nat := 118140960795 + 7879927 * 2 ^ 59
def prefixEnd_7879927 : Nat := 4983230072969 + 3 ^ 40 * 7879927 * 2
def baseEnd_7879927 : Nat := 4046190073341496483073381

theorem tailTrace_7879927 : CollatzResearch.WordTrace tailWord_7879927 prefixEnd_7879927 4046190073341496483073381 := by
  unfold tailWord_7879927
  simp only [CollatzResearch.WordTrace]
  refine ⟨287404548923377738233342035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191603032615585158822228023 287404548923377738233342035)
  ·
    refine ⟨431106823385066607350013053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287404548923377738233342035 431106823385066607350013053)
    ·
      refine ⟨161665058769399977756254895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431106823385066607350013053 161665058769399977756254895)
      ·
        refine ⟨242497588154099966634382343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161665058769399977756254895 242497588154099966634382343)
        ·
          refine ⟨363746382231149949951573515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242497588154099966634382343 363746382231149949951573515)
          ·
            refine ⟨545619573346724924927360273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363746382231149949951573515 545619573346724924927360273)
            ·
              refine ⟨409214680010043693695520205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545619573346724924927360273 409214680010043693695520205)
              ·
                refine ⟨153455505003766385135820077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409214680010043693695520205 153455505003766385135820077)
                ·
                  refine ⟨57545814376412394425932529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153455505003766385135820077 57545814376412394425932529)
                  ·
                    refine ⟨43159360782309295819449397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57545814376412394425932529 43159360782309295819449397)
                    ·
                      refine ⟨4046190073341496483073381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43159360782309295819449397 4046190073341496483073381)
                      ·
                        rfl

theorem cell23_7879927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_7879927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879927 prefixEnd_7879927 := by exact prefixLift 7879927
  have htrace : WordTrace (prefixWord ++ tailWord_7879927) baseStart_7879927 baseEnd_7879927 := by
    simpa [prefixWord, tailWord_7879927, baseEnd_7879927] using wordTrace_append hprefix tailTrace_7879927
  have hstable : (prefixWord ++ tailWord_7879927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879927).length < 2 ^ (prefixWord ++ tailWord_7879927).sum := by decide
  have hdescent : baseEnd_7879927 < baseStart_7879927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879938 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 7]
def baseStart_7879938 : Nat := 118140960795 + 7879938 * 2 ^ 59
def prefixEnd_7879938 : Nat := 4983230072969 + 3 ^ 40 * 7879938 * 2
def baseEnd_7879938 : Nat := 449577302403188437781759

theorem tailTrace_7879938 : CollatzResearch.WordTrace tailWord_7879938 prefixEnd_7879938 449577302403188437781759 := by
  unfold tailWord_7879938
  simp only [CollatzResearch.WordTrace]
  refine ⟨71851237531584471777998117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191603300084225258074661645 71851237531584471777998117)
  ·
    refine ⟨13472107037172088458374647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71851237531584471777998117 13472107037172088458374647)
    ·
      refine ⟨20208160555758132687561971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13472107037172088458374647 20208160555758132687561971)
      ·
        refine ⟨30312240833637199031342957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20208160555758132687561971 30312240833637199031342957)
        ·
          refine ⟨11367090312613949636753609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30312240833637199031342957 11367090312613949636753609)
          ·
            refine ⟨8525317734460462227565207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11367090312613949636753609 8525317734460462227565207)
            ·
              refine ⟨12787976601690693341347811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8525317734460462227565207 12787976601690693341347811)
              ·
                refine ⟨19181964902536040012021717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12787976601690693341347811 19181964902536040012021717)
                ·
                  refine ⟨449577302403188437781759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19181964902536040012021717 449577302403188437781759)
                  ·
                    rfl

theorem cell23_7879938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_7879938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879938 prefixEnd_7879938 := by exact prefixLift 7879938
  have htrace : WordTrace (prefixWord ++ tailWord_7879938) baseStart_7879938 baseEnd_7879938 := by
    simpa [prefixWord, tailWord_7879938, baseEnd_7879938] using wordTrace_append hprefix tailTrace_7879938
  have hstable : (prefixWord ++ tailWord_7879938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879938).length < 2 ^ (prefixWord ++ tailWord_7879938).sum := by decide
  have hdescent : baseEnd_7879938 < baseStart_7879938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879971 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 4]
def baseStart_7879971 : Nat := 118140960795 + 7879971 * 2 ^ 59
def prefixEnd_7879971 : Nat := 4983230072969 + 3 ^ 40 * 7879971 * 2
def baseEnd_7879971 : Nat := 4046212666490294310923179

theorem tailTrace_7879971 : CollatzResearch.WordTrace tailWord_7879971 prefixEnd_7879971 4046212666490294310923179 := by
  unfold tailWord_7879971
  simp only [CollatzResearch.WordTrace]
  refine ⟨287406153735218333747943767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191604102490145555831962511 287406153735218333747943767)
  ·
    refine ⟨431109230602827500621915651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287406153735218333747943767 431109230602827500621915651)
    ·
      refine ⟨646663845904241250932873477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431109230602827500621915651 646663845904241250932873477)
      ·
        refine ⟨121249471107045234549913777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 646663845904241250932873477 121249471107045234549913777)
        ·
          refine ⟨90937103330283925912435333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121249471107045234549913777 90937103330283925912435333)
          ·
            refine ⟨17050706874428236108581625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90937103330283925912435333 17050706874428236108581625)
            ·
              refine ⟨12788030155821177081436219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17050706874428236108581625 12788030155821177081436219)
              ·
                refine ⟨19182045233731765622154329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12788030155821177081436219 19182045233731765622154329)
                ·
                  refine ⟨14386533925298824216615747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19182045233731765622154329 14386533925298824216615747)
                  ·
                    refine ⟨21579800887948236324923621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14386533925298824216615747 21579800887948236324923621)
                    ·
                      refine ⟨4046212666490294310923179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21579800887948236324923621 4046212666490294310923179)
                      ·
                        rfl

theorem cell23_7879971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_7879971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879971 prefixEnd_7879971 := by exact prefixLift 7879971
  have htrace : WordTrace (prefixWord ++ tailWord_7879971) baseStart_7879971 baseEnd_7879971 := by
    simpa [prefixWord, tailWord_7879971, baseEnd_7879971] using wordTrace_append hprefix tailTrace_7879971
  have hstable : (prefixWord ++ tailWord_7879971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879971).length < 2 ^ (prefixWord ++ tailWord_7879971).sum := by decide
  have hdescent : baseEnd_7879971 < baseStart_7879971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7879988 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_7879988 : Nat := 118140960795 + 7879988 * 2 ^ 59
def prefixEnd_7879988 : Nat := 4983230072969 + 3 ^ 40 * 7879988 * 2
def baseEnd_7879988 : Nat := 4046221395661420744410601

theorem tailTrace_7879988 : CollatzResearch.WordTrace tailWord_7879988 prefixEnd_7879988 4046221395661420744410601 := by
  unfold tailWord_7879988
  simp only [CollatzResearch.WordTrace]
  refine ⟨143703386888078372825656309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191604515850771163767541745 143703386888078372825656309)
  ·
    refine ⟨13472192520757347452405279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143703386888078372825656309 13472192520757347452405279)
    ·
      refine ⟨20208288781136021178607919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13472192520757347452405279 20208288781136021178607919)
      ·
        refine ⟨30312433171704031767911879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20208288781136021178607919 30312433171704031767911879)
        ·
          refine ⟨45468649757556047651867819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30312433171704031767911879 45468649757556047651867819)
          ·
            refine ⟨68202974636334071477801729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45468649757556047651867819 68202974636334071477801729)
            ·
              refine ⟨51152230977250553608351297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68202974636334071477801729 51152230977250553608351297)
              ·
                refine ⟨38364173232937915206263473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51152230977250553608351297 38364173232937915206263473)
                ·
                  refine ⟨28773129924703436404697605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38364173232937915206263473 28773129924703436404697605)
                  ·
                    refine ⟨5394961860881894325880801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28773129924703436404697605 5394961860881894325880801)
                    ·
                      refine ⟨4046221395661420744410601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5394961860881894325880801 4046221395661420744410601)
                      ·
                        rfl

theorem cell23_7879988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_7879988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7879988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7879988 prefixEnd_7879988 := by exact prefixLift 7879988
  have htrace : WordTrace (prefixWord ++ tailWord_7879988) baseStart_7879988 baseEnd_7879988 := by
    simpa [prefixWord, tailWord_7879988, baseEnd_7879988] using wordTrace_append hprefix tailTrace_7879988
  have hstable : (prefixWord ++ tailWord_7879988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7879988).length < 2 ^ (prefixWord ++ tailWord_7879988).sum := by decide
  have hdescent : baseEnd_7879988 < baseStart_7879988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7879988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880022 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7880022 : Nat := 118140960795 + 7880022 * 2 ^ 59
def prefixEnd_7880022 : Nat := 4983230072969 + 3 ^ 40 * 7880022 * 2
def baseEnd_7880022 : Nat := 4046238854003673611385445

theorem tailTrace_7880022 : CollatzResearch.WordTrace tailWord_7880022 prefixEnd_7880022 4046238854003673611385445 := by
  unfold tailWord_7880022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17963000866127098091128145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191605342572022379638700213 17963000866127098091128145)
  ·
    refine ⟨13472250649595323568346109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17963000866127098091128145 13472250649595323568346109)
    ·
      refine ⟨5052093993598246338129791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13472250649595323568346109 5052093993598246338129791)
      ·
        refine ⟨7578140990397369507194687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5052093993598246338129791 7578140990397369507194687)
        ·
          refine ⟨11367211485596054260792031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578140990397369507194687 11367211485596054260792031)
          ·
            refine ⟨17050817228394081391188047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367211485596054260792031 17050817228394081391188047)
            ·
              refine ⟨25576225842591122086782071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17050817228394081391188047 25576225842591122086782071)
              ·
                refine ⟨38364338763886683130173107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25576225842591122086782071 38364338763886683130173107)
                ·
                  refine ⟨57546508145830024695259661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38364338763886683130173107 57546508145830024695259661)
                  ·
                    refine ⟨21579940554686259260722373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57546508145830024695259661 21579940554686259260722373)
                    ·
                      refine ⟨4046238854003673611385445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21579940554686259260722373 4046238854003673611385445)
                      ·
                        rfl

theorem cell23_7880022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7880022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880022 prefixEnd_7880022 := by exact prefixLift 7880022
  have htrace : WordTrace (prefixWord ++ tailWord_7880022) baseStart_7880022 baseEnd_7880022 := by
    simpa [prefixWord, tailWord_7880022, baseEnd_7880022] using wordTrace_append hprefix tailTrace_7880022
  have hstable : (prefixWord ++ tailWord_7880022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880022).length < 2 ^ (prefixWord ++ tailWord_7880022).sum := by decide
  have hdescent : baseEnd_7880022 < baseStart_7880022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880024 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 3, 5]
def baseStart_7880024 : Nat := 118140960795 + 7880024 * 2 ^ 59
def prefixEnd_7880024 : Nat := 4983230072969 + 3 ^ 40 * 7880024 * 2
def baseEnd_7880024 : Nat := 1348746626988327534520145

theorem tailTrace_7880024 : CollatzResearch.WordTrace tailWord_7880024 prefixEnd_7880024 1348746626988327534520145 := by
  unfold tailWord_7880024
  simp only [CollatzResearch.WordTrace]
  refine ⟨143704043402013161899811563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191605391202684215866415417 143704043402013161899811563)
  ·
    refine ⟨215556065103019742849717345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143704043402013161899811563 215556065103019742849717345)
    ·
      refine ⟨161667048827264807137288009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215556065103019742849717345 161667048827264807137288009)
      ·
        refine ⟨121250286620448605352966007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161667048827264807137288009 121250286620448605352966007)
        ·
          refine ⟨181875429930672908029449011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121250286620448605352966007 181875429930672908029449011)
          ·
            refine ⟨272813144896009362044173517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181875429930672908029449011 272813144896009362044173517)
            ·
              refine ⟨102304929336003510766565069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272813144896009362044173517 102304929336003510766565069)
              ·
                refine ⟨38364348501001316537461901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102304929336003510766565069 38364348501001316537461901)
                ·
                  refine ⟨14386630687875493701548213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38364348501001316537461901 14386630687875493701548213)
                  ·
                    refine ⟨1348746626988327534520145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14386630687875493701548213 1348746626988327534520145)
                    ·
                      rfl

theorem cell23_7880024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_7880024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880024 prefixEnd_7880024 := by exact prefixLift 7880024
  have htrace : WordTrace (prefixWord ++ tailWord_7880024) baseStart_7880024 baseEnd_7880024 := by
    simpa [prefixWord, tailWord_7880024, baseEnd_7880024] using wordTrace_append hprefix tailTrace_7880024
  have hstable : (prefixWord ++ tailWord_7880024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880024).length < 2 ^ (prefixWord ++ tailWord_7880024).sum := by decide
  have hdescent : baseEnd_7880024 < baseStart_7880024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880062 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_7880062 : Nat := 118140960795 + 7880062 * 2 ^ 59
def prefixEnd_7880062 : Nat := 4983230072969 + 3 ^ 40 * 7880062 * 2
def baseEnd_7880062 : Nat := 449584377025539272765029

theorem tailTrace_7880062 : CollatzResearch.WordTrace tailWord_7880062 prefixEnd_7880062 449584377025539272765029 := by
  unfold tailWord_7880062
  simp only [CollatzResearch.WordTrace]
  refine ⟨35926184097236082036188305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191606315185259104193004293 35926184097236082036188305)
  ·
    refine ⟨26944638072927061527141229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35926184097236082036188305 26944638072927061527141229)
    ·
      refine ⟨10104239277347648072677961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26944638072927061527141229 10104239277347648072677961)
      ·
        refine ⟨7578179458010736054508471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10104239277347648072677961 7578179458010736054508471)
        ·
          refine ⟨11367269187016104081762707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578179458010736054508471 11367269187016104081762707)
          ·
            refine ⟨17050903780524156122644061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367269187016104081762707 17050903780524156122644061)
            ·
              refine ⟨6394088917696558545991523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17050903780524156122644061 6394088917696558545991523)
              ·
                refine ⟨9591133376544837818987285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394088917696558545991523 9591133376544837818987285)
                ·
                  refine ⟨449584377025539272765029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9591133376544837818987285 449584377025539272765029)
                  ·
                    rfl

theorem cell23_7880062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_7880062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880062 prefixEnd_7880062 := by exact prefixLift 7880062
  have htrace : WordTrace (prefixWord ++ tailWord_7880062) baseStart_7880062 baseEnd_7880062 := by
    simpa [prefixWord, tailWord_7880062, baseEnd_7880062] using wordTrace_append hprefix tailTrace_7880062
  have hstable : (prefixWord ++ tailWord_7880062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880062).length < 2 ^ (prefixWord ++ tailWord_7880062).sum := by decide
  have hdescent : baseEnd_7880062 < baseStart_7880062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880071 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 1, 6]
def baseStart_7880071 : Nat := 118140960795 + 7880071 * 2 ^ 59
def prefixEnd_7880071 : Nat := 4983230072969 + 3 ^ 40 * 7880071 * 2
def baseEnd_7880071 : Nat := 1348754671518581306557573

theorem tailTrace_7880071 : CollatzResearch.WordTrace tailWord_7880071 prefixEnd_7880071 1348754671518581306557573 := by
  unfold tailWord_7880071
  simp only [CollatzResearch.WordTrace]
  refine ⟨287409801034856050826584067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191606534023237367217722711 287409801034856050826584067)
  ·
    refine ⟨431114701552284076239876101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287409801034856050826584067 431114701552284076239876101)
    ·
      refine ⟨80834006541053264294976769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431114701552284076239876101 80834006541053264294976769)
      ·
        refine ⟨60625504905789948221232577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80834006541053264294976769 60625504905789948221232577)
        ·
          refine ⟨45469128679342461165924433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60625504905789948221232577 45469128679342461165924433)
          ·
            refine ⟨34101846509506845874443325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45469128679342461165924433 34101846509506845874443325)
            ·
              refine ⟨12788192441065067202916247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34101846509506845874443325 12788192441065067202916247)
              ·
                refine ⟨19182288661597600804374371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12788192441065067202916247 19182288661597600804374371)
                ·
                  refine ⟨28773432992396401206561557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19182288661597600804374371 28773432992396401206561557)
                  ·
                    refine ⟨1348754671518581306557573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28773432992396401206561557 1348754671518581306557573)
                    ·
                      rfl

theorem cell23_7880071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_7880071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880071 prefixEnd_7880071 := by exact prefixLift 7880071
  have htrace : WordTrace (prefixWord ++ tailWord_7880071) baseStart_7880071 baseEnd_7880071 := by
    simpa [prefixWord, tailWord_7880071, baseEnd_7880071] using wordTrace_append hprefix tailTrace_7880071
  have hstable : (prefixWord ++ tailWord_7880071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880071).length < 2 ^ (prefixWord ++ tailWord_7880071).sum := by decide
  have hdescent : baseEnd_7880071 < baseStart_7880071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880098 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_7880098 : Nat := 118140960795 + 7880098 * 2 ^ 59
def prefixEnd_7880098 : Nat := 4983230072969 + 3 ^ 40 * 7880098 * 2
def baseEnd_7880098 : Nat := 4046277878533415314035095

theorem tailTrace_7880098 : CollatzResearch.WordTrace tailWord_7880098 prefixEnd_7880098 4046277878533415314035095 := by
  unfold tailWord_7880098
  simp only [CollatzResearch.WordTrace]
  refine ⟨71852696451439558609454237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191607190537172156291877965 71852696451439558609454237)
  ·
    refine ⟨26944761169289834478545339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71852696451439558609454237 26944761169289834478545339)
    ·
      refine ⟨40417141753934751717818009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26944761169289834478545339 40417141753934751717818009)
      ·
        refine ⟨30312856315451063788363507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40417141753934751717818009 30312856315451063788363507)
        ·
          refine ⟨45469284473176595682545261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30312856315451063788363507 45469284473176595682545261)
          ·
            refine ⟨17050981677441223380954473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45469284473176595682545261 17050981677441223380954473)
            ·
              refine ⟨12788236258080917535715855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17050981677441223380954473 12788236258080917535715855)
              ·
                refine ⟨19182354387121376303573783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12788236258080917535715855 19182354387121376303573783)
                ·
                  refine ⟨28773531580682064455360675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19182354387121376303573783 28773531580682064455360675)
                  ·
                    refine ⟨43160297371023096683041013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28773531580682064455360675 43160297371023096683041013)
                    ·
                      refine ⟨4046277878533415314035095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43160297371023096683041013 4046277878533415314035095)
                      ·
                        rfl

theorem cell23_7880098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_7880098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880098 prefixEnd_7880098 := by exact prefixLift 7880098
  have htrace : WordTrace (prefixWord ++ tailWord_7880098) baseStart_7880098 baseEnd_7880098 := by
    simpa [prefixWord, tailWord_7880098, baseEnd_7880098] using wordTrace_append hprefix tailTrace_7880098
  have hstable : (prefixWord ++ tailWord_7880098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880098).length < 2 ^ (prefixWord ++ tailWord_7880098).sum := by decide
  have hdescent : baseEnd_7880098 < baseStart_7880098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880132 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_7880132 : Nat := 118140960795 + 7880132 * 2 ^ 59
def prefixEnd_7880132 : Nat := 4983230072969 + 3 ^ 40 * 7880132 * 2
def baseEnd_7880132 : Nat := 4046295336875668181009939

theorem tailTrace_7880132 : CollatzResearch.WordTrace tailWord_7880132 prefixEnd_7880132 4046295336875668181009939 := by
  unfold tailWord_7880132
  simp only [CollatzResearch.WordTrace]
  refine ⟨143706012943817529122277325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191608017258423372163036433 143706012943817529122277325)
  ·
    refine ⟨53889754853931573420853997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143706012943817529122277325 53889754853931573420853997)
    ·
      refine ⟨20208658070224340032820249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53889754853931573420853997 20208658070224340032820249)
      ·
        refine ⟨15156493552668255024615187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20208658070224340032820249 15156493552668255024615187)
        ·
          refine ⟨22734740329002382536922781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15156493552668255024615187 22734740329002382536922781)
          ·
            refine ⟨8525527623375893451346043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22734740329002382536922781 8525527623375893451346043)
            ·
              refine ⟨12788291435063840177019065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8525527623375893451346043 12788291435063840177019065)
              ·
                refine ⟨9591218576297880132764299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12788291435063840177019065 9591218576297880132764299)
                ·
                  refine ⟨14386827864446820199146449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9591218576297880132764299 14386827864446820199146449)
                  ·
                    refine ⟨10790120898335115149359837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14386827864446820199146449 10790120898335115149359837)
                    ·
                      refine ⟨4046295336875668181009939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10790120898335115149359837 4046295336875668181009939)
                      ·
                        rfl

theorem cell23_7880132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_7880132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880132 prefixEnd_7880132 := by exact prefixLift 7880132
  have htrace : WordTrace (prefixWord ++ tailWord_7880132) baseStart_7880132 baseEnd_7880132 := by
    simpa [prefixWord, tailWord_7880132, baseEnd_7880132] using wordTrace_append hprefix tailTrace_7880132
  have hstable : (prefixWord ++ tailWord_7880132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880132).length < 2 ^ (prefixWord ++ tailWord_7880132).sum := by decide
  have hdescent : baseEnd_7880132 < baseStart_7880132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880144 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 1, 8]
def baseStart_7880144 : Nat := 118140960795 + 7880144 * 2 ^ 59
def prefixEnd_7880144 : Nat := 4983230072969 + 3 ^ 40 * 7880144 * 2
def baseEnd_7880144 : Nat := 1348767166214507378019961

theorem tailTrace_7880144 : CollatzResearch.WordTrace tailWord_7880144 prefixEnd_7880144 1348767166214507378019961 := by
  unfold tailWord_7880144
  simp only [CollatzResearch.WordTrace]
  refine ⟨143706231781795792146995743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191608309042394389529327657 143706231781795792146995743)
  ·
    refine ⟨215559347672693688220493615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143706231781795792146995743 215559347672693688220493615)
    ·
      refine ⟨323339021509040532330740423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215559347672693688220493615 323339021509040532330740423)
      ·
        refine ⟨485008532263560798496110635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323339021509040532330740423 485008532263560798496110635)
        ·
          refine ⟨727512798395341197744165953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485008532263560798496110635 727512798395341197744165953)
          ·
            refine ⟨545634598796505898308124465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727512798395341197744165953 545634598796505898308124465)
            ·
              refine ⟨409225949097379423731093349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545634598796505898308124465 409225949097379423731093349)
              ·
                refine ⟨76729865455758641949580003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409225949097379423731093349 76729865455758641949580003)
                ·
                  refine ⟨115094798183637962924370005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76729865455758641949580003 115094798183637962924370005)
                  ·
                    refine ⟨1348767166214507378019961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115094798183637962924370005 1348767166214507378019961)
                    ·
                      rfl

theorem cell23_7880144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_7880144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880144 prefixEnd_7880144 := by exact prefixLift 7880144
  have htrace : WordTrace (prefixWord ++ tailWord_7880144) baseStart_7880144 baseEnd_7880144 := by
    simpa [prefixWord, tailWord_7880144, baseEnd_7880144] using wordTrace_append hprefix tailTrace_7880144
  have hstable : (prefixWord ++ tailWord_7880144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880144).length < 2 ^ (prefixWord ++ tailWord_7880144).sum := by decide
  have hdescent : baseEnd_7880144 < baseStart_7880144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880168 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_7880168 : Nat := 118140960795 + 7880168 * 2 ^ 59
def prefixEnd_7880168 : Nat := 4983230072969 + 3 ^ 40 * 7880168 * 2
def baseEnd_7880168 : Nat := 4046313822179230040159773

theorem tailTrace_7880168 : CollatzResearch.WordTrace tailWord_7880168 prefixEnd_7880168 4046313822179230040159773 := by
  unfold tailWord_7880168
  simp only [CollatzResearch.WordTrace]
  refine ⟨143706669457752318196432579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191608892610336424261910105 143706669457752318196432579)
  ·
    refine ⟨215560004186628477294648869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143706669457752318196432579 215560004186628477294648869)
    ·
      refine ⟨40417500784992839492746663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215560004186628477294648869 40417500784992839492746663)
      ·
        refine ⟨60626251177489259239119995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40417500784992839492746663 60626251177489259239119995)
        ·
          refine ⟨90939376766233888858679993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60626251177489259239119995 90939376766233888858679993)
          ·
            refine ⟨68204532574675416644009995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90939376766233888858679993 68204532574675416644009995)
            ·
              refine ⟨102306798862013124966014993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68204532574675416644009995 102306798862013124966014993)
              ·
                refine ⟨76730099146509843724511245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102306798862013124966014993 76730099146509843724511245)
                ·
                  refine ⟨28773787179941191396691717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76730099146509843724511245 28773787179941191396691717)
                  ·
                    refine ⟨5395085096238973386879697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28773787179941191396691717 5395085096238973386879697)
                    ·
                      refine ⟨4046313822179230040159773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5395085096238973386879697 4046313822179230040159773)
                      ·
                        rfl

theorem cell23_7880168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_7880168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880168 prefixEnd_7880168 := by exact prefixLift 7880168
  have htrace : WordTrace (prefixWord ++ tailWord_7880168) baseStart_7880168 baseEnd_7880168 := by
    simpa [prefixWord, tailWord_7880168, baseEnd_7880168] using wordTrace_append hprefix tailTrace_7880168
  have hstable : (prefixWord ++ tailWord_7880168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880168).length < 2 ^ (prefixWord ++ tailWord_7880168).sum := by decide
  have hdescent : baseEnd_7880168 < baseStart_7880168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880178 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_7880178 : Nat := 118140960795 + 7880178 * 2 ^ 59
def prefixEnd_7880178 : Nat := 4983230072969 + 3 ^ 40 * 7880178 * 2
def baseEnd_7880178 : Nat := 1348772985661925000344909

theorem tailTrace_7880178 : CollatzResearch.WordTrace tailWord_7880178 prefixEnd_7880178 1348772985661925000344909 := by
  unfold tailWord_7880178
  simp only [CollatzResearch.WordTrace]
  refine ⟨71853425911367102025182297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191609135763645605400486125 71853425911367102025182297)
  ·
    refine ⟨53890069433525326518886723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71853425911367102025182297 53890069433525326518886723)
    ·
      refine ⟨80835104150287989778330085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53890069433525326518886723 80835104150287989778330085)
      ·
        refine ⟨15156582028178998083436891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80835104150287989778330085 15156582028178998083436891)
        ·
          refine ⟨22734873042268497125155337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15156582028178998083436891 22734873042268497125155337)
          ·
            refine ⟨17051154781701372843866503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22734873042268497125155337 17051154781701372843866503)
            ·
              refine ⟨25576732172552059265799755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17051154781701372843866503 25576732172552059265799755)
              ·
                refine ⟨38365098258828088898699633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25576732172552059265799755 38365098258828088898699633)
                ·
                  refine ⟨28773823694121066674024725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38365098258828088898699633 28773823694121066674024725)
                  ·
                    refine ⟨1348772985661925000344909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28773823694121066674024725 1348772985661925000344909)
                    ·
                      rfl

theorem cell23_7880178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_7880178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880178 prefixEnd_7880178 := by exact prefixLift 7880178
  have htrace : WordTrace (prefixWord ++ tailWord_7880178) baseStart_7880178 baseEnd_7880178 := by
    simpa [prefixWord, tailWord_7880178, baseEnd_7880178] using wordTrace_append hprefix tailTrace_7880178
  have hstable : (prefixWord ++ tailWord_7880178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880178).length < 2 ^ (prefixWord ++ tailWord_7880178).sum := by decide
  have hdescent : baseEnd_7880178 < baseStart_7880178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880201 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 3]
def baseStart_7880201 : Nat := 118140960795 + 7880201 * 2 ^ 59
def prefixEnd_7880201 : Nat := 4983230072969 + 3 ^ 40 * 7880201 * 2
def baseEnd_7880201 : Nat := 4046330767040828411047121

theorem tailTrace_7880201 : CollatzResearch.WordTrace tailWord_7880201 prefixEnd_7880201 4046330767040828411047121 := by
  unfold tailWord_7880201
  simp only [CollatzResearch.WordTrace]
  refine ⟨287414542524385083028816457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191609695016256722019210971 287414542524385083028816457)
  ·
    refine ⟨215560906893288812271612343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287414542524385083028816457 215560906893288812271612343)
    ·
      refine ⟨323341360339933218407418515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215560906893288812271612343 323341360339933218407418515)
      ·
        refine ⟨485012040509899827611127773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323341360339933218407418515 485012040509899827611127773)
        ·
          refine ⟨181879515191212435354172915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485012040509899827611127773 181879515191212435354172915)
          ·
            refine ⟨272819272786818653031259373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181879515191212435354172915 272819272786818653031259373)
            ·
              refine ⟨102307227295056994886722265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272819272786818653031259373 102307227295056994886722265)
              ·
                refine ⟨76730420471292746165041699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102307227295056994886722265 76730420471292746165041699)
                ·
                  refine ⟨115095630706939119247562549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76730420471292746165041699 115095630706939119247562549)
                  ·
                    refine ⟨10790215378775542429458989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115095630706939119247562549 10790215378775542429458989)
                    ·
                      refine ⟨4046330767040828411047121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10790215378775542429458989 4046330767040828411047121)
                      ·
                        rfl

theorem cell23_7880201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_7880201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880201 prefixEnd_7880201 := by exact prefixLift 7880201
  have htrace : WordTrace (prefixWord ++ tailWord_7880201) baseStart_7880201 baseEnd_7880201 := by
    simpa [prefixWord, tailWord_7880201, baseEnd_7880201] using wordTrace_append hprefix tailTrace_7880201
  have hstable : (prefixWord ++ tailWord_7880201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880201).length < 2 ^ (prefixWord ++ tailWord_7880201).sum := by decide
  have hdescent : baseEnd_7880201 < baseStart_7880201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880206 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_7880206 : Nat := 118140960795 + 7880206 * 2 ^ 59
def prefixEnd_7880206 : Nat := 4983230072969 + 3 ^ 40 * 7880206 * 2
def baseEnd_7880206 : Nat := 4046333334444100891484599

theorem tailTrace_7880206 : CollatzResearch.WordTrace tailWord_7880206 prefixEnd_7880206 4046333334444100891484599 := by
  unfold tailWord_7880206
  simp only [CollatzResearch.WordTrace]
  refine ⟨35926840611170871110343559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191609816592911312588498981 35926840611170871110343559)
  ·
    refine ⟨53890260916756306665515339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35926840611170871110343559 53890260916756306665515339)
    ·
      refine ⟨80835391375134459998273009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53890260916756306665515339 80835391375134459998273009)
      ·
        refine ⟨60626543531350844998704757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80835391375134459998273009 60626543531350844998704757)
        ·
          refine ⟨5683738456064141718628571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60626543531350844998704757 5683738456064141718628571)
          ·
            refine ⟨8525607684096212577942857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5683738456064141718628571 8525607684096212577942857)
            ·
              refine ⟨6394205763072159433457143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8525607684096212577942857 6394205763072159433457143)
              ·
                refine ⟨9591308644608239150185715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394205763072159433457143 9591308644608239150185715)
                ·
                  refine ⟨14386962966912358725278573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9591308644608239150185715 14386962966912358725278573)
                  ·
                    refine ⟨5395111112592134521979465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14386962966912358725278573 5395111112592134521979465)
                    ·
                      refine ⟨4046333334444100891484599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5395111112592134521979465 4046333334444100891484599)
                      ·
                        rfl

theorem cell23_7880206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_7880206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880206 prefixEnd_7880206 := by exact prefixLift 7880206
  have htrace : WordTrace (prefixWord ++ tailWord_7880206) baseStart_7880206 baseEnd_7880206 := by
    simpa [prefixWord, tailWord_7880206, baseEnd_7880206] using wordTrace_append hprefix tailTrace_7880206
  have hstable : (prefixWord ++ tailWord_7880206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880206).length < 2 ^ (prefixWord ++ tailWord_7880206).sum := by decide
  have hdescent : baseEnd_7880206 < baseStart_7880206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880238 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_7880238 : Nat := 118140960795 + 7880238 * 2 ^ 59
def prefixEnd_7880238 : Nat := 4983230072969 + 3 ^ 40 * 7880238 * 2
def baseEnd_7880238 : Nat := 1348783255275014922094817

theorem tailTrace_7880238 : CollatzResearch.WordTrace tailWord_7880238 prefixEnd_7880238 1348783255275014922094817 := by
  unfold tailWord_7880238
  simp only [CollatzResearch.WordTrace]
  refine ⟨35926986503156379793489171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191610594683500692231942245 35926986503156379793489171)
  ·
    refine ⟨53890479754734569690233757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35926986503156379793489171 53890479754734569690233757)
    ·
      refine ⟨20208929908025463633837659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53890479754734569690233757 20208929908025463633837659)
      ·
        refine ⟨30313394862038195450756489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20208929908025463633837659 30313394862038195450756489)
        ·
          refine ⟨22735046146528646588067367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30313394862038195450756489 22735046146528646588067367)
          ·
            refine ⟨34102569219792969882101051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22735046146528646588067367 34102569219792969882101051)
            ·
              refine ⟨51153853829689454823151577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34102569219792969882101051 51153853829689454823151577)
              ·
                refine ⟨38365390372267091117363683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51153853829689454823151577 38365390372267091117363683)
                ·
                  refine ⟨57548085558400636676045525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38365390372267091117363683 57548085558400636676045525)
                  ·
                    refine ⟨1348783255275014922094817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57548085558400636676045525 1348783255275014922094817)
                    ·
                      rfl

theorem cell23_7880238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_7880238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880238 prefixEnd_7880238 := by exact prefixLift 7880238
  have htrace : WordTrace (prefixWord ++ tailWord_7880238) baseStart_7880238 baseEnd_7880238 := by
    simpa [prefixWord, tailWord_7880238, baseEnd_7880238] using wordTrace_append hprefix tailTrace_7880238
  have hstable : (prefixWord ++ tailWord_7880238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880238).length < 2 ^ (prefixWord ++ tailWord_7880238).sum := by decide
  have hdescent : baseEnd_7880238 < baseStart_7880238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880365 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_7880365 : Nat := 118140960795 + 7880365 * 2 ^ 59
def prefixEnd_7880365 : Nat := 4983230072969 + 3 ^ 40 * 7880365 * 2
def baseEnd_7880365 : Nat := 4046414977868165769396367

theorem tailTrace_7880365 : CollatzResearch.WordTrace tailWord_7880365 prefixEnd_7880365 4046414977868165769396367 := by
  unfold tailWord_7880365
  simp only [CollatzResearch.WordTrace]
  refine ⟨287420524095790939037786549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191613682730527292691857699 287420524095790939037786549)
  ·
    refine ⟨26945674133980400534792489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287420524095790939037786549 26945674133980400534792489)
    ·
      refine ⟨20209255600485300401094367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26945674133980400534792489 20209255600485300401094367)
      ·
        refine ⟨30313883400727950601641551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20209255600485300401094367 30313883400727950601641551)
        ·
          refine ⟨45470825101091925902462327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30313883400727950601641551 45470825101091925902462327)
          ·
            refine ⟨68206237651637888853693491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45470825101091925902462327 68206237651637888853693491)
            ·
              refine ⟨102309356477456833280540237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68206237651637888853693491 102309356477456833280540237)
              ·
                refine ⟨38366008679046312480202589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102309356477456833280540237 38366008679046312480202589)
                ·
                  refine ⟨14387253254642367180075971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38366008679046312480202589 14387253254642367180075971)
                  ·
                    refine ⟨21580879881963550770113957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14387253254642367180075971 21580879881963550770113957)
                    ·
                      refine ⟨4046414977868165769396367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21580879881963550770113957 4046414977868165769396367)
                      ·
                        rfl

theorem cell23_7880365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_7880365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880365 prefixEnd_7880365 := by exact prefixLift 7880365
  have htrace : WordTrace (prefixWord ++ tailWord_7880365) baseStart_7880365 baseEnd_7880365 := by
    simpa [prefixWord, tailWord_7880365, baseEnd_7880365] using wordTrace_append hprefix tailTrace_7880365
  have hstable : (prefixWord ++ tailWord_7880365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880365).length < 2 ^ (prefixWord ++ tailWord_7880365).sum := by decide
  have hdescent : baseEnd_7880365 < baseStart_7880365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880382 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_7880382 : Nat := 118140960795 + 7880382 * 2 ^ 59
def prefixEnd_7880382 : Nat := 4983230072969 + 3 ^ 40 * 7880382 * 2
def baseEnd_7880382 : Nat := 4046423707039292202883789

theorem tailTrace_7880382 : CollatzResearch.WordTrace tailWord_7880382 prefixEnd_7880382 4046423707039292202883789 := by
  unfold tailWord_7880382
  simp only [CollatzResearch.WordTrace]
  refine ⟨35927643017091168867644425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191614096091152900627436933 35927643017091168867644425)
  ·
    refine ⟨26945732262818376650733319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35927643017091168867644425 26945732262818376650733319)
    ·
      refine ⟨40418598394227564976099979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26945732262818376650733319 40418598394227564976099979)
      ·
        refine ⟨60627897591341347464149969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40418598394227564976099979 60627897591341347464149969)
        ·
          refine ⟨45470923193506010598112477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60627897591341347464149969 45470923193506010598112477)
          ·
            refine ⟨17051596197564753974292179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45470923193506010598112477 17051596197564753974292179)
            ·
              refine ⟨25577394296347130961438269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17051596197564753974292179 25577394296347130961438269)
              ·
                refine ⟨9591522861130174110539351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25577394296347130961438269 9591522861130174110539351)
                ·
                  refine ⟨14387284291695261165809027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9591522861130174110539351 14387284291695261165809027)
                  ·
                    refine ⟨21580926437542891748713541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14387284291695261165809027 21580926437542891748713541)
                    ·
                      refine ⟨4046423707039292202883789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21580926437542891748713541 4046423707039292202883789)
                      ·
                        rfl

theorem cell23_7880382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_7880382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880382 prefixEnd_7880382 := by exact prefixLift 7880382
  have htrace : WordTrace (prefixWord ++ tailWord_7880382) baseStart_7880382 baseEnd_7880382 := by
    simpa [prefixWord, tailWord_7880382, baseEnd_7880382] using wordTrace_append hprefix tailTrace_7880382
  have hstable : (prefixWord ++ tailWord_7880382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880382).length < 2 ^ (prefixWord ++ tailWord_7880382).sum := by decide
  have hdescent : baseEnd_7880382 < baseStart_7880382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880388 : List Nat := [2, 3, 3, 1, 1, 1, 12]
def baseStart_7880388 : Nat := 118140960795 + 7880388 * 2 ^ 59
def prefixEnd_7880388 : Nat := 4983230072969 + 3 ^ 40 * 7880388 * 2
def baseEnd_7880388 : Nat := 49955886270657026906281

theorem tailTrace_7880388 : CollatzResearch.WordTrace tailWord_7880388 prefixEnd_7880388 49955886270657026906281 := by
  unfold tailWord_7880388
  simp only [CollatzResearch.WordTrace]
  refine ⟨143710681487353806982936909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191614241983138409310582545 143710681487353806982936909)
  ·
    refine ⟨53891505557757677618601341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143710681487353806982936909 53891505557757677618601341)
    ·
      refine ⟨20209314584159129106975503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53891505557757677618601341 20209314584159129106975503)
      ·
        refine ⟨30313971876238693660463255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20209314584159129106975503 30313971876238693660463255)
        ·
          refine ⟨45470957814358040490694883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30313971876238693660463255 45470957814358040490694883)
          ·
            refine ⟨68206436721537060736042325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45470957814358040490694883 68206436721537060736042325)
            ·
              refine ⟨49955886270657026906281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 68206436721537060736042325 49955886270657026906281)
              ·
                rfl

theorem cell23_7880388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 12].length) (baseStart_7880388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880388 prefixEnd_7880388 := by exact prefixLift 7880388
  have htrace : WordTrace (prefixWord ++ tailWord_7880388) baseStart_7880388 baseEnd_7880388 := by
    simpa [prefixWord, tailWord_7880388, baseEnd_7880388] using wordTrace_append hprefix tailTrace_7880388
  have hstable : (prefixWord ++ tailWord_7880388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880388).length < 2 ^ (prefixWord ++ tailWord_7880388).sum := by decide
  have hdescent : baseEnd_7880388 < baseStart_7880388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880412 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_7880412 : Nat := 118140960795 + 7880412 * 2 ^ 59
def prefixEnd_7880412 : Nat := 4983230072969 + 3 ^ 40 * 7880412 * 2
def baseEnd_7880412 : Nat := 4046439111458927085508651

theorem tailTrace_7880412 : CollatzResearch.WordTrace tailWord_7880412 prefixEnd_7880412 4046439111458927085508651 := by
  unfold tailWord_7880412
  simp only [CollatzResearch.WordTrace]
  refine ⟨143711119163310333032373745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191614825551080444043164993 143711119163310333032373745)
  ·
    refine ⟨107783339372482749774280309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143711119163310333032373745 107783339372482749774280309)
    ·
      refine ⟨10104688066170257791338779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107783339372482749774280309 10104688066170257791338779)
      ·
        refine ⟨15157032099255386687008169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104688066170257791338779 15157032099255386687008169)
        ·
          refine ⟨11367774074441540015256127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15157032099255386687008169 11367774074441540015256127)
          ·
            refine ⟨17051661111662310022884191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367774074441540015256127 17051661111662310022884191)
            ·
              refine ⟨25577491667493465034326287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17051661111662310022884191 25577491667493465034326287)
              ·
                refine ⟨38366237501240197551489431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25577491667493465034326287 38366237501240197551489431)
                ·
                  refine ⟨57549356251860296327234147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38366237501240197551489431 57549356251860296327234147)
                  ·
                    refine ⟨86324034377790444490851221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57549356251860296327234147 86324034377790444490851221)
                    ·
                      refine ⟨4046439111458927085508651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86324034377790444490851221 4046439111458927085508651)
                      ·
                        rfl

theorem cell23_7880412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_7880412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880412 prefixEnd_7880412 := by exact prefixLift 7880412
  have htrace : WordTrace (prefixWord ++ tailWord_7880412) baseStart_7880412 baseEnd_7880412 := by
    simpa [prefixWord, tailWord_7880412, baseEnd_7880412] using wordTrace_append hprefix tailTrace_7880412
  have hstable : (prefixWord ++ tailWord_7880412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880412).length < 2 ^ (prefixWord ++ tailWord_7880412).sum := by decide
  have hdescent : baseEnd_7880412 < baseStart_7880412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880419 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7880419 : Nat := 118140960795 + 7880419 * 2 ^ 59
def prefixEnd_7880419 : Nat := 4983230072969 + 3 ^ 40 * 7880419 * 2
def baseEnd_7880419 : Nat := 4046442705823508558121119

theorem tailTrace_7880419 : CollatzResearch.WordTrace tailWord_7880419 prefixEnd_7880419 4046442705823508558121119 := by
  unfold tailWord_7880419
  simp only [CollatzResearch.WordTrace]
  refine ⟨287422493637595306260252311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191614995758396870840168207 287422493637595306260252311)
  ·
    refine ⟨431133740456392959390378467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287422493637595306260252311 431133740456392959390378467)
    ·
      refine ⟨646700610684589439085567701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431133740456392959390378467 646700610684589439085567701)
      ·
        refine ⟨15157045562920064978567993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 646700610684589439085567701 15157045562920064978567993)
        ·
          refine ⟨11367784172190048733925995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15157045562920064978567993 11367784172190048733925995)
          ·
            refine ⟨17051676258285073100888993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367784172190048733925995 17051676258285073100888993)
            ·
              refine ⟨12788757193713804825666745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17051676258285073100888993 12788757193713804825666745)
              ·
                refine ⟨9591567895285353619250059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12788757193713804825666745 9591567895285353619250059)
                ·
                  refine ⟨14387351842928030428875089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9591567895285353619250059 14387351842928030428875089)
                  ·
                    refine ⟨10790513882196022821656317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14387351842928030428875089 10790513882196022821656317)
                    ·
                      refine ⟨4046442705823508558121119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10790513882196022821656317 4046442705823508558121119)
                      ·
                        rfl

theorem cell23_7880419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7880419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880419 prefixEnd_7880419 := by exact prefixLift 7880419
  have htrace : WordTrace (prefixWord ++ tailWord_7880419) baseStart_7880419 baseEnd_7880419 := by
    simpa [prefixWord, tailWord_7880419, baseEnd_7880419] using wordTrace_append hprefix tailTrace_7880419
  have hstable : (prefixWord ++ tailWord_7880419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880419).length < 2 ^ (prefixWord ++ tailWord_7880419).sum := by decide
  have hdescent : baseEnd_7880419 < baseStart_7880419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880428 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_7880428 : Nat := 118140960795 + 7880428 * 2 ^ 59
def prefixEnd_7880428 : Nat := 4983230072969 + 3 ^ 40 * 7880428 * 2
def baseEnd_7880428 : Nat := 4046447327149399022908577

theorem tailTrace_7880428 : CollatzResearch.WordTrace tailWord_7880428 prefixEnd_7880428 4046447327149399022908577 := by
  unfold tailWord_7880428
  simp only [CollatzResearch.WordTrace]
  refine ⟨143711410947281350398664969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191615214596375133864886625 143711410947281350398664969)
  ·
    refine ⟨107783558210461012798998727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143711410947281350398664969 107783558210461012798998727)
    ·
      refine ⟨161675337315691519198498091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107783558210461012798998727 161675337315691519198498091)
      ·
        refine ⟨242513005973537278797747137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161675337315691519198498091 242513005973537278797747137)
        ·
          refine ⟨181884754480152959098310353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242513005973537278797747137 181884754480152959098310353)
          ·
            refine ⟨136413565860114719323732765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181884754480152959098310353 136413565860114719323732765)
            ·
              refine ⟨51155087197543019746399787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136413565860114719323732765 51155087197543019746399787)
              ·
                refine ⟨76732630796314529619599681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51155087197543019746399787 76732630796314529619599681)
                ·
                  refine ⟨57549473097235897214699761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76732630796314529619599681 57549473097235897214699761)
                  ·
                    refine ⟨43162104822926922911024821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57549473097235897214699761 43162104822926922911024821)
                    ·
                      refine ⟨4046447327149399022908577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43162104822926922911024821 4046447327149399022908577)
                      ·
                        rfl

theorem cell23_7880428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_7880428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880428 prefixEnd_7880428 := by exact prefixLift 7880428
  have htrace : WordTrace (prefixWord ++ tailWord_7880428) baseStart_7880428 baseEnd_7880428 := by
    simpa [prefixWord, tailWord_7880428, baseEnd_7880428] using wordTrace_append hprefix tailTrace_7880428
  have hstable : (prefixWord ++ tailWord_7880428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880428).length < 2 ^ (prefixWord ++ tailWord_7880428).sum := by decide
  have hdescent : baseEnd_7880428 < baseStart_7880428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880436 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7880436 : Nat := 118140960795 + 7880436 * 2 ^ 59
def prefixEnd_7880436 : Nat := 4983230072969 + 3 ^ 40 * 7880436 * 2
def baseEnd_7880436 : Nat := 4046451434994634991608541

theorem tailTrace_7880436 : CollatzResearch.WordTrace tailWord_7880436 prefixEnd_7880436 4046451434994634991608541 := by
  unfold tailWord_7880436
  simp only [CollatzResearch.WordTrace]
  refine ⟨143711556839266859081810581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191615409119022478775747441 143711556839266859081810581)
  ·
    refine ⟨6736479226840634019459871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143711556839266859081810581 6736479226840634019459871)
    ·
      refine ⟨10104718840260951029189807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6736479226840634019459871 10104718840260951029189807)
      ·
        refine ⟨15157078260391426543784711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104718840260951029189807 15157078260391426543784711)
        ·
          refine ⟨22735617390587139815677067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15157078260391426543784711 22735617390587139815677067)
          ·
            refine ⟨34103426085880709723515601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22735617390587139815677067 34103426085880709723515601)
            ·
              refine ⟨25577569564410532292636701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34103426085880709723515601 25577569564410532292636701)
              ·
                refine ⟨9591588586653949609738763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25577569564410532292636701 9591588586653949609738763)
                ·
                  refine ⟨14387382879980924414608145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9591588586653949609738763 14387382879980924414608145)
                  ·
                    refine ⟨10790537159985693310956109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14387382879980924414608145 10790537159985693310956109)
                    ·
                      refine ⟨4046451434994634991608541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10790537159985693310956109 4046451434994634991608541)
                      ·
                        rfl

theorem cell23_7880436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7880436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880436 prefixEnd_7880436 := by exact prefixLift 7880436
  have htrace : WordTrace (prefixWord ++ tailWord_7880436) baseStart_7880436 baseEnd_7880436 := by
    simpa [prefixWord, tailWord_7880436, baseEnd_7880436] using wordTrace_append hprefix tailTrace_7880436
  have hstable : (prefixWord ++ tailWord_7880436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880436).length < 2 ^ (prefixWord ++ tailWord_7880436).sum := by decide
  have hdescent : baseEnd_7880436 < baseStart_7880436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880466 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7880466 : Nat := 118140960795 + 7880466 * 2 ^ 59
def prefixEnd_7880466 : Nat := 4983230072969 + 3 ^ 40 * 7880466 * 2
def baseEnd_7880466 : Nat := 4046466839414269874233403

theorem tailTrace_7880466 : CollatzResearch.WordTrace tailWord_7880466 prefixEnd_7880466 4046466839414269874233403 := by
  unfold tailWord_7880466
  simp only [CollatzResearch.WordTrace]
  refine ⟨71856051967106258321803313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191616138578950022191475501 71856051967106258321803313)
  ·
    refine ⟨53892038975329693741352485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71856051967106258321803313 53892038975329693741352485)
    ·
      refine ⟨10104757307874317576503591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53892038975329693741352485 10104757307874317576503591)
      ·
        refine ⟨15157135961811476364755387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104757307874317576503591 15157135961811476364755387)
        ·
          refine ⟨22735703942717214547133081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15157135961811476364755387 22735703942717214547133081)
          ·
            refine ⟨17051777957037910910349811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22735703942717214547133081 17051777957037910910349811)
            ·
              refine ⟨25577666935556866365524717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17051777957037910910349811 25577666935556866365524717)
              ·
                refine ⟨9591625100833824887071769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25577666935556866365524717 9591625100833824887071769)
                ·
                  refine ⟨7193718825625368665303827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9591625100833824887071769 7193718825625368665303827)
                  ·
                    refine ⟨10790578238438052997955741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7193718825625368665303827 10790578238438052997955741)
                    ·
                      refine ⟨4046466839414269874233403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10790578238438052997955741 4046466839414269874233403)
                      ·
                        rfl

theorem cell23_7880466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7880466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880466 prefixEnd_7880466 := by exact prefixLift 7880466
  have htrace : WordTrace (prefixWord ++ tailWord_7880466) baseStart_7880466 baseEnd_7880466 := by
    simpa [prefixWord, tailWord_7880466, baseEnd_7880466] using wordTrace_append hprefix tailTrace_7880466
  have hstable : (prefixWord ++ tailWord_7880466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880466).length < 2 ^ (prefixWord ++ tailWord_7880466).sum := by decide
  have hdescent : baseEnd_7880466 < baseStart_7880466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880506 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2]
def baseStart_7880506 : Nat := 118140960795 + 7880506 * 2 ^ 59
def prefixEnd_7880506 : Nat := 4983230072969 + 3 ^ 40 * 7880506 * 2
def baseEnd_7880506 : Nat := 4046487378640449717733219

theorem tailTrace_7880506 : CollatzResearch.WordTrace tailWord_7880506 prefixEnd_7880506 4046487378640449717733219 := by
  unfold tailWord_7880506
  simp only [CollatzResearch.WordTrace]
  refine ⟨71856416697070030029667343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191617111192186746745779581 71856416697070030029667343)
  ·
    refine ⟨107784625045605045044501015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71856416697070030029667343 107784625045605045044501015)
    ·
      refine ⟨161676937568407567566751523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107784625045605045044501015 161676937568407567566751523)
      ·
        refine ⟨242515406352611351350127285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161676937568407567566751523 242515406352611351350127285)
        ·
          refine ⟨22735819345557314189074433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242515406352611351350127285 22735819345557314189074433)
          ·
            refine ⟨17051864509167985641805825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22735819345557314189074433 17051864509167985641805825)
            ·
              refine ⟨12788898381875989231354369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17051864509167985641805825 12788898381875989231354369)
              ·
                refine ⟨9591673786406991923515777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12788898381875989231354369 9591673786406991923515777)
                ·
                  refine ⟨7193755339805243942636833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9591673786406991923515777 7193755339805243942636833)
                  ·
                    refine ⟨5395316504853932956977625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7193755339805243942636833 5395316504853932956977625)
                    ·
                      refine ⟨4046487378640449717733219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5395316504853932956977625 4046487378640449717733219)
                      ·
                        rfl

theorem cell23_7880506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_7880506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880506 prefixEnd_7880506 := by exact prefixLift 7880506
  have htrace : WordTrace (prefixWord ++ tailWord_7880506) baseStart_7880506 baseEnd_7880506 := by
    simpa [prefixWord, tailWord_7880506, baseEnd_7880506] using wordTrace_append hprefix tailTrace_7880506
  have hstable : (prefixWord ++ tailWord_7880506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880506).length < 2 ^ (prefixWord ++ tailWord_7880506).sum := by decide
  have hdescent : baseEnd_7880506 < baseStart_7880506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880545 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_7880545 : Nat := 118140960795 + 7880545 * 2 ^ 59
def prefixEnd_7880545 : Nat := 4983230072969 + 3 ^ 40 * 7880545 * 2
def baseEnd_7880545 : Nat := 4046507404385975065145539

theorem tailTrace_7880545 : CollatzResearch.WordTrace tailWord_7880545 prefixEnd_7880545 4046507404385975065145539 := by
  unfold tailWord_7880545
  simp only [CollatzResearch.WordTrace]
  refine ⟨287427089235138829779339089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191618059490092553186226059 287427089235138829779339089)
  ·
    refine ⟨215570316926354122334504317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287427089235138829779339089 215570316926354122334504317)
    ·
      refine ⟨80838868847382795875439119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215570316926354122334504317 80838868847382795875439119)
      ·
        refine ⟨121258303271074193813158679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80838868847382795875439119 121258303271074193813158679)
        ·
          refine ⟨181887454906611290719738019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121258303271074193813158679 181887454906611290719738019)
          ·
            refine ⟨272831182359916936079607029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181887454906611290719738019 272831182359916936079607029)
            ·
              refine ⟨25577923346242212757463159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272831182359916936079607029 25577923346242212757463159)
              ·
                refine ⟨38366885019363319136194739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25577923346242212757463159 38366885019363319136194739)
                ·
                  refine ⟨57550327529044978704292109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38366885019363319136194739 57550327529044978704292109)
                  ·
                    refine ⟨21581372823391867014109541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57550327529044978704292109 21581372823391867014109541)
                    ·
                      refine ⟨4046507404385975065145539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21581372823391867014109541 4046507404385975065145539)
                      ·
                        rfl

theorem cell23_7880545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_7880545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880545 prefixEnd_7880545 := by exact prefixLift 7880545
  have htrace : WordTrace (prefixWord ++ tailWord_7880545) baseStart_7880545 baseEnd_7880545 := by
    simpa [prefixWord, tailWord_7880545, baseEnd_7880545] using wordTrace_append hprefix tailTrace_7880545
  have hstable : (prefixWord ++ tailWord_7880545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880545).length < 2 ^ (prefixWord ++ tailWord_7880545).sum := by decide
  have hdescent : baseEnd_7880545 < baseStart_7880545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880555 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 7, 4]
def baseStart_7880555 : Nat := 118140960795 + 7880555 * 2 ^ 59
def prefixEnd_7880555 : Nat := 4983230072969 + 3 ^ 40 * 7880555 * 2
def baseEnd_7880555 : Nat := 1348837513064173342006831

theorem tailTrace_7880555 : CollatzResearch.WordTrace tailWord_7880555 prefixEnd_7880555 1348837513064173342006831 := by
  unfold tailWord_7880555
  simp only [CollatzResearch.WordTrace]
  refine ⟨287427453965102601487203119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191618302643401734324802079 287427453965102601487203119)
  ·
    refine ⟨431141180947653902230804679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287427453965102601487203119 431141180947653902230804679)
    ·
      refine ⟨646711771421480853346207019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431141180947653902230804679 646711771421480853346207019)
      ·
        refine ⟨970067657132221280019310529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646711771421480853346207019 970067657132221280019310529)
        ·
          refine ⟨727550742849165960014482897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970067657132221280019310529 727550742849165960014482897)
          ·
            refine ⟨545663057136874470010862173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727550742849165960014482897 545663057136874470010862173)
            ·
              refine ⟨204623646426327926254073315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545663057136874470010862173 204623646426327926254073315)
              ·
                refine ⟨306935469639491889381109973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204623646426327926254073315 306935469639491889381109973)
                ·
                  refine ⟨7193800069675591157369765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 306935469639491889381109973 7193800069675591157369765)
                  ·
                    refine ⟨1348837513064173342006831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7193800069675591157369765 1348837513064173342006831)
                    ·
                      rfl

theorem cell23_7880555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 4].length) (baseStart_7880555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880555 prefixEnd_7880555 := by exact prefixLift 7880555
  have htrace : WordTrace (prefixWord ++ tailWord_7880555) baseStart_7880555 baseEnd_7880555 := by
    simpa [prefixWord, tailWord_7880555, baseEnd_7880555] using wordTrace_append hprefix tailTrace_7880555
  have hstable : (prefixWord ++ tailWord_7880555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880555).length < 2 ^ (prefixWord ++ tailWord_7880555).sum := by decide
  have hdescent : baseEnd_7880555 < baseStart_7880555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880666 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_7880666 : Nat := 118140960795 + 7880666 * 2 ^ 59
def prefixEnd_7880666 : Nat := 4983230072969 + 3 ^ 40 * 7880666 * 2
def baseEnd_7880666 : Nat := 1348856511848389697244161

theorem tailTrace_7880666 : CollatzResearch.WordTrace tailWord_7880666 prefixEnd_7880666 1348856511848389697244161 := by
  unfold tailWord_7880666
  simp only [CollatzResearch.WordTrace]
  refine ⟨71857875616925116861123463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191621001645133644962995901 71857875616925116861123463)
  ·
    refine ⟨107786813425387675291685195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71857875616925116861123463 107786813425387675291685195)
    ·
      refine ⟨161680220138081512937527793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107786813425387675291685195 161680220138081512937527793)
      ·
        refine ⟨121260165103561134703145845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161680220138081512937527793 121260165103561134703145845)
        ·
          refine ⟨11368140478458856378419923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121260165103561134703145845 11368140478458856378419923)
          ·
            refine ⟨17052210717688284567629885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11368140478458856378419923 17052210717688284567629885)
            ·
              refine ⟨6394579019133106712861207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17052210717688284567629885 6394579019133106712861207)
              ·
                refine ⟨9591868528699660069291811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394579019133106712861207 9591868528699660069291811)
                ·
                  refine ⟨14387802793049490103937717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9591868528699660069291811 14387802793049490103937717)
                  ·
                    refine ⟨1348856511848389697244161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14387802793049490103937717 1348856511848389697244161)
                    ·
                      rfl

theorem cell23_7880666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_7880666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880666 prefixEnd_7880666 := by exact prefixLift 7880666
  have htrace : WordTrace (prefixWord ++ tailWord_7880666) baseStart_7880666 baseEnd_7880666 := by
    simpa [prefixWord, tailWord_7880666, baseEnd_7880666] using wordTrace_append hprefix tailTrace_7880666
  have hstable : (prefixWord ++ tailWord_7880666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880666).length < 2 ^ (prefixWord ++ tailWord_7880666).sum := by decide
  have hdescent : baseEnd_7880666 < baseStart_7880666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880675 : List Nat := [1, 1, 1, 6, 1, 13]
def baseStart_7880675 : Nat := 118140960795 + 7880675 * 2 ^ 59
def prefixEnd_7880675 : Nat := 4983230072969 + 3 ^ 40 * 7880675 * 2
def baseEnd_7880675 : Nat := 16652568546794483771687

theorem tailTrace_7880675 : CollatzResearch.WordTrace tailWord_7880675 prefixEnd_7880675 16652568546794483771687 := by
  unfold tailWord_7880675
  simp only [CollatzResearch.WordTrace]
  refine ⟨287431830724667861981571479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191621220483111907987714319 287431830724667861981571479)
  ·
    refine ⟨431147746087001792972357219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287431830724667861981571479 431147746087001792972357219)
    ·
      refine ⟨646721619130502689458535829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431147746087001792972357219 646721619130502689458535829)
      ·
        refine ⟨30315075896742313568368867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 646721619130502689458535829 30315075896742313568368867)
        ·
          refine ⟨45472613845113470352553301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30315075896742313568368867 45472613845113470352553301)
          ·
            refine ⟨16652568546794483771687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 45472613845113470352553301 16652568546794483771687)
            ·
              rfl

theorem cell23_7880675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 13].length) (baseStart_7880675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880675 prefixEnd_7880675 := by exact prefixLift 7880675
  have htrace : WordTrace (prefixWord ++ tailWord_7880675) baseStart_7880675 baseEnd_7880675 := by
    simpa [prefixWord, tailWord_7880675, baseEnd_7880675] using wordTrace_append hprefix tailTrace_7880675
  have hstable : (prefixWord ++ tailWord_7880675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880675).length < 2 ^ (prefixWord ++ tailWord_7880675).sum := by decide
  have hdescent : baseEnd_7880675 < baseStart_7880675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880682 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_7880682 : Nat := 118140960795 + 7880682 * 2 ^ 59
def prefixEnd_7880682 : Nat := 4983230072969 + 3 ^ 40 * 7880682 * 2
def baseEnd_7880682 : Nat := 4046577751235641029132409

theorem tailTrace_7880682 : CollatzResearch.WordTrace tailWord_7880682 prefixEnd_7880682 4046577751235641029132409 := by
  unfold tailWord_7880682
  simp only [CollatzResearch.WordTrace]
  refine ⟨71858021508910625544269075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191621390690428334784717533 71858021508910625544269075)
  ·
    refine ⟨107787032263365938316403613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71858021508910625544269075 107787032263365938316403613)
    ·
      refine ⟨40420137098762226868651355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107787032263365938316403613 40420137098762226868651355)
      ·
        refine ⟨60630205648143340302977033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40420137098762226868651355 60630205648143340302977033)
        ·
          refine ⟨45472654236107505227232775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60630205648143340302977033 45472654236107505227232775)
          ·
            refine ⟨68208981354161257840849163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45472654236107505227232775 68208981354161257840849163)
            ·
              refine ⟨102313472031241886761273745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68208981354161257840849163 102313472031241886761273745)
              ·
                refine ⟨76735104023431415070955309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102313472031241886761273745 76735104023431415070955309)
                ·
                  refine ⟨28775664008786780651608241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76735104023431415070955309 28775664008786780651608241)
                  ·
                    refine ⟨21581748006590085488706181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28775664008786780651608241 21581748006590085488706181)
                    ·
                      refine ⟨4046577751235641029132409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21581748006590085488706181 4046577751235641029132409)
                      ·
                        rfl

theorem cell23_7880682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_7880682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880682 prefixEnd_7880682 := by exact prefixLift 7880682
  have htrace : WordTrace (prefixWord ++ tailWord_7880682) baseStart_7880682 baseEnd_7880682 := by
    simpa [prefixWord, tailWord_7880682, baseEnd_7880682] using wordTrace_append hprefix tailTrace_7880682
  have hstable : (prefixWord ++ tailWord_7880682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880682).length < 2 ^ (prefixWord ++ tailWord_7880682).sum := by decide
  have hdescent : baseEnd_7880682 < baseStart_7880682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880717 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_7880717 : Nat := 118140960795 + 7880717 * 2 ^ 59
def prefixEnd_7880717 : Nat := 4983230072969 + 3 ^ 40 * 7880717 * 2
def baseEnd_7880717 : Nat := 1348865241019516130731583

theorem tailTrace_7880717 : CollatzResearch.WordTrace tailWord_7880717 prefixEnd_7880717 1348865241019516130731583 := by
  unfold tailWord_7880717
  simp only [CollatzResearch.WordTrace]
  refine ⟨287433362590515703154600405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191622241727010468769733603 287433362590515703154600405)
  ·
    refine ⟨6736719435715211792685947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 287433362590515703154600405 6736719435715211792685947)
    ·
      refine ⟨10105079153572817689028921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6736719435715211792685947 10105079153572817689028921)
      ·
        refine ⟨7578809365179613266771691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10105079153572817689028921 7578809365179613266771691)
        ·
          refine ⟨11368214047769419900157537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578809365179613266771691 11368214047769419900157537)
          ·
            refine ⟨8526160535827064925118153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11368214047769419900157537 8526160535827064925118153)
            ·
              refine ⟨6394620401870298693838615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8526160535827064925118153 6394620401870298693838615)
              ·
                refine ⟨9591930602805448040757923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394620401870298693838615 9591930602805448040757923)
                ·
                  refine ⟨14387895904208172061136885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9591930602805448040757923 14387895904208172061136885)
                  ·
                    refine ⟨1348865241019516130731583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14387895904208172061136885 1348865241019516130731583)
                    ·
                      rfl

theorem cell23_7880717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_7880717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880717 prefixEnd_7880717 := by exact prefixLift 7880717
  have htrace : WordTrace (prefixWord ++ tailWord_7880717) baseStart_7880717 baseEnd_7880717 := by
    simpa [prefixWord, tailWord_7880717, baseEnd_7880717] using wordTrace_append hprefix tailTrace_7880717
  have hstable : (prefixWord ++ tailWord_7880717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880717).length < 2 ^ (prefixWord ++ tailWord_7880717).sum := by decide
  have hdescent : baseEnd_7880717 < baseStart_7880717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880752 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 2, 6]
def baseStart_7880752 : Nat := 118140960795 + 7880752 * 2 ^ 59
def prefixEnd_7880752 : Nat := 4983230072969 + 3 ^ 40 * 7880752 * 2
def baseEnd_7880752 : Nat := 1348871231627151918419029

theorem tailTrace_7880752 : CollatzResearch.WordTrace tailWord_7880752 prefixEnd_7880752 1348871231627151918419029 := by
  unfold tailWord_7880752
  simp only [CollatzResearch.WordTrace]
  refine ⟨143717319572694452066062255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191623092763592602754749673 143717319572694452066062255)
  ·
    refine ⟨215575979359041678099093383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143717319572694452066062255 215575979359041678099093383)
    ·
      refine ⟨323363969038562517148640075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215575979359041678099093383 323363969038562517148640075)
      ·
        refine ⟨485045953557843775722960113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323363969038562517148640075 485045953557843775722960113)
        ·
          refine ⟨363784465168382831792220085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485045953557843775722960113 363784465168382831792220085)
          ·
            refine ⟨34104793609535890480520633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 363784465168382831792220085 34104793609535890480520633)
            ·
              refine ⟨25578595207151917860390475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34104793609535890480520633 25578595207151917860390475)
              ·
                refine ⟨38367892810727876790585713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25578595207151917860390475 38367892810727876790585713)
                ·
                  refine ⟨28775919608045907592939285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38367892810727876790585713 28775919608045907592939285)
                  ·
                    refine ⟨1348871231627151918419029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28775919608045907592939285 1348871231627151918419029)
                    ·
                      rfl

theorem cell23_7880752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_7880752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880752 prefixEnd_7880752 := by exact prefixLift 7880752
  have htrace : WordTrace (prefixWord ++ tailWord_7880752) baseStart_7880752 baseEnd_7880752 := by
    simpa [prefixWord, tailWord_7880752, baseEnd_7880752] using wordTrace_append hprefix tailTrace_7880752
  have hstable : (prefixWord ++ tailWord_7880752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880752).length < 2 ^ (prefixWord ++ tailWord_7880752).sum := by decide
  have hdescent : baseEnd_7880752 < baseStart_7880752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880753 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 2, 1, 3]
def baseStart_7880753 : Nat := 118140960795 + 7880753 * 2 ^ 59
def prefixEnd_7880753 : Nat := 4983230072969 + 3 ^ 40 * 7880753 * 2
def baseEnd_7880753 : Nat := 4046614208362110251344583

theorem tailTrace_7880753 : CollatzResearch.WordTrace tailWord_7880753 prefixEnd_7880753 4046614208362110251344583 := by
  unfold tailWord_7880753
  simp only [CollatzResearch.WordTrace]
  refine ⟨287434675618385281302910913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191623117078923520868607275 287434675618385281302910913)
  ·
    refine ⟨215576006713788960977183185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287434675618385281302910913 215576006713788960977183185)
    ·
      refine ⟨161682005035341720732887389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215576006713788960977183185 161682005035341720732887389)
      ·
        refine ⟨60630751888253145274832771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161682005035341720732887389 60630751888253145274832771)
        ·
          refine ⟨90946127832379717912249157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60630751888253145274832771 90946127832379717912249157)
          ·
            refine ⟨17052398968571197108546717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90946127832379717912249157 17052398968571197108546717)
            ·
              refine ⟨6394649613214198915705019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17052398968571197108546717 6394649613214198915705019)
              ·
                refine ⟨9591974419821298373557529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394649613214198915705019 9591974419821298373557529)
                ·
                  refine ⟨7193980814865973780168147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9591974419821298373557529 7193980814865973780168147)
                  ·
                    refine ⟨10790971222298960670252221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7193980814865973780168147 10790971222298960670252221)
                    ·
                      refine ⟨4046614208362110251344583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10790971222298960670252221 4046614208362110251344583)
                      ·
                        rfl

theorem cell23_7880753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_7880753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880753 prefixEnd_7880753 := by exact prefixLift 7880753
  have htrace : WordTrace (prefixWord ++ tailWord_7880753) baseStart_7880753 baseEnd_7880753 := by
    simpa [prefixWord, tailWord_7880753, baseEnd_7880753] using wordTrace_append hprefix tailTrace_7880753
  have hstable : (prefixWord ++ tailWord_7880753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880753).length < 2 ^ (prefixWord ++ tailWord_7880753).sum := by decide
  have hdescent : baseEnd_7880753 < baseStart_7880753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880762 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_7880762 : Nat := 118140960795 + 7880762 * 2 ^ 59
def prefixEnd_7880762 : Nat := 4983230072969 + 3 ^ 40 * 7880762 * 2
def baseEnd_7880762 : Nat := 4046618829688000716132041

theorem tailTrace_7880762 : CollatzResearch.WordTrace tailWord_7880762 prefixEnd_7880762 4046618829688000716132041 := by
  unfold tailWord_7880762
  simp only [CollatzResearch.WordTrace]
  refine ⟨71858750968838168959997135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191623335916901783893325693 71858750968838168959997135)
  ·
    refine ⟨107788126453257253439995703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71858750968838168959997135 107788126453257253439995703)
    ·
      refine ⟨161682189679885880159993555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107788126453257253439995703 161682189679885880159993555)
      ·
        refine ⟨242523284519828820239990333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161682189679885880159993555 242523284519828820239990333)
        ·
          refine ⟨90946231694935807589996375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242523284519828820239990333 90946231694935807589996375)
          ·
            refine ⟨136419347542403711384994563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90946231694935807589996375 136419347542403711384994563)
            ·
              refine ⟨204629021313605567077491845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136419347542403711384994563 204629021313605567077491845)
              ·
                refine ⟨38367941496301043827029721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204629021313605567077491845 38367941496301043827029721)
                ·
                  refine ⟨28775956122225782870272291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38367941496301043827029721 28775956122225782870272291)
                  ·
                    refine ⟨43163934183338674305408437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28775956122225782870272291 43163934183338674305408437)
                    ·
                      refine ⟨4046618829688000716132041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43163934183338674305408437 4046618829688000716132041)
                      ·
                        rfl

theorem cell23_7880762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_7880762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880762 prefixEnd_7880762 := by exact prefixLift 7880762
  have htrace : WordTrace (prefixWord ++ tailWord_7880762) baseStart_7880762 baseEnd_7880762 := by
    simpa [prefixWord, tailWord_7880762, baseEnd_7880762] using wordTrace_append hprefix tailTrace_7880762
  have hstable : (prefixWord ++ tailWord_7880762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880762).length < 2 ^ (prefixWord ++ tailWord_7880762).sum := by decide
  have hdescent : baseEnd_7880762 < baseStart_7880762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880810 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_7880810 : Nat := 118140960795 + 7880810 * 2 ^ 59
def prefixEnd_7880810 : Nat := 4983230072969 + 3 ^ 40 * 7880810 * 2
def baseEnd_7880810 : Nat := 4046643476759416528331821

theorem tailTrace_7880810 : CollatzResearch.WordTrace tailWord_7880810 prefixEnd_7880810 4046643476759416528331821 := by
  unfold tailWord_7880810
  simp only [CollatzResearch.WordTrace]
  refine ⟨71859188644794695009433971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191624503052785853358490589 71859188644794695009433971)
  ·
    refine ⟨107788782967192042514150957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71859188644794695009433971 107788782967192042514150957)
    ·
      refine ⟨40420793612697015942806609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107788782967192042514150957 40420793612697015942806609)
      ·
        refine ⟨30315595209522761957104957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40420793612697015942806609 30315595209522761957104957)
        ·
          refine ⟨11368348203571035733914359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30315595209522761957104957 11368348203571035733914359)
          ·
            refine ⟨17052522305356553600871539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11368348203571035733914359 17052522305356553600871539)
            ·
              refine ⟨25578783458034830401307309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17052522305356553600871539 25578783458034830401307309)
              ·
                refine ⟨9592043796763061400490241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25578783458034830401307309 9592043796763061400490241)
                ·
                  refine ⟨7194032847572296050367681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9592043796763061400490241 7194032847572296050367681)
                  ·
                    refine ⟨5395524635679222037775761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7194032847572296050367681 5395524635679222037775761)
                    ·
                      refine ⟨4046643476759416528331821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5395524635679222037775761 4046643476759416528331821)
                      ·
                        rfl

theorem cell23_7880810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_7880810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880810 prefixEnd_7880810 := by exact prefixLift 7880810
  have htrace : WordTrace (prefixWord ++ tailWord_7880810) baseStart_7880810 baseEnd_7880810 := by
    simpa [prefixWord, tailWord_7880810, baseEnd_7880810] using wordTrace_append hprefix tailTrace_7880810
  have hstable : (prefixWord ++ tailWord_7880810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880810).length < 2 ^ (prefixWord ++ tailWord_7880810).sum := by decide
  have hdescent : baseEnd_7880810 < baseStart_7880810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880829 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_7880829 : Nat := 118140960795 + 7880829 * 2 ^ 59
def prefixEnd_7880829 : Nat := 4983230072969 + 3 ^ 40 * 7880829 * 2
def baseEnd_7880829 : Nat := 1348884410963950651331411

theorem tailTrace_7880829 : CollatzResearch.WordTrace tailWord_7880829 prefixEnd_7880829 1348884410963950651331411 := by
  unfold tailWord_7880829
  simp only [CollatzResearch.WordTrace]
  refine ⟨287437447566109946282677541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191624965044073297521785027 287437447566109946282677541)
  ·
    refine ⟨53894521418645614928002039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287437447566109946282677541 53894521418645614928002039)
    ·
      refine ⟨80841782127968422392003059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53894521418645614928002039 80841782127968422392003059)
      ·
        refine ⟨121262673191952633588004589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80841782127968422392003059 121262673191952633588004589)
        ·
          refine ⟨45473502446982237595501721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121262673191952633588004589 45473502446982237595501721)
          ·
            refine ⟨34105126835236678196626291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45473502446982237595501721 34105126835236678196626291)
            ·
              refine ⟨51157690252855017294939437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34105126835236678196626291 51157690252855017294939437)
              ·
                refine ⟨19184133844820631485602289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51157690252855017294939437 19184133844820631485602289)
                ·
                  refine ⟨14388100383615473614201717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19184133844820631485602289 14388100383615473614201717)
                  ·
                    refine ⟨1348884410963950651331411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14388100383615473614201717 1348884410963950651331411)
                    ·
                      rfl

theorem cell23_7880829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_7880829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880829 prefixEnd_7880829 := by exact prefixLift 7880829
  have htrace : WordTrace (prefixWord ++ tailWord_7880829) baseStart_7880829 baseEnd_7880829 := by
    simpa [prefixWord, tailWord_7880829, baseEnd_7880829] using wordTrace_append hprefix tailTrace_7880829
  have hstable : (prefixWord ++ tailWord_7880829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880829).length < 2 ^ (prefixWord ++ tailWord_7880829).sum := by decide
  have hdescent : baseEnd_7880829 < baseStart_7880829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880849 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 5, 6, 2]
def baseStart_7880849 : Nat := 118140960795 + 7880849 * 2 ^ 59
def prefixEnd_7880849 : Nat := 4983230072969 + 3 ^ 40 * 7880849 * 2
def baseEnd_7880849 : Nat := 4046663502504941875744141

theorem tailTrace_7880849 : CollatzResearch.WordTrace tailWord_7880849 prefixEnd_7880849 4046663502504941875744141 := by
  unfold tailWord_7880849
  simp only [CollatzResearch.WordTrace]
  refine ⟨287438177026037489698405601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191625451350691659798937067 287438177026037489698405601)
  ·
    refine ⟨215578632769528117273804201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287438177026037489698405601 215578632769528117273804201)
    ·
      refine ⟨161683974577146087955353151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215578632769528117273804201 161683974577146087955353151)
      ·
        refine ⟨242525961865719131933029727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161683974577146087955353151 242525961865719131933029727)
        ·
          refine ⟨363788942798578697899544591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242525961865719131933029727 363788942798578697899544591)
          ·
            refine ⟨545683414197868046849316887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363788942798578697899544591 545683414197868046849316887)
            ·
              refine ⟨818525121296802070273975331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545683414197868046849316887 818525121296802070273975331)
              ·
                refine ⟨1227787681945203105410962997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818525121296802070273975331 1227787681945203105410962997)
                ·
                  refine ⟨115105095182362791132277781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1227787681945203105410962997 115105095182362791132277781)
                  ·
                    refine ⟨5395551336673255834325521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115105095182362791132277781 5395551336673255834325521)
                    ·
                      refine ⟨4046663502504941875744141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5395551336673255834325521 4046663502504941875744141)
                      ·
                        rfl

theorem cell23_7880849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_7880849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880849 prefixEnd_7880849 := by exact prefixLift 7880849
  have htrace : WordTrace (prefixWord ++ tailWord_7880849) baseStart_7880849 baseEnd_7880849 := by
    simpa [prefixWord, tailWord_7880849, baseEnd_7880849] using wordTrace_append hprefix tailTrace_7880849
  have hstable : (prefixWord ++ tailWord_7880849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880849).length < 2 ^ (prefixWord ++ tailWord_7880849).sum := by decide
  have hdescent : baseEnd_7880849 < baseStart_7880849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880869 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_7880869 : Nat := 118140960795 + 7880869 * 2 ^ 59
def prefixEnd_7880869 : Nat := 4983230072969 + 3 ^ 40 * 7880869 * 2
def baseEnd_7880869 : Nat := 4046673772118031797494049

theorem tailTrace_7880869 : CollatzResearch.WordTrace tailWord_7880869 prefixEnd_7880869 4046673772118031797494049 := by
  unfold tailWord_7880869
  simp only [CollatzResearch.WordTrace]
  refine ⟨287438906485965033114133661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191625937657310022076089107 287438906485965033114133661)
  ·
    refine ⟨107789589932236887417800123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287438906485965033114133661 107789589932236887417800123)
    ·
      refine ⟨161684384898355331126700185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107789589932236887417800123 161684384898355331126700185)
      ·
        refine ⟨121263288673766498345025139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161684384898355331126700185 121263288673766498345025139)
        ·
          refine ⟨181894933010649747517537709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121263288673766498345025139 181894933010649747517537709)
          ·
            refine ⟨68210599878993655319076641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181894933010649747517537709 68210599878993655319076641)
            ·
              refine ⟨51157949909245241489307481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68210599878993655319076641 51157949909245241489307481)
              ·
                refine ⟨38368462431933931116980611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51157949909245241489307481 38368462431933931116980611)
                ·
                  refine ⟨57552693647900896675470917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38368462431933931116980611 57552693647900896675470917)
                  ·
                    refine ⟨10791130058981418126650797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57552693647900896675470917 10791130058981418126650797)
                    ·
                      refine ⟨4046673772118031797494049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10791130058981418126650797 4046673772118031797494049)
                      ·
                        rfl

theorem cell23_7880869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_7880869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880869 prefixEnd_7880869 := by exact prefixLift 7880869
  have htrace : WordTrace (prefixWord ++ tailWord_7880869) baseStart_7880869 baseEnd_7880869 := by
    simpa [prefixWord, tailWord_7880869, baseEnd_7880869] using wordTrace_append hprefix tailTrace_7880869
  have hstable : (prefixWord ++ tailWord_7880869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880869).length < 2 ^ (prefixWord ++ tailWord_7880869).sum := by decide
  have hdescent : baseEnd_7880869 < baseStart_7880869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880933 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 3]
def baseStart_7880933 : Nat := 118140960795 + 7880933 * 2 ^ 59
def prefixEnd_7880933 : Nat := 4983230072969 + 3 ^ 40 * 7880933 * 2
def baseEnd_7880933 : Nat := 4046706634879919547093755

theorem tailTrace_7880933 : CollatzResearch.WordTrace tailWord_7880933 prefixEnd_7880933 4046706634879919547093755 := by
  unfold tailWord_7880933
  simp only [CollatzResearch.WordTrace]
  refine ⟨287441240757733172044463453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191627493838488781362975635 287441240757733172044463453)
  ·
    refine ⟨107790465284149939516673795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287441240757733172044463453 107790465284149939516673795)
    ·
      refine ⟨161685697926224909275010693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107790465284149939516673795 161685697926224909275010693)
      ·
        refine ⟨30316068361167170489064505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161685697926224909275010693 30316068361167170489064505)
        ·
          refine ⟨22737051270875377866798379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30316068361167170489064505 22737051270875377866798379)
          ·
            refine ⟨34105576906313066800197569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22737051270875377866798379 34105576906313066800197569)
            ·
              refine ⟨25579182679734800100148177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34105576906313066800197569 25579182679734800100148177)
              ·
                refine ⟨19184387009801100075111133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25579182679734800100148177 19184387009801100075111133)
                ·
                  refine ⟨7194145128675412528166675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19184387009801100075111133 7194145128675412528166675)
                  ·
                    refine ⟨10791217693013118792250013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7194145128675412528166675 10791217693013118792250013)
                    ·
                      refine ⟨4046706634879919547093755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10791217693013118792250013 4046706634879919547093755)
                      ·
                        rfl

theorem cell23_7880933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_7880933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880933 prefixEnd_7880933 := by exact prefixLift 7880933
  have htrace : WordTrace (prefixWord ++ tailWord_7880933) baseStart_7880933 baseEnd_7880933 := by
    simpa [prefixWord, tailWord_7880933, baseEnd_7880933] using wordTrace_append hprefix tailTrace_7880933
  have hstable : (prefixWord ++ tailWord_7880933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880933).length < 2 ^ (prefixWord ++ tailWord_7880933).sum := by decide
  have hdescent : baseEnd_7880933 < baseStart_7880933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880936 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 1, 5]
def baseStart_7880936 : Nat := 118140960795 + 7880936 * 2 ^ 59
def prefixEnd_7880936 : Nat := 4983230072969 + 3 ^ 40 * 7880936 * 2
def baseEnd_7880936 : Nat := 1348902725107294345118747

theorem tailTrace_7880936 : CollatzResearch.WordTrace tailWord_7880936 prefixEnd_7880936 1348902725107294345118747 := by
  unfold tailWord_7880936
  simp only [CollatzResearch.WordTrace]
  refine ⟨143720675088361151778411331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191627566784481535704548441 143720675088361151778411331)
  ·
    refine ⟨215581012632541727667616997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143720675088361151778411331 215581012632541727667616997)
    ·
      refine ⟨40421439868601573937678187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215581012632541727667616997 40421439868601573937678187)
      ·
        refine ⟨60632159802902360906517281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40421439868601573937678187 60632159802902360906517281)
        ·
          refine ⟨45474119852176770679887961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60632159802902360906517281 45474119852176770679887961)
          ·
            refine ⟨34105589889132578009915971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45474119852176770679887961 34105589889132578009915971)
            ·
              refine ⟨51158384833698867014873957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34105589889132578009915971 51158384833698867014873957)
              ·
                refine ⟨9592197156318537565288867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51158384833698867014873957 9592197156318537565288867)
                ·
                  refine ⟨14388295734477806347933301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9592197156318537565288867 14388295734477806347933301)
                  ·
                    refine ⟨1348902725107294345118747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14388295734477806347933301 1348902725107294345118747)
                    ·
                      rfl

theorem cell23_7880936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_7880936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880936 prefixEnd_7880936 := by exact prefixLift 7880936
  have htrace : WordTrace (prefixWord ++ tailWord_7880936) baseStart_7880936 baseEnd_7880936 := by
    simpa [prefixWord, tailWord_7880936, baseEnd_7880936] using wordTrace_append hprefix tailTrace_7880936
  have hstable : (prefixWord ++ tailWord_7880936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880936).length < 2 ^ (prefixWord ++ tailWord_7880936).sum := by decide
  have hdescent : baseEnd_7880936 < baseStart_7880936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880967 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7880967 : Nat := 118140960795 + 7880967 * 2 ^ 59
def prefixEnd_7880967 : Nat := 4983230072969 + 3 ^ 40 * 7880967 * 2
def baseEnd_7880967 : Nat := 4046724093222172414068599

theorem tailTrace_7880967 : CollatzResearch.WordTrace tailWord_7880967 prefixEnd_7880967 4046724093222172414068599 := by
  unfold tailWord_7880967
  simp only [CollatzResearch.WordTrace]
  refine ⟨287442480839609995851201155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191628320559739997234134103 287442480839609995851201155)
  ·
    refine ⟨431163721259414993776801733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287442480839609995851201155 431163721259414993776801733)
    ·
      refine ⟨80843197736140311333150325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431163721259414993776801733 80843197736140311333150325)
      ·
        refine ⟨7579049787763154187482843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80843197736140311333150325 7579049787763154187482843)
        ·
          refine ⟨11368574681644731281224265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7579049787763154187482843 11368574681644731281224265)
          ·
            refine ⟨8526431011233548460918199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11368574681644731281224265 8526431011233548460918199)
            ·
              refine ⟨12789646516850322691377299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8526431011233548460918199 12789646516850322691377299)
              ·
                refine ⟨19184469775275484037065949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12789646516850322691377299 19184469775275484037065949)
                ·
                  refine ⟨7194176165728306513899731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19184469775275484037065949 7194176165728306513899731)
                  ·
                    refine ⟨10791264248592459770849597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7194176165728306513899731 10791264248592459770849597)
                    ·
                      refine ⟨4046724093222172414068599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10791264248592459770849597 4046724093222172414068599)
                      ·
                        rfl

theorem cell23_7880967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7880967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880967 prefixEnd_7880967 := by exact prefixLift 7880967
  have htrace : WordTrace (prefixWord ++ tailWord_7880967) baseStart_7880967 baseEnd_7880967 := by
    simpa [prefixWord, tailWord_7880967, baseEnd_7880967] using wordTrace_append hprefix tailTrace_7880967
  have hstable : (prefixWord ++ tailWord_7880967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880967).length < 2 ^ (prefixWord ++ tailWord_7880967).sum := by decide
  have hdescent : baseEnd_7880967 < baseStart_7880967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880969 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_7880969 : Nat := 118140960795 + 7880969 * 2 ^ 59
def prefixEnd_7880969 : Nat := 4983230072969 + 3 ^ 40 * 7880969 * 2
def baseEnd_7880969 : Nat := 4046725120183481406243589

theorem tailTrace_7880969 : CollatzResearch.WordTrace tailWord_7880969 prefixEnd_7880969 4046725120183481406243589 := by
  unfold tailWord_7880969
  simp only [CollatzResearch.WordTrace]
  refine ⟨287442553785602750192773961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191628369190401833461849307 287442553785602750192773961)
  ·
    refine ⟨215581915339202062644580471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287442553785602750192773961 215581915339202062644580471)
    ·
      refine ⟨323372873008803093966870707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215581915339202062644580471 323372873008803093966870707)
      ·
        refine ⟨485059309513204640950306061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323372873008803093966870707 485059309513204640950306061)
        ·
          refine ⟨181897241067451740356364773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485059309513204640950306061 181897241067451740356364773)
          ·
            refine ⟨34105732700147201316818395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181897241067451740356364773 34105732700147201316818395)
            ·
              refine ⟨51158599050220801975227593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34105732700147201316818395 51158599050220801975227593)
              ·
                refine ⟨38368949287665601481420695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51158599050220801975227593 38368949287665601481420695)
                ·
                  refine ⟨57553423931498402222131043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38368949287665601481420695 57553423931498402222131043)
                  ·
                    refine ⟨86330135897247603333196565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57553423931498402222131043 86330135897247603333196565)
                    ·
                      refine ⟨4046725120183481406243589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86330135897247603333196565 4046725120183481406243589)
                      ·
                        rfl

theorem cell23_7880969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_7880969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880969 prefixEnd_7880969 := by exact prefixLift 7880969
  have htrace : WordTrace (prefixWord ++ tailWord_7880969) baseStart_7880969 baseEnd_7880969 := by
    simpa [prefixWord, tailWord_7880969, baseEnd_7880969] using wordTrace_append hprefix tailTrace_7880969
  have hstable : (prefixWord ++ tailWord_7880969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880969).length < 2 ^ (prefixWord ++ tailWord_7880969).sum := by decide
  have hdescent : baseEnd_7880969 < baseStart_7880969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880983 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 2, 4]
def baseStart_7880983 : Nat := 118140960795 + 7880983 * 2 ^ 59
def prefixEnd_7880983 : Nat := 4983230072969 + 3 ^ 40 * 7880983 * 2
def baseEnd_7880983 : Nat := 1348910769637548117156175

theorem tailTrace_7880983 : CollatzResearch.WordTrace tailWord_7880983 prefixEnd_7880983 1348910769637548117156175 := by
  unfold tailWord_7880983
  simp only [CollatzResearch.WordTrace]
  refine ⟨287443064407552030583783603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191628709605034687055855735 287443064407552030583783603)
  ·
    refine ⟨431164596611328045875675405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287443064407552030583783603 431164596611328045875675405)
    ·
      refine ⟨161686723729248017203378277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431164596611328045875675405 161686723729248017203378277)
      ·
        refine ⟨30316260699234003225633427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161686723729248017203378277 30316260699234003225633427)
        ·
          refine ⟨45474391048851004838450141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30316260699234003225633427 45474391048851004838450141)
          ·
            refine ⟨17052896643319126814418803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45474391048851004838450141 17052896643319126814418803)
            ·
              refine ⟨25579344964978690221628205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17052896643319126814418803 25579344964978690221628205)
              ·
                refine ⟨9592254361867008833110577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25579344964978690221628205 9592254361867008833110577)
                ·
                  refine ⟨7194190771400256624832933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9592254361867008833110577 7194190771400256624832933)
                  ·
                    refine ⟨1348910769637548117156175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7194190771400256624832933 1348910769637548117156175)
                    ·
                      rfl

theorem cell23_7880983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_7880983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880983 prefixEnd_7880983 := by exact prefixLift 7880983
  have htrace : WordTrace (prefixWord ++ tailWord_7880983) baseStart_7880983 baseEnd_7880983 := by
    simpa [prefixWord, tailWord_7880983, baseEnd_7880983] using wordTrace_append hprefix tailTrace_7880983
  have hstable : (prefixWord ++ tailWord_7880983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880983).length < 2 ^ (prefixWord ++ tailWord_7880983).sum := by decide
  have hdescent : baseEnd_7880983 < baseStart_7880983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880990 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7880990 : Nat := 118140960795 + 7880990 * 2 ^ 59
def prefixEnd_7880990 : Nat := 4983230072969 + 3 ^ 40 * 7880990 * 2
def baseEnd_7880990 : Nat := 4046735903277225824080993

theorem tailTrace_7880990 : CollatzResearch.WordTrace tailWord_7880990 prefixEnd_7880990 4046735903277225824080993 := by
  unfold tailWord_7880990
  simp only [CollatzResearch.WordTrace]
  refine ⟨35930414964815833847411053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191628879812351113852858949 35930414964815833847411053)
  ·
    refine ⟨13473905611805937692779145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35930414964815833847411053 13473905611805937692779145)
    ·
      refine ⟨10105429208854453269584359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13473905611805937692779145 10105429208854453269584359)
      ·
        refine ⟨15158143813281679904376539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10105429208854453269584359 15158143813281679904376539)
        ·
          refine ⟨22737215719922519856564809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15158143813281679904376539 22737215719922519856564809)
          ·
            refine ⟨17052911789941889892423607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22737215719922519856564809 17052911789941889892423607)
            ·
              refine ⟨25579367684912834838635411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17052911789941889892423607 25579367684912834838635411)
              ·
                refine ⟨38369051527369252257953117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25579367684912834838635411 38369051527369252257953117)
                ·
                  refine ⟨14388394322763469596732419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38369051527369252257953117 14388394322763469596732419)
                  ·
                    refine ⟨21582591484145204395098629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14388394322763469596732419 21582591484145204395098629)
                    ·
                      refine ⟨4046735903277225824080993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21582591484145204395098629 4046735903277225824080993)
                      ·
                        rfl

theorem cell23_7880990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7880990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880990 prefixEnd_7880990 := by exact prefixLift 7880990
  have htrace : WordTrace (prefixWord ++ tailWord_7880990) baseStart_7880990 baseEnd_7880990 := by
    simpa [prefixWord, tailWord_7880990, baseEnd_7880990] using wordTrace_append hprefix tailTrace_7880990
  have hstable : (prefixWord ++ tailWord_7880990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880990).length < 2 ^ (prefixWord ++ tailWord_7880990).sum := by decide
  have hdescent : baseEnd_7880990 < baseStart_7880990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7880993 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_7880993 : Nat := 118140960795 + 7880993 * 2 ^ 59
def prefixEnd_7880993 : Nat := 4983230072969 + 3 ^ 40 * 7880993 * 2
def baseEnd_7880993 : Nat := 4046737443719189312343479

theorem tailTrace_7880993 : CollatzResearch.WordTrace tailWord_7880993 prefixEnd_7880993 4046737443719189312343479 := by
  unfold tailWord_7880993
  simp only [CollatzResearch.WordTrace]
  refine ⟨287443429137515802291647633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191628952758343868194431755 287443429137515802291647633)
  ·
    refine ⟨215582571853136851718735725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287443429137515802291647633 215582571853136851718735725)
    ·
      refine ⟨80843464444926319394525897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215582571853136851718735725 80843464444926319394525897)
      ·
        refine ⟨60632598333694739545894423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80843464444926319394525897 60632598333694739545894423)
        ·
          refine ⟨90948897500542109318841635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60632598333694739545894423 90948897500542109318841635)
          ·
            refine ⟨136423346250813163978262453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90948897500542109318841635 136423346250813163978262453)
            ·
              refine ⟨12789688711013734122962105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136423346250813163978262453 12789688711013734122962105)
              ·
                refine ⟨9592266533260300592221579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12789688711013734122962105 9592266533260300592221579)
                ·
                  refine ⟨14388399799890450888332369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9592266533260300592221579 14388399799890450888332369)
                  ·
                    refine ⟨10791299849917838166249277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14388399799890450888332369 10791299849917838166249277)
                    ·
                      refine ⟨4046737443719189312343479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10791299849917838166249277 4046737443719189312343479)
                      ·
                        rfl

theorem cell23_7880993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_7880993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7880993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7880993 prefixEnd_7880993 := by exact prefixLift 7880993
  have htrace : WordTrace (prefixWord ++ tailWord_7880993) baseStart_7880993 baseEnd_7880993 := by
    simpa [prefixWord, tailWord_7880993, baseEnd_7880993] using wordTrace_append hprefix tailTrace_7880993
  have hstable : (prefixWord ++ tailWord_7880993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7880993).length < 2 ^ (prefixWord ++ tailWord_7880993).sum := by decide
  have hdescent : baseEnd_7880993 < baseStart_7880993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7880993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881010 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_7881010 : Nat := 118140960795 + 7881010 * 2 ^ 59
def prefixEnd_7881010 : Nat := 4983230072969 + 3 ^ 40 * 7881010 * 2
def baseEnd_7881010 : Nat := 4046746172890315745830901

theorem tailTrace_7881010 : CollatzResearch.WordTrace tailWord_7881010 prefixEnd_7881010 4046746172890315745830901 := by
  unfold tailWord_7881010
  simp only [CollatzResearch.WordTrace]
  refine ⟨71861012294613553548754121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191629366118969476130010989 71861012294613553548754121)
  ·
    refine ⟨53895759220960165161565591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71861012294613553548754121 53895759220960165161565591)
    ·
      refine ⟨80843638831440247742348387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53895759220960165161565591 80843638831440247742348387)
      ·
        refine ⟨121265458247160371613522581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80843638831440247742348387 121265458247160371613522581)
        ·
          refine ⟨5684318355335642419383871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121265458247160371613522581 5684318355335642419383871)
          ·
            refine ⟨8526477533003463629075807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684318355335642419383871 8526477533003463629075807)
            ·
              refine ⟨12789716299505195443613711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8526477533003463629075807 12789716299505195443613711)
              ·
                refine ⟨19184574449257793165420567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12789716299505195443613711 19184574449257793165420567)
                ·
                  refine ⟨28776861673886689748130851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19184574449257793165420567 28776861673886689748130851)
                  ·
                    refine ⟨43165292510830034622196277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28776861673886689748130851 43165292510830034622196277)
                    ·
                      refine ⟨4046746172890315745830901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43165292510830034622196277 4046746172890315745830901)
                      ·
                        rfl

theorem cell23_7881010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_7881010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881010 prefixEnd_7881010 := by exact prefixLift 7881010
  have htrace : WordTrace (prefixWord ++ tailWord_7881010) baseStart_7881010 baseEnd_7881010 := by
    simpa [prefixWord, tailWord_7881010, baseEnd_7881010] using wordTrace_append hprefix tailTrace_7881010
  have hstable : (prefixWord ++ tailWord_7881010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881010).length < 2 ^ (prefixWord ++ tailWord_7881010).sum := by decide
  have hdescent : baseEnd_7881010 < baseStart_7881010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881079 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_7881079 : Nat := 118140960795 + 7881079 * 2 ^ 59
def prefixEnd_7881079 : Nat := 4983230072969 + 3 ^ 40 * 7881079 * 2
def baseEnd_7881079 : Nat := 4046781603055475975868083

theorem tailTrace_7881079 : CollatzResearch.WordTrace tailWord_7881079 prefixEnd_7881079 4046781603055475975868083 := by
  unfold tailWord_7881079
  simp only [CollatzResearch.WordTrace]
  refine ⟨287446565815204238979278291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191631043876802825986185527 287446565815204238979278291)
  ·
    refine ⟨431169848722806358468917437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287446565815204238979278291 431169848722806358468917437)
    ·
      refine ⟨161688693271052384425844039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431169848722806358468917437 161688693271052384425844039)
      ·
        refine ⟨242533039906578576638766059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161688693271052384425844039 242533039906578576638766059)
        ·
          refine ⟨363799559859867864958149089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242533039906578576638766059 363799559859867864958149089)
          ·
            refine ⟨272849669894900898718611817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363799559859867864958149089 272849669894900898718611817)
            ·
              refine ⟨204637252421175674038958863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272849669894900898718611817 204637252421175674038958863)
              ·
                refine ⟨306955878631763511058438295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204637252421175674038958863 306955878631763511058438295)
                ·
                  refine ⟨460433817947645266587657443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306955878631763511058438295 460433817947645266587657443)
                  ·
                    refine ⟨690650726921467899881486165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460433817947645266587657443 690650726921467899881486165)
                    ·
                      refine ⟨4046781603055475975868083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 690650726921467899881486165 4046781603055475975868083)
                      ·
                        rfl

theorem cell23_7881079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_7881079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881079 prefixEnd_7881079 := by exact prefixLift 7881079
  have htrace : WordTrace (prefixWord ++ tailWord_7881079) baseStart_7881079 baseEnd_7881079 := by
    simpa [prefixWord, tailWord_7881079, baseEnd_7881079] using wordTrace_append hprefix tailTrace_7881079
  have hstable : (prefixWord ++ tailWord_7881079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881079).length < 2 ^ (prefixWord ++ tailWord_7881079).sum := by decide
  have hdescent : baseEnd_7881079 < baseStart_7881079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881120 : List Nat := [2, 1, 1, 4, 1, 5, 1, 3, 5]
def baseStart_7881120 : Nat := 118140960795 + 7881120 * 2 ^ 59
def prefixEnd_7881120 : Nat := 4983230072969 + 3 ^ 40 * 7881120 * 2
def baseEnd_7881120 : Nat := 449644739529145590606155

theorem tailTrace_7881120 : CollatzResearch.WordTrace tailWord_7881120 prefixEnd_7881120 449644739529145590606155 := by
  unfold tailWord_7881120
  simp only [CollatzResearch.WordTrace]
  refine ⟨143724030604027851490760407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191632040805370468654347209 143724030604027851490760407)
  ·
    refine ⟨215586045906041777236140611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143724030604027851490760407 215586045906041777236140611)
    ·
      refine ⟨323379068859062665854210917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215586045906041777236140611 323379068859062665854210917)
      ·
        refine ⟨60633575411074249847664547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323379068859062665854210917 60633575411074249847664547)
        ·
          refine ⟨90950363116611374771496821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60633575411074249847664547 90950363116611374771496821)
          ·
            refine ⟨8526596542182316384827827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90950363116611374771496821 8526596542182316384827827)
            ·
              refine ⟨12789894813273474577241741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8526596542182316384827827 12789894813273474577241741)
              ·
                refine ⟨4796210554977552966465653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12789894813273474577241741 4796210554977552966465653)
                ·
                  refine ⟨449644739529145590606155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4796210554977552966465653 449644739529145590606155)
                  ·
                    rfl

theorem cell23_7881120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 5].length) (baseStart_7881120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881120 prefixEnd_7881120 := by exact prefixLift 7881120
  have htrace : WordTrace (prefixWord ++ tailWord_7881120) baseStart_7881120 baseEnd_7881120 := by
    simpa [prefixWord, tailWord_7881120, baseEnd_7881120] using wordTrace_append hprefix tailTrace_7881120
  have hstable : (prefixWord ++ tailWord_7881120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881120).length < 2 ^ (prefixWord ++ tailWord_7881120).sum := by decide
  have hdescent : baseEnd_7881120 < baseStart_7881120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881166 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_7881166 : Nat := 118140960795 + 7881166 * 2 ^ 59
def prefixEnd_7881166 : Nat := 4983230072969 + 3 ^ 40 * 7881166 * 2
def baseEnd_7881166 : Nat := 4046826275872417135480183

theorem tailTrace_7881166 : CollatzResearch.WordTrace tailWord_7881166 prefixEnd_7881166 4046826275872417135480183 := by
  unfold tailWord_7881166
  simp only [CollatzResearch.WordTrace]
  refine ⟨35931217370736131604711919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191633159310592701891796901 35931217370736131604711919)
  ·
    refine ⟨53896826056104197407067879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35931217370736131604711919 53896826056104197407067879)
    ·
      refine ⟨80845239084156296110601819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53896826056104197407067879 80845239084156296110601819)
      ·
        refine ⟨121267858626234444165902729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80845239084156296110601819 121267858626234444165902729)
        ·
          refine ⟨90950893969675833124427047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121267858626234444165902729 90950893969675833124427047)
          ·
            refine ⟨136426340954513749686640571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90950893969675833124427047 136426340954513749686640571)
            ·
              refine ⟨204639511431770624529960857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136426340954513749686640571 204639511431770624529960857)
              ·
                refine ⟨153479633573827968397470643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204639511431770624529960857 153479633573827968397470643)
                ·
                  refine ⟨230219450360741952596205965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153479633573827968397470643 230219450360741952596205965)
                  ·
                    refine ⟨86332293885278232223577237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230219450360741952596205965 86332293885278232223577237)
                    ·
                      refine ⟨4046826275872417135480183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86332293885278232223577237 4046826275872417135480183)
                      ·
                        rfl

theorem cell23_7881166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_7881166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881166 prefixEnd_7881166 := by exact prefixLift 7881166
  have htrace : WordTrace (prefixWord ++ tailWord_7881166) baseStart_7881166 baseEnd_7881166 := by
    simpa [prefixWord, tailWord_7881166, baseEnd_7881166] using wordTrace_append hprefix tailTrace_7881166
  have hstable : (prefixWord ++ tailWord_7881166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881166).length < 2 ^ (prefixWord ++ tailWord_7881166).sum := by decide
  have hdescent : baseEnd_7881166 < baseStart_7881166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881196 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_7881196 : Nat := 118140960795 + 7881196 * 2 ^ 59
def prefixEnd_7881196 : Nat := 4983230072969 + 3 ^ 40 * 7881196 * 2
def baseEnd_7881196 : Nat := 4046841680292052018105045

theorem tailTrace_7881196 : CollatzResearch.WordTrace tailWord_7881196 prefixEnd_7881196 4046841680292052018105045 := by
  unfold tailWord_7881196
  simp only [CollatzResearch.WordTrace]
  refine ⟨143725416577890183980643721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191633888770520245307524961 143725416577890183980643721)
  ·
    refine ⟨107794062433417637985482791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143725416577890183980643721 107794062433417637985482791)
    ·
      refine ⟨161691093650126456978224187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107794062433417637985482791 161691093650126456978224187)
      ·
        refine ⟨242536640475189685467336281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161691093650126456978224187 242536640475189685467336281)
        ·
          refine ⟨181902480356392264100502211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242536640475189685467336281 181902480356392264100502211)
          ·
            refine ⟨272853720534588396150753317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181902480356392264100502211 272853720534588396150753317)
            ·
              refine ⟨51160072600235324278266247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272853720534588396150753317 51160072600235324278266247)
              ·
                refine ⟨76740108900352986417399371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51160072600235324278266247 76740108900352986417399371)
                ·
                  refine ⟨115110163350529479626099057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76740108900352986417399371 115110163350529479626099057)
                  ·
                    refine ⟨86332622512897109719574293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115110163350529479626099057 86332622512897109719574293)
                    ·
                      refine ⟨4046841680292052018105045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86332622512897109719574293 4046841680292052018105045)
                      ·
                        rfl

theorem cell23_7881196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_7881196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881196 prefixEnd_7881196 := by exact prefixLift 7881196
  have htrace : WordTrace (prefixWord ++ tailWord_7881196) baseStart_7881196 baseEnd_7881196 := by
    simpa [prefixWord, tailWord_7881196, baseEnd_7881196] using wordTrace_append hprefix tailTrace_7881196
  have hstable : (prefixWord ++ tailWord_7881196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881196).length < 2 ^ (prefixWord ++ tailWord_7881196).sum := by decide
  have hdescent : baseEnd_7881196 < baseStart_7881196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881240 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 1, 5]
def baseStart_7881240 : Nat := 118140960795 + 7881240 * 2 ^ 59
def prefixEnd_7881240 : Nat := 4983230072969 + 3 ^ 40 * 7881240 * 2
def baseEnd_7881240 : Nat := 1348954757813616615318281

theorem tailTrace_7881240 : CollatzResearch.WordTrace tailWord_7881240 prefixEnd_7881240 1348954757813616615318281 := by
  unfold tailWord_7881240
  simp only [CollatzResearch.WordTrace]
  refine ⟨143726218983810481737944587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191634958645080642317259449 143726218983810481737944587)
  ·
    refine ⟨215589328475715722606916881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143726218983810481737944587 215589328475715722606916881)
    ·
      refine ⟨161691996356786791955187661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215589328475715722606916881 161691996356786791955187661)
      ·
        refine ⟨60634498633795046983195373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161691996356786791955187661 60634498633795046983195373)
        ·
          refine ⟨22737936987673142618698265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60634498633795046983195373 22737936987673142618698265)
          ·
            refine ⟨17053452740754856964023699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22737936987673142618698265 17053452740754856964023699)
            ·
              refine ⟨25580179111132285446035549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17053452740754856964023699 25580179111132285446035549)
              ·
                refine ⟨9592567166674607042263331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25580179111132285446035549 9592567166674607042263331)
                ·
                  refine ⟨14388850750011910563394997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9592567166674607042263331 14388850750011910563394997)
                  ·
                    refine ⟨1348954757813616615318281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14388850750011910563394997 1348954757813616615318281)
                    ·
                      rfl

theorem cell23_7881240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_7881240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881240 prefixEnd_7881240 := by exact prefixLift 7881240
  have htrace : WordTrace (prefixWord ++ tailWord_7881240) baseStart_7881240 baseEnd_7881240 := by
    simpa [prefixWord, tailWord_7881240, baseEnd_7881240] using wordTrace_append hprefix tailTrace_7881240
  have hstable : (prefixWord ++ tailWord_7881240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881240).length < 2 ^ (prefixWord ++ tailWord_7881240).sum := by decide
  have hdescent : baseEnd_7881240 < baseStart_7881240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881243 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 3, 8, 2]
def baseStart_7881243 : Nat := 118140960795 + 7881243 * 2 ^ 59
def prefixEnd_7881243 : Nat := 4983230072969 + 3 ^ 40 * 7881243 * 2
def baseEnd_7881243 : Nat := 4046865813882813334217329

theorem tailTrace_7881243 : CollatzResearch.WordTrace tailWord_7881243 prefixEnd_7881243 4046865813882813334217329 := by
  unfold tailWord_7881243
  simp only [CollatzResearch.WordTrace]
  refine ⟨287452547386610094988248383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191635031591073396658832255 287452547386610094988248383)
  ·
    refine ⟨431178821079915142482372575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287452547386610094988248383 431178821079915142482372575)
    ·
      refine ⟨646768231619872713723558863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431178821079915142482372575 646768231619872713723558863)
      ·
        refine ⟨970152347429809070585338295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646768231619872713723558863 970152347429809070585338295)
        ·
          refine ⟨1455228521144713605878007443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970152347429809070585338295 1455228521144713605878007443)
          ·
            refine ⟨2182842781717070408817011165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455228521144713605878007443 2182842781717070408817011165)
            ·
              refine ⟨818566043143901403306379187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2182842781717070408817011165 818566043143901403306379187)
              ·
                refine ⟨1227849064715852104959568781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818566043143901403306379187 1227849064715852104959568781)
                ·
                  refine ⟨460443399268444539359838293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227849064715852104959568781 460443399268444539359838293)
                  ·
                    refine ⟨5395821085177084445623105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 460443399268444539359838293 5395821085177084445623105)
                    ·
                      refine ⟨4046865813882813334217329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5395821085177084445623105 4046865813882813334217329)
                      ·
                        rfl

theorem cell23_7881243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8, 2].length) (baseStart_7881243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881243 prefixEnd_7881243 := by exact prefixLift 7881243
  have htrace : WordTrace (prefixWord ++ tailWord_7881243) baseStart_7881243 baseEnd_7881243 := by
    simpa [prefixWord, tailWord_7881243, baseEnd_7881243] using wordTrace_append hprefix tailTrace_7881243
  have hstable : (prefixWord ++ tailWord_7881243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881243).length < 2 ^ (prefixWord ++ tailWord_7881243).sum := by decide
  have hdescent : baseEnd_7881243 < baseStart_7881243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881261 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 6]
def baseStart_7881261 : Nat := 118140960795 + 7881261 * 2 ^ 59
def prefixEnd_7881261 : Nat := 4983230072969 + 3 ^ 40 * 7881261 * 2
def baseEnd_7881261 : Nat := 449652784059399362643583

theorem tailTrace_7881261 : CollatzResearch.WordTrace tailWord_7881261 prefixEnd_7881261 449652784059399362643583 := by
  unfold tailWord_7881261
  simp only [CollatzResearch.WordTrace]
  refine ⟨287453203900544884062403637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191635469267029922708269091 287453203900544884062403637)
  ·
    refine ⟨26948737865676082880850341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287453203900544884062403637 26948737865676082880850341)
    ·
      refine ⟨5052888349814265540159439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26948737865676082880850341 5052888349814265540159439)
      ·
        refine ⟨7579332524721398310239159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5052888349814265540159439 7579332524721398310239159)
        ·
          refine ⟨11368998787082097465358739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7579332524721398310239159 11368998787082097465358739)
          ·
            refine ⟨17053498180623146198038109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11368998787082097465358739 17053498180623146198038109)
            ·
              refine ⟨6395061817733679824264291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17053498180623146198038109 6395061817733679824264291)
              ·
                refine ⟨9592592726600519736396437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6395061817733679824264291 9592592726600519736396437)
                ·
                  refine ⟨449652784059399362643583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9592592726600519736396437 449652784059399362643583)
                  ·
                    rfl

theorem cell23_7881261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_7881261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881261 prefixEnd_7881261 := by exact prefixLift 7881261
  have htrace : WordTrace (prefixWord ++ tailWord_7881261) baseStart_7881261 baseEnd_7881261 := by
    simpa [prefixWord, tailWord_7881261, baseEnd_7881261] using wordTrace_append hprefix tailTrace_7881261
  have hstable : (prefixWord ++ tailWord_7881261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881261).length < 2 ^ (prefixWord ++ tailWord_7881261).sum := by decide
  have hdescent : baseEnd_7881261 < baseStart_7881261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881273 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7881273 : Nat := 118140960795 + 7881273 * 2 ^ 59
def prefixEnd_7881273 : Nat := 4983230072969 + 3 ^ 40 * 7881273 * 2
def baseEnd_7881273 : Nat := 4046881218302448216842191

theorem tailTrace_7881273 : CollatzResearch.WordTrace tailWord_7881273 prefixEnd_7881273 4046881218302448216842191 := by
  unfold tailWord_7881273
  simp only [CollatzResearch.WordTrace]
  refine ⟨287453641576501410111840473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191635761051000940074560315 287453641576501410111840473)
  ·
    refine ⟨215590231182376057583880355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287453641576501410111840473 215590231182376057583880355)
    ·
      refine ⟨323385346773564086375820533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215590231182376057583880355 323385346773564086375820533)
      ·
        refine ⟨30317376260021633097733175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323385346773564086375820533 30317376260021633097733175)
        ·
          refine ⟨45476064390032449646599763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30317376260021633097733175 45476064390032449646599763)
          ·
            refine ⟨68214096585048674469899645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45476064390032449646599763 68214096585048674469899645)
            ·
              refine ⟨25580286219393252926212367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68214096585048674469899645 25580286219393252926212367)
              ·
                refine ⟨38370429329089879389318551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25580286219393252926212367 38370429329089879389318551)
                ·
                  refine ⟨57555643993634819083977827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38370429329089879389318551 57555643993634819083977827)
                  ·
                    refine ⟨86333465990452228625966741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57555643993634819083977827 86333465990452228625966741)
                    ·
                      refine ⟨4046881218302448216842191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86333465990452228625966741 4046881218302448216842191)
                      ·
                        rfl

theorem cell23_7881273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7881273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881273 prefixEnd_7881273 := by exact prefixLift 7881273
  have htrace : WordTrace (prefixWord ++ tailWord_7881273) baseStart_7881273 baseEnd_7881273 := by
    simpa [prefixWord, tailWord_7881273, baseEnd_7881273] using wordTrace_append hprefix tailTrace_7881273
  have hstable : (prefixWord ++ tailWord_7881273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881273).length < 2 ^ (prefixWord ++ tailWord_7881273).sum := by decide
  have hdescent : baseEnd_7881273 < baseStart_7881273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881277 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_7881277 : Nat := 118140960795 + 7881277 * 2 ^ 59
def prefixEnd_7881277 : Nat := 4983230072969 + 3 ^ 40 * 7881277 * 2
def baseEnd_7881277 : Nat := 4046883272225066201192173

theorem tailTrace_7881277 : CollatzResearch.WordTrace tailWord_7881277 prefixEnd_7881277 4046883272225066201192173 := by
  unfold tailWord_7881277
  simp only [CollatzResearch.WordTrace]
  refine ⟨287453787468486918794986085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191635858312324612529990723 287453787468486918794986085)
  ·
    refine ⟨53897585150341297274059891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287453787468486918794986085 53897585150341297274059891)
    ·
      refine ⟨80846377725511945911089837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53897585150341297274059891 80846377725511945911089837)
      ·
        refine ⟨30317391647066979716658689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80846377725511945911089837 30317391647066979716658689)
        ·
          refine ⟨22738043735300234787494017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30317391647066979716658689 22738043735300234787494017)
          ·
            refine ⟨17053532801475176090620513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22738043735300234787494017 17053532801475176090620513)
            ·
              refine ⟨12790149601106382067965385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17053532801475176090620513 12790149601106382067965385)
              ·
                refine ⟨9592612200829786550974039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12790149601106382067965385 9592612200829786550974039)
                ·
                  refine ⟨14388918301244679826461059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9592612200829786550974039 14388918301244679826461059)
                  ·
                    refine ⟨21583377451867019739691589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14388918301244679826461059 21583377451867019739691589)
                    ·
                      refine ⟨4046883272225066201192173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21583377451867019739691589 4046883272225066201192173)
                      ·
                        rfl

theorem cell23_7881277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_7881277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881277 prefixEnd_7881277 := by exact prefixLift 7881277
  have htrace : WordTrace (prefixWord ++ tailWord_7881277) baseStart_7881277 baseEnd_7881277 := by
    simpa [prefixWord, tailWord_7881277, baseEnd_7881277] using wordTrace_append hprefix tailTrace_7881277
  have hstable : (prefixWord ++ tailWord_7881277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881277).length < 2 ^ (prefixWord ++ tailWord_7881277).sum := by decide
  have hdescent : baseEnd_7881277 < baseStart_7881277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881280 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 3]
def baseStart_7881280 : Nat := 118140960795 + 7881280 * 2 ^ 59
def prefixEnd_7881280 : Nat := 4983230072969 + 3 ^ 40 * 7881280 * 2
def baseEnd_7881280 : Nat := 4046884812667029689454659

theorem tailTrace_7881280 : CollatzResearch.WordTrace tailWord_7881280 prefixEnd_7881280 4046884812667029689454659 := by
  unfold tailWord_7881280
  simp only [CollatzResearch.WordTrace]
  refine ⟨143726948443738025153672647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191635931258317366871563529 143726948443738025153672647)
  ·
    refine ⟨215590422665607037730508971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143726948443738025153672647 215590422665607037730508971)
    ·
      refine ⟨323385633998410556595763457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215590422665607037730508971 323385633998410556595763457)
      ·
        refine ⟨242539225498807917446822593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323385633998410556595763457 242539225498807917446822593)
        ·
          refine ⟨181904419124105938085116945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242539225498807917446822593 181904419124105938085116945)
          ·
            refine ⟨136428314343079453563837709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181904419124105938085116945 136428314343079453563837709)
            ·
              refine ⟨51160617878654795086439141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136428314343079453563837709 51160617878654795086439141)
              ·
                refine ⟨9592615852247774078707339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51160617878654795086439141 9592615852247774078707339)
                ·
                  refine ⟨14388923778371661118061009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9592615852247774078707339 14388923778371661118061009)
                  ·
                    refine ⟨10791692833778745838545757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14388923778371661118061009 10791692833778745838545757)
                    ·
                      refine ⟨4046884812667029689454659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10791692833778745838545757 4046884812667029689454659)
                      ·
                        rfl

theorem cell23_7881280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_7881280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881280 prefixEnd_7881280 := by exact prefixLift 7881280
  have htrace : WordTrace (prefixWord ++ tailWord_7881280) baseStart_7881280 baseEnd_7881280 := by
    simpa [prefixWord, tailWord_7881280, baseEnd_7881280] using wordTrace_append hprefix tailTrace_7881280
  have hstable : (prefixWord ++ tailWord_7881280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881280).length < 2 ^ (prefixWord ++ tailWord_7881280).sum := by decide
  have hdescent : baseEnd_7881280 < baseStart_7881280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881337 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 3, 3, 2]
def baseStart_7881337 : Nat := 118140960795 + 7881337 * 2 ^ 59
def prefixEnd_7881337 : Nat := 4983230072969 + 3 ^ 40 * 7881337 * 2
def baseEnd_7881337 : Nat := 4046914081064335966441897

theorem tailTrace_7881337 : CollatzResearch.WordTrace tailWord_7881337 prefixEnd_7881337 4046914081064335966441897 := by
  unfold tailWord_7881337
  simp only [CollatzResearch.WordTrace]
  refine ⟨287455975848269549042170265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191637317232179699361446843 287455975848269549042170265)
  ·
    refine ⟨215591981886202161781627699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287455975848269549042170265 215591981886202161781627699)
    ·
      refine ⟨323387972829303242672441549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215591981886202161781627699 323387972829303242672441549)
      ·
        refine ⟨121270489810988716002165581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323387972829303242672441549 121270489810988716002165581)
        ·
          refine ⟨45476433679120768500812093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121270489810988716002165581 45476433679120768500812093)
          ·
            refine ⟨17053662629670288187804535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45476433679120768500812093 17053662629670288187804535)
            ·
              refine ⟨25580493944505432281706803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17053662629670288187804535 25580493944505432281706803)
              ·
                refine ⟨38370740916758148422560205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25580493944505432281706803 38370740916758148422560205)
                ·
                  refine ⟨14389027843784305658460077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38370740916758148422560205 14389027843784305658460077)
                  ·
                    refine ⟨5395885441419114621922529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14389027843784305658460077 5395885441419114621922529)
                    ·
                      refine ⟨4046914081064335966441897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5395885441419114621922529 4046914081064335966441897)
                      ·
                        rfl

theorem cell23_7881337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_7881337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881337 prefixEnd_7881337 := by exact prefixLift 7881337
  have htrace : WordTrace (prefixWord ++ tailWord_7881337) baseStart_7881337 baseEnd_7881337 := by
    simpa [prefixWord, tailWord_7881337, baseEnd_7881337] using wordTrace_append hprefix tailTrace_7881337
  have hstable : (prefixWord ++ tailWord_7881337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881337).length < 2 ^ (prefixWord ++ tailWord_7881337).sum := by decide
  have hdescent : baseEnd_7881337 < baseStart_7881337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881363 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 4]
def baseStart_7881363 : Nat := 118140960795 + 7881363 * 2 ^ 59
def prefixEnd_7881363 : Nat := 4983230072969 + 3 ^ 40 * 7881363 * 2
def baseEnd_7881363 : Nat := 4046927431561352864716777

theorem tailTrace_7881363 : CollatzResearch.WordTrace tailWord_7881363 prefixEnd_7881363 4046927431561352864716777 := by
  unfold tailWord_7881363
  simp only [CollatzResearch.WordTrace]
  refine ⟨287456924146175355482616743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191637949430783570321744495 287456924146175355482616743)
  ·
    refine ⟨431185386219263033223925115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287456924146175355482616743 431185386219263033223925115)
    ·
      refine ⟨646778079328894549835887673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431185386219263033223925115 646778079328894549835887673)
      ·
        refine ⟨485083559496670912376915755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646778079328894549835887673 485083559496670912376915755)
        ·
          refine ⟨727625339245006368565373633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485083559496670912376915755 727625339245006368565373633)
          ·
            refine ⟨545719004433754776424030225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727625339245006368565373633 545719004433754776424030225)
            ·
              refine ⟨409289253325316082318022669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545719004433754776424030225 409289253325316082318022669)
              ·
                refine ⟨153483469996993530869258501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409289253325316082318022669 153483469996993530869258501)
                ·
                  refine ⟨28778150624436287037985969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153483469996993530869258501 28778150624436287037985969)
                  ·
                    refine ⟨21583612968327215278489477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28778150624436287037985969 21583612968327215278489477)
                    ·
                      refine ⟨4046927431561352864716777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21583612968327215278489477 4046927431561352864716777)
                      ·
                        rfl

theorem cell23_7881363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_7881363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881363 prefixEnd_7881363 := by exact prefixLift 7881363
  have htrace : WordTrace (prefixWord ++ tailWord_7881363) baseStart_7881363 baseEnd_7881363 := by
    simpa [prefixWord, tailWord_7881363, baseEnd_7881363] using wordTrace_append hprefix tailTrace_7881363
  have hstable : (prefixWord ++ tailWord_7881363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881363).length < 2 ^ (prefixWord ++ tailWord_7881363).sum := by decide
  have hdescent : baseEnd_7881363 < baseStart_7881363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881380 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_7881380 : Nat := 118140960795 + 7881380 * 2 ^ 59
def prefixEnd_7881380 : Nat := 4983230072969 + 3 ^ 40 * 7881380 * 2
def baseEnd_7881380 : Nat := 4046936160732479298204199

theorem tailTrace_7881380 : CollatzResearch.WordTrace tailWord_7881380 prefixEnd_7881380 4046936160732479298204199 := by
  unfold tailWord_7881380
  simp only [CollatzResearch.WordTrace]
  refine ⟨143728772093556883692992797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191638362791409178257323729 143728772093556883692992797)
  ·
    refine ⟨53898289535083831384872299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143728772093556883692992797 53898289535083831384872299)
    ·
      refine ⟨80847434302625747077308449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53898289535083831384872299 80847434302625747077308449)
      ·
        refine ⟨60635575726969310307981337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80847434302625747077308449 60635575726969310307981337)
        ·
          refine ⟨45476681795226982730986003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60635575726969310307981337 45476681795226982730986003)
          ·
            refine ⟨68215022692840474096479005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45476681795226982730986003 68215022692840474096479005)
            ·
              refine ⟨25580633509815177786179627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68215022692840474096479005 25580633509815177786179627)
              ·
                refine ⟨38370950264722766679269441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25580633509815177786179627 38370950264722766679269441)
                ·
                  refine ⟨28778212698542075009452081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38370950264722766679269441 28778212698542075009452081)
                  ·
                    refine ⟨21583659523906556257089061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28778212698542075009452081 21583659523906556257089061)
                    ·
                      refine ⟨4046936160732479298204199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21583659523906556257089061 4046936160732479298204199)
                      ·
                        rfl

theorem cell23_7881380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_7881380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881380 prefixEnd_7881380 := by exact prefixLift 7881380
  have htrace : WordTrace (prefixWord ++ tailWord_7881380) baseStart_7881380 baseEnd_7881380 := by
    simpa [prefixWord, tailWord_7881380, baseEnd_7881380] using wordTrace_append hprefix tailTrace_7881380
  have hstable : (prefixWord ++ tailWord_7881380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881380).length < 2 ^ (prefixWord ++ tailWord_7881380).sum := by decide
  have hdescent : baseEnd_7881380 < baseStart_7881380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881407 : List Nat := [1, 1, 2, 2, 2, 5, 2, 3, 5]
def baseStart_7881407 : Nat := 118140960795 + 7881407 * 2 ^ 59
def prefixEnd_7881407 : Nat := 4983230072969 + 3 ^ 40 * 7881407 * 2
def baseEnd_7881407 : Nat := 449661113856683410285175

theorem tailTrace_7881407 : CollatzResearch.WordTrace tailWord_7881407 prefixEnd_7881407 449661113856683410285175 := by
  unfold tailWord_7881407
  simp only [CollatzResearch.WordTrace]
  refine ⟨287458528958015950997218475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191639019305343967331478983 287458528958015950997218475)
  ·
    refine ⟨431187793437023926495827713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287458528958015950997218475 431187793437023926495827713)
    ·
      refine ⟨323390845077767944871870785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431187793437023926495827713 323390845077767944871870785)
      ·
        refine ⟨242543133808325958653903089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323390845077767944871870785 242543133808325958653903089)
        ·
          refine ⟨181907350356244468990427317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242543133808325958653903089 181907350356244468990427317)
          ·
            refine ⟨17053814095897918967852561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181907350356244468990427317 17053814095897918967852561)
            ·
              refine ⟨12790360571923439225889421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17053814095897918967852561 12790360571923439225889421)
              ·
                refine ⟨4796385214471289709708533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12790360571923439225889421 4796385214471289709708533)
                ·
                  refine ⟨449661113856683410285175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4796385214471289709708533 449661113856683410285175)
                  ·
                    rfl

theorem cell23_7881407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 5].length) (baseStart_7881407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881407 prefixEnd_7881407 := by exact prefixLift 7881407
  have htrace : WordTrace (prefixWord ++ tailWord_7881407) baseStart_7881407 baseEnd_7881407 := by
    simpa [prefixWord, tailWord_7881407, baseEnd_7881407] using wordTrace_append hprefix tailTrace_7881407
  have hstable : (prefixWord ++ tailWord_7881407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881407).length < 2 ^ (prefixWord ++ tailWord_7881407).sum := by decide
  have hdescent : baseEnd_7881407 < baseStart_7881407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881474 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_7881474 : Nat := 118140960795 + 7881474 * 2 ^ 59
def prefixEnd_7881474 : Nat := 4983230072969 + 3 ^ 40 * 7881474 * 2
def baseEnd_7881474 : Nat := 4046984427914001930428767

theorem tailTrace_7881474 : CollatzResearch.WordTrace tailWord_7881474 prefixEnd_7881474 4046984427914001930428767 := by
  unfold tailWord_7881474
  simp only [CollatzResearch.WordTrace]
  refine ⟨71865243162193305359976869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191640648432515480959938317 71865243162193305359976869)
  ·
    refine ⟨13474733092911244754995663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71865243162193305359976869 13474733092911244754995663)
    ·
      refine ⟨20212099639366867132493495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13474733092911244754995663 20212099639366867132493495)
      ·
        refine ⟨30318149459050300698740243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20212099639366867132493495 30318149459050300698740243)
        ·
          refine ⟨45477224188575451048110365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30318149459050300698740243 45477224188575451048110365)
          ·
            refine ⟨17053959070715794143041387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45477224188575451048110365 17053959070715794143041387)
            ·
              refine ⟨25580938606073691214562081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17053959070715794143041387 25580938606073691214562081)
              ·
                refine ⟨19185703954555268410921561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25580938606073691214562081 19185703954555268410921561)
                ·
                  refine ⟨14389277965916451308191171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19185703954555268410921561 14389277965916451308191171)
                  ·
                    refine ⟨21583916948874676962286757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14389277965916451308191171 21583916948874676962286757)
                    ·
                      refine ⟨4046984427914001930428767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21583916948874676962286757 4046984427914001930428767)
                      ·
                        rfl

theorem cell23_7881474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_7881474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881474 prefixEnd_7881474 := by exact prefixLift 7881474
  have htrace : WordTrace (prefixWord ++ tailWord_7881474) baseStart_7881474 baseEnd_7881474 := by
    simpa [prefixWord, tailWord_7881474, baseEnd_7881474] using wordTrace_append hprefix tailTrace_7881474
  have hstable : (prefixWord ++ tailWord_7881474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881474).length < 2 ^ (prefixWord ++ tailWord_7881474).sum := by decide
  have hdescent : baseEnd_7881474 < baseStart_7881474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881480 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 8]
def baseStart_7881480 : Nat := 118140960795 + 7881480 * 2 ^ 59
def prefixEnd_7881480 : Nat := 4983230072969 + 3 ^ 40 * 7881480 * 2
def baseEnd_7881480 : Nat := 449665278755325434105971

theorem tailTrace_7881480 : CollatzResearch.WordTrace tailWord_7881480 prefixEnd_7881480 449665278755325434105971 := by
  unfold tailWord_7881480
  simp only [CollatzResearch.WordTrace]
  refine ⟨143730595743375742232312947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191640794324500989643083929 143730595743375742232312947)
  ·
    refine ⟨215595893615063613348469421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143730595743375742232312947 215595893615063613348469421)
    ·
      refine ⟨80848460105648855005676033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215595893615063613348469421 80848460105648855005676033)
      ·
        refine ⟨60636345079236641254257025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80848460105648855005676033 60636345079236641254257025)
        ·
          refine ⟨45477258809427480940692769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60636345079236641254257025 45477258809427480940692769)
          ·
            refine ⟨34107944107070610705519577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45477258809427480940692769 34107944107070610705519577)
            ·
              refine ⟨25580958080302958029139683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34107944107070610705519577 25580958080302958029139683)
              ·
                refine ⟨38371437120454437043709525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25580958080302958029139683 38371437120454437043709525)
                ·
                  refine ⟨449665278755325434105971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38371437120454437043709525 449665278755325434105971)
                  ·
                    rfl

theorem cell23_7881480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 8].length) (baseStart_7881480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881480 prefixEnd_7881480 := by exact prefixLift 7881480
  have htrace : WordTrace (prefixWord ++ tailWord_7881480) baseStart_7881480 baseEnd_7881480 := by
    simpa [prefixWord, tailWord_7881480, baseEnd_7881480] using wordTrace_append hprefix tailTrace_7881480
  have hstable : (prefixWord ++ tailWord_7881480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881480).length < 2 ^ (prefixWord ++ tailWord_7881480).sum := by decide
  have hdescent : baseEnd_7881480 < baseStart_7881480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881507 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 3]
def baseStart_7881507 : Nat := 118140960795 + 7881507 * 2 ^ 59
def prefixEnd_7881507 : Nat := 4983230072969 + 3 ^ 40 * 7881507 * 2
def baseEnd_7881507 : Nat := 4047001372775600301316115

theorem tailTrace_7881507 : CollatzResearch.WordTrace tailWord_7881507 prefixEnd_7881507 4047001372775600301316115 := by
  unfold tailWord_7881507
  simp only [CollatzResearch.WordTrace]
  refine ⟨287462176257653668075858775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191641450838435778717239183 287462176257653668075858775)
  ·
    refine ⟨431193264386480502113788163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287462176257653668075858775 431193264386480502113788163)
    ·
      refine ⟨646789896579720753170682245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431193264386480502113788163 646789896579720753170682245)
      ·
        refine ⟨121273105608697641219502921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 646789896579720753170682245 121273105608697641219502921)
        ·
          refine ⟨90954829206523230914627191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121273105608697641219502921 90954829206523230914627191)
          ·
            refine ⟨136432243809784846371940787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90954829206523230914627191 136432243809784846371940787)
            ·
              refine ⟨204648365714677269557911181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136432243809784846371940787 204648365714677269557911181)
              ·
                refine ⟨76743137143003976084216693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204648365714677269557911181 76743137143003976084216693)
                ·
                  refine ⟨7194669107156622757895315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76743137143003976084216693 7194669107156622757895315)
                  ·
                    refine ⟨10792003660734934136842973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7194669107156622757895315 10792003660734934136842973)
                    ·
                      refine ⟨4047001372775600301316115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792003660734934136842973 4047001372775600301316115)
                      ·
                        rfl

theorem cell23_7881507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_7881507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881507 prefixEnd_7881507 := by exact prefixLift 7881507
  have htrace : WordTrace (prefixWord ++ tailWord_7881507) baseStart_7881507 baseEnd_7881507 := by
    simpa [prefixWord, tailWord_7881507, baseEnd_7881507] using wordTrace_append hprefix tailTrace_7881507
  have hstable : (prefixWord ++ tailWord_7881507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881507).length < 2 ^ (prefixWord ++ tailWord_7881507).sum := by decide
  have hdescent : baseEnd_7881507 < baseStart_7881507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881557 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_7881557 : Nat := 118140960795 + 7881557 * 2 ^ 59
def prefixEnd_7881557 : Nat := 4983230072969 + 3 ^ 40 * 7881557 * 2
def baseEnd_7881557 : Nat := 1349009015602775035230295

theorem tailTrace_7881557 : CollatzResearch.WordTrace tailWord_7881557 prefixEnd_7881557 1349009015602775035230295 := by
  unfold tailWord_7881557
  simp only [CollatzResearch.WordTrace]
  refine ⟨287463999907472526615178925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191642666604981684410119283 287463999907472526615178925)
  ·
    refine ⟨107798999965302197480692097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287463999907472526615178925 107798999965302197480692097)
    ·
      refine ⟨80849249973976648110519073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107798999965302197480692097 80849249973976648110519073)
      ·
        refine ⟨60636937480482486082889305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80849249973976648110519073 60636937480482486082889305)
        ·
          refine ⟨45477703110361864562166979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60636937480482486082889305 45477703110361864562166979)
          ·
            refine ⟨68216554665542796843250469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45477703110361864562166979 68216554665542796843250469)
            ·
              refine ⟨12790603999789274408109463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68216554665542796843250469 12790603999789274408109463)
              ·
                refine ⟨19185905999683911612164195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12790603999789274408109463 19185905999683911612164195)
                ·
                  refine ⟨28778858999525867418246293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19185905999683911612164195 28778858999525867418246293)
                  ·
                    refine ⟨1349009015602775035230295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28778858999525867418246293 1349009015602775035230295)
                    ·
                      rfl

theorem cell23_7881557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_7881557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881557 prefixEnd_7881557 := by exact prefixLift 7881557
  have htrace : WordTrace (prefixWord ++ tailWord_7881557) baseStart_7881557 baseEnd_7881557 := by
    simpa [prefixWord, tailWord_7881557, baseEnd_7881557] using wordTrace_append hprefix tailTrace_7881557
  have hstable : (prefixWord ++ tailWord_7881557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881557).length < 2 ^ (prefixWord ++ tailWord_7881557).sum := by decide
  have hdescent : baseEnd_7881557 < baseStart_7881557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881560 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_7881560 : Nat := 118140960795 + 7881560 * 2 ^ 59
def prefixEnd_7881560 : Nat := 4983230072969 + 3 ^ 40 * 7881560 * 2
def baseEnd_7881560 : Nat := 4047028587250288593953371

theorem tailTrace_7881560 : CollatzResearch.WordTrace tailWord_7881560 prefixEnd_7881560 4047028587250288593953371 := by
  unfold tailWord_7881560
  simp only [CollatzResearch.WordTrace]
  refine ⟨143732054663230829063769067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191642739550974438751692089 143732054663230829063769067)
  ·
    refine ⟨215598081994846243595653601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143732054663230829063769067 215598081994846243595653601)
    ·
      refine ⟨161698561496134682696740201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215598081994846243595653601 161698561496134682696740201)
      ·
        refine ⟨121273921122101012022555151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161698561496134682696740201 121273921122101012022555151)
        ·
          refine ⟨181910881683151518033832727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121273921122101012022555151 181910881683151518033832727)
          ·
            refine ⟨272866322524727277050749091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181910881683151518033832727 272866322524727277050749091)
            ·
              refine ⟨409299483787090915576123637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272866322524727277050749091 409299483787090915576123637)
              ·
                refine ⟨38371826605039773335261591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409299483787090915576123637 38371826605039773335261591)
                ·
                  refine ⟨57557739907559660002892387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38371826605039773335261591 57557739907559660002892387)
                  ·
                    refine ⟨86336609861339490004338581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57557739907559660002892387 86336609861339490004338581)
                    ·
                      refine ⟨4047028587250288593953371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86336609861339490004338581 4047028587250288593953371)
                      ·
                        rfl

theorem cell23_7881560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_7881560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881560 prefixEnd_7881560 := by exact prefixLift 7881560
  have htrace : WordTrace (prefixWord ++ tailWord_7881560) baseStart_7881560 baseEnd_7881560 := by
    simpa [prefixWord, tailWord_7881560, baseEnd_7881560] using wordTrace_append hprefix tailTrace_7881560
  have hstable : (prefixWord ++ tailWord_7881560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881560).length < 2 ^ (prefixWord ++ tailWord_7881560).sum := by decide
  have hdescent : baseEnd_7881560 < baseStart_7881560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881564 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7881564 : Nat := 118140960795 + 7881564 * 2 ^ 59
def prefixEnd_7881564 : Nat := 4983230072969 + 3 ^ 40 * 7881564 * 2
def baseEnd_7881564 : Nat := 4047030641172906578303353

theorem tailTrace_7881564 : CollatzResearch.WordTrace tailWord_7881564 prefixEnd_7881564 4047030641172906578303353 := by
  unfold tailWord_7881564
  simp only [CollatzResearch.WordTrace]
  refine ⟨143732127609223583405341873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191642836812298111207122497 143732127609223583405341873)
  ·
    refine ⟨107799095706917687554006405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143732127609223583405341873 107799095706917687554006405)
    ·
      refine ⟨20212330445047066416376201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107799095706917687554006405 20212330445047066416376201)
      ·
        refine ⟨15159247833785299812282151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20212330445047066416376201 15159247833785299812282151)
        ·
          refine ⟨22738871750677949718423227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15159247833785299812282151 22738871750677949718423227)
          ·
            refine ⟨34108307626016924577634841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22738871750677949718423227 34108307626016924577634841)
            ·
              refine ⟨25581230719512693433226131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34108307626016924577634841 25581230719512693433226131)
              ·
                refine ⟨38371846079269040149839197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25581230719512693433226131 38371846079269040149839197)
                ·
                  refine ⟨14389442279725890056189699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38371846079269040149839197 14389442279725890056189699)
                  ·
                    refine ⟨21584163419588835084284549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14389442279725890056189699 21584163419588835084284549)
                    ·
                      refine ⟨4047030641172906578303353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21584163419588835084284549 4047030641172906578303353)
                      ·
                        rfl

theorem cell23_7881564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7881564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881564 prefixEnd_7881564 := by exact prefixLift 7881564
  have htrace : WordTrace (prefixWord ++ tailWord_7881564) baseStart_7881564 baseEnd_7881564 := by
    simpa [prefixWord, tailWord_7881564, baseEnd_7881564] using wordTrace_append hprefix tailTrace_7881564
  have hstable : (prefixWord ++ tailWord_7881564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881564).length < 2 ^ (prefixWord ++ tailWord_7881564).sum := by decide
  have hdescent : baseEnd_7881564 < baseStart_7881564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881567 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 3]
def baseStart_7881567 : Nat := 118140960795 + 7881567 * 2 ^ 59
def prefixEnd_7881567 : Nat := 4983230072969 + 3 ^ 40 * 7881567 * 2
def baseEnd_7881567 : Nat := 4047032181614870066565839

theorem tailTrace_7881567 : CollatzResearch.WordTrace tailWord_7881567 prefixEnd_7881567 4047032181614870066565839 := by
  unfold tailWord_7881567
  simp only [CollatzResearch.WordTrace]
  refine ⟨287464364637436298323042955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191642909758290865548695303 287464364637436298323042955)
  ·
    refine ⟨431196546956154447484564433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287464364637436298323042955 431196546956154447484564433)
    ·
      refine ⟨323397410217115835613423325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431196546956154447484564433 323397410217115835613423325)
      ·
        refine ⟨121274028831418438355033747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323397410217115835613423325 121274028831418438355033747)
        ·
          refine ⟨181911043247127657532550621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121274028831418438355033747 181911043247127657532550621)
          ·
            refine ⟨68216641217672871574706483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181911043247127657532550621 68216641217672871574706483)
            ·
              refine ⟨102324961826509307362059725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68216641217672871574706483 102324961826509307362059725)
              ·
                refine ⟨38371860684940990260772397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102324961826509307362059725 38371860684940990260772397)
                ·
                  refine ⟨14389447756852871347789649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38371860684940990260772397 14389447756852871347789649)
                  ·
                    refine ⟨10792085817639653510842237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14389447756852871347789649 10792085817639653510842237)
                    ·
                      refine ⟨4047032181614870066565839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792085817639653510842237 4047032181614870066565839)
                      ·
                        rfl

theorem cell23_7881567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_7881567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881567 prefixEnd_7881567 := by exact prefixLift 7881567
  have htrace : WordTrace (prefixWord ++ tailWord_7881567) baseStart_7881567 baseEnd_7881567 := by
    simpa [prefixWord, tailWord_7881567, baseEnd_7881567] using wordTrace_append hprefix tailTrace_7881567
  have hstable : (prefixWord ++ tailWord_7881567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881567).length < 2 ^ (prefixWord ++ tailWord_7881567).sum := by decide
  have hdescent : baseEnd_7881567 < baseStart_7881567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881597 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_7881597 : Nat := 118140960795 + 7881597 * 2 ^ 59
def prefixEnd_7881597 : Nat := 4983230072969 + 3 ^ 40 * 7881597 * 2
def baseEnd_7881597 : Nat := 4047047586034504949190701

theorem tailTrace_7881597 : CollatzResearch.WordTrace tailWord_7881597 prefixEnd_7881597 4047047586034504949190701 := by
  unfold tailWord_7881597
  simp only [CollatzResearch.WordTrace]
  refine ⟨287465458827327613446635045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191643639218218408964423363 287465458827327613446635045)
  ·
    refine ⟨53899773530123927521244071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287465458827327613446635045 53899773530123927521244071)
    ·
      refine ⟨80849660295185891281866107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53899773530123927521244071 80849660295185891281866107)
      ·
        refine ⟨121274490442778836922799161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80849660295185891281866107 121274490442778836922799161)
        ·
          refine ⟨90955867832084127692099371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121274490442778836922799161 90955867832084127692099371)
          ·
            refine ⟨136433801748126191538149057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90955867832084127692099371 136433801748126191538149057)
            ·
              refine ⟨102325351311094643653611793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136433801748126191538149057 102325351311094643653611793)
              ·
                refine ⟨76744013483320982740208845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102325351311094643653611793 76744013483320982740208845)
                ·
                  refine ⟨28779005056245368527578317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76744013483320982740208845 28779005056245368527578317)
                  ·
                    refine ⟨10792126896092013197841869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28779005056245368527578317 10792126896092013197841869)
                    ·
                      refine ⟨4047047586034504949190701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792126896092013197841869 4047047586034504949190701)
                      ·
                        rfl

theorem cell23_7881597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_7881597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881597 prefixEnd_7881597 := by exact prefixLift 7881597
  have htrace : WordTrace (prefixWord ++ tailWord_7881597) baseStart_7881597 baseEnd_7881597 := by
    simpa [prefixWord, tailWord_7881597, baseEnd_7881597] using wordTrace_append hprefix tailTrace_7881597
  have hstable : (prefixWord ++ tailWord_7881597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881597).length < 2 ^ (prefixWord ++ tailWord_7881597).sum := by decide
  have hdescent : baseEnd_7881597 < baseStart_7881597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881600 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 2, 7]
def baseStart_7881600 : Nat := 118140960795 + 7881600 * 2 ^ 59
def prefixEnd_7881600 : Nat := 4983230072969 + 3 ^ 40 * 7881600 * 2
def baseEnd_7881600 : Nat := 1349016375492156145817729

theorem tailTrace_7881600 : CollatzResearch.WordTrace tailWord_7881600 prefixEnd_7881600 1349016375492156145817729 := by
  unfold tailWord_7881600
  simp only [CollatzResearch.WordTrace]
  refine ⟨143732784123158372479497127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191643712164211163305996169 143732784123158372479497127)
  ·
    refine ⟨215599176184737558719245691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143732784123158372479497127 215599176184737558719245691)
    ·
      refine ⟨323398764277106338078868537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215599176184737558719245691 323398764277106338078868537)
      ·
        refine ⟨242549073207829753559151403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323398764277106338078868537 242549073207829753559151403)
        ·
          refine ⟨363823609811744630338727105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242549073207829753559151403 363823609811744630338727105)
          ·
            refine ⟨272867707358808472754045329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363823609811744630338727105 272867707358808472754045329)
            ·
              refine ⟨204650780519106354565533997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272867707358808472754045329 204650780519106354565533997)
              ·
                refine ⟨76744042694664882962075249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204650780519106354565533997 76744042694664882962075249)
                ·
                  refine ⟨57558032020998662221556437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76744042694664882962075249 57558032020998662221556437)
                  ·
                    refine ⟨1349016375492156145817729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57558032020998662221556437 1349016375492156145817729)
                    ·
                      rfl

theorem cell23_7881600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_7881600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881600 prefixEnd_7881600 := by exact prefixLift 7881600
  have htrace : WordTrace (prefixWord ++ tailWord_7881600) baseStart_7881600 baseEnd_7881600 := by
    simpa [prefixWord, tailWord_7881600, baseEnd_7881600] using wordTrace_append hprefix tailTrace_7881600
  have hstable : (prefixWord ++ tailWord_7881600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881600).length < 2 ^ (prefixWord ++ tailWord_7881600).sum := by decide
  have hdescent : baseEnd_7881600 < baseStart_7881600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881618 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7881618 : Nat := 118140960795 + 7881618 * 2 ^ 59
def prefixEnd_7881618 : Nat := 4983230072969 + 3 ^ 40 * 7881618 * 2
def baseEnd_7881618 : Nat := 4047058369128249367028105

theorem tailTrace_7881618 : CollatzResearch.WordTrace tailWord_7881618 prefixEnd_7881618 4047058369128249367028105 := by
  unfold tailWord_7881618
  simp only [CollatzResearch.WordTrace]
  refine ⟨71866556190062883508287377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191644149840167689355433005 71866556190062883508287377)
  ·
    refine ⟨53899917142547162631215533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71866556190062883508287377 53899917142547162631215533)
    ·
      refine ⟨20212468928455185986705825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53899917142547162631215533 20212468928455185986705825)
      ·
        refine ⟨15159351696341389490029369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20212468928455185986705825 15159351696341389490029369)
        ·
          refine ⟨11369513772256042117522027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15159351696341389490029369 11369513772256042117522027)
          ·
            refine ⟨17054270658384063176283041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11369513772256042117522027 17054270658384063176283041)
            ·
              refine ⟨12790702993788047382212281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17054270658384063176283041 12790702993788047382212281)
              ·
                refine ⟨9593027245341035536659211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12790702993788047382212281 9593027245341035536659211)
                ·
                  refine ⟨14389540868011553304988817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9593027245341035536659211 14389540868011553304988817)
                  ·
                    refine ⟨10792155651008664978741613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14389540868011553304988817 10792155651008664978741613)
                    ·
                      refine ⟨4047058369128249367028105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792155651008664978741613 4047058369128249367028105)
                      ·
                        rfl

theorem cell23_7881618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7881618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881618 prefixEnd_7881618 := by exact prefixLift 7881618
  have htrace : WordTrace (prefixWord ++ tailWord_7881618) baseStart_7881618 baseEnd_7881618 := by
    simpa [prefixWord, tailWord_7881618, baseEnd_7881618] using wordTrace_append hprefix tailTrace_7881618
  have hstable : (prefixWord ++ tailWord_7881618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881618).length < 2 ^ (prefixWord ++ tailWord_7881618).sum := by decide
  have hdescent : baseEnd_7881618 < baseStart_7881618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881687 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_7881687 : Nat := 118140960795 + 7881687 * 2 ^ 59
def prefixEnd_7881687 : Nat := 4983230072969 + 3 ^ 40 * 7881687 * 2
def baseEnd_7881687 : Nat := 4047093799293409597065287

theorem tailTrace_7881687 : CollatzResearch.WordTrace tailWord_7881687 prefixEnd_7881687 4047093799293409597065287 := by
  unfold tailWord_7881687
  simp only [CollatzResearch.WordTrace]
  refine ⟨287468741397001558817411315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191645827598001039211607543 287468741397001558817411315)
  ·
    refine ⟨431203112095502338226116973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287468741397001558817411315 431203112095502338226116973)
    ·
      refine ⟨161701167035813376834793865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431203112095502338226116973 161701167035813376834793865)
      ·
        refine ⟨121275875276860032626095399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161701167035813376834793865 121275875276860032626095399)
        ·
          refine ⟨181913812915290048939143099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121275875276860032626095399 181913812915290048939143099)
          ·
            refine ⟨272870719372935073408714649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181913812915290048939143099 272870719372935073408714649)
            ·
              refine ⟨204653039529701305056535987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272870719372935073408714649 204653039529701305056535987)
              ·
                refine ⟨306979559294551957584803981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204653039529701305056535987 306979559294551957584803981)
                ·
                  refine ⟨115117334735456984094301493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306979559294551957584803981 115117334735456984094301493)
                  ·
                    refine ⟨10792250131449092258840765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115117334735456984094301493 10792250131449092258840765)
                    ·
                      refine ⟨4047093799293409597065287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792250131449092258840765 4047093799293409597065287)
                      ·
                        rfl

theorem cell23_7881687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_7881687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881687 prefixEnd_7881687 := by exact prefixLift 7881687
  have htrace : WordTrace (prefixWord ++ tailWord_7881687) baseStart_7881687 baseEnd_7881687 := by
    simpa [prefixWord, tailWord_7881687, baseEnd_7881687] using wordTrace_append hprefix tailTrace_7881687
  have hstable : (prefixWord ++ tailWord_7881687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881687).length < 2 ^ (prefixWord ++ tailWord_7881687).sum := by decide
  have hdescent : baseEnd_7881687 < baseStart_7881687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881711 : List Nat := [1, 1, 2, 1, 4, 3, 4, 2, 5]
def baseStart_7881711 : Nat := 118140960795 + 7881711 * 2 ^ 59
def prefixEnd_7881711 : Nat := 4983230072969 + 3 ^ 40 * 7881711 * 2
def baseEnd_7881711 : Nat := 449678458092124167018353

theorem tailTrace_7881711 : CollatzResearch.WordTrace tailWord_7881711 prefixEnd_7881711 449678458092124167018353 := by
  unfold tailWord_7881711
  simp only [CollatzResearch.WordTrace]
  refine ⟨287469616748914610916284987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191646411165943073944189991 287469616748914610916284987)
  ·
    refine ⟨431204425123371916374427481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287469616748914610916284987 431204425123371916374427481)
    ·
      refine ⟨323403318842528937280820611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431204425123371916374427481 323403318842528937280820611)
      ·
        refine ⟨485104978263793405921230917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323403318842528937280820611 485104978263793405921230917)
        ·
          refine ⟨90957183424461263610230797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485104978263793405921230917 90957183424461263610230797)
          ·
            refine ⟨34108943784172973853836549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90957183424461263610230797 34108943784172973853836549)
            ·
              refine ⟨6395426959532432597594353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34108943784172973853836549 6395426959532432597594353)
              ·
                refine ⟨4796570219649324448195765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6395426959532432597594353 4796570219649324448195765)
                ·
                  refine ⟨449678458092124167018353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4796570219649324448195765 449678458092124167018353)
                  ·
                    rfl

theorem cell23_7881711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 5].length) (baseStart_7881711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881711 prefixEnd_7881711 := by exact prefixLift 7881711
  have htrace : WordTrace (prefixWord ++ tailWord_7881711) baseStart_7881711 baseEnd_7881711 := by
    simpa [prefixWord, tailWord_7881711, baseEnd_7881711] using wordTrace_append hprefix tailTrace_7881711
  have hstable : (prefixWord ++ tailWord_7881711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881711).length < 2 ^ (prefixWord ++ tailWord_7881711).sum := by decide
  have hdescent : baseEnd_7881711 < baseStart_7881711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881744 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 6, 4, 2]
def baseStart_7881744 : Nat := 118140960795 + 7881744 * 2 ^ 59
def prefixEnd_7881744 : Nat := 4983230072969 + 3 ^ 40 * 7881744 * 2
def baseEnd_7881744 : Nat := 4047123067690715874052525

theorem tailTrace_7881744 : CollatzResearch.WordTrace tailWord_7881744 prefixEnd_7881744 4047123067690715874052525 := by
  unfold tailWord_7881744
  simp only [CollatzResearch.WordTrace]
  refine ⟨143735410178897528776118143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191647213571863371701490857 143735410178897528776118143)
  ·
    refine ⟨215603115268346293164177215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143735410178897528776118143 215603115268346293164177215)
    ·
      refine ⟨323404672902519439746265823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215603115268346293164177215 323404672902519439746265823)
      ·
        refine ⟨485107009353779159619398735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323404672902519439746265823 485107009353779159619398735)
        ·
          refine ⟨727660514030668739429098103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485107009353779159619398735 727660514030668739429098103)
          ·
            refine ⟨1091490771046003109143647155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727660514030668739429098103 1091490771046003109143647155)
            ·
              refine ⟨1637236156569004663715470733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091490771046003109143647155 1637236156569004663715470733)
              ·
                refine ⟨613963558713376748893301525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1637236156569004663715470733 613963558713376748893301525)
                ·
                  refine ⟨28779541814689535104373509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 613963558713376748893301525 28779541814689535104373509)
                  ·
                    refine ⟨5396164090254287832070033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28779541814689535104373509 5396164090254287832070033)
                    ·
                      refine ⟨4047123067690715874052525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5396164090254287832070033 4047123067690715874052525)
                      ·
                        rfl

theorem cell23_7881744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 4, 2].length) (baseStart_7881744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881744 prefixEnd_7881744 := by exact prefixLift 7881744
  have htrace : WordTrace (prefixWord ++ tailWord_7881744) baseStart_7881744 baseEnd_7881744 := by
    simpa [prefixWord, tailWord_7881744, baseEnd_7881744] using wordTrace_append hprefix tailTrace_7881744
  have hstable : (prefixWord ++ tailWord_7881744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881744).length < 2 ^ (prefixWord ++ tailWord_7881744).sum := by decide
  have hdescent : baseEnd_7881744 < baseStart_7881744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881754 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_7881754 : Nat := 118140960795 + 7881754 * 2 ^ 59
def prefixEnd_7881754 : Nat := 4983230072969 + 3 ^ 40 * 7881754 * 2
def baseEnd_7881754 : Nat := 1349042734165753611642493

theorem tailTrace_7881754 : CollatzResearch.WordTrace tailWord_7881754 prefixEnd_7881754 1349042734165753611642493 := by
  unfold tailWord_7881754
  simp only [CollatzResearch.WordTrace]
  refine ⟨71867796271939707315025079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191647456725172552840066877 71867796271939707315025079)
  ·
    refine ⟨107801694407909560972537619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71867796271939707315025079 107801694407909560972537619)
    ·
      refine ⟨161702541611864341458806429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107801694407909560972537619 161702541611864341458806429)
      ·
        refine ⟨60638453104449128047052411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161702541611864341458806429 60638453104449128047052411)
        ·
          refine ⟨90957679656673692070578617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60638453104449128047052411 90957679656673692070578617)
          ·
            refine ⟨68218259742505269052933963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90957679656673692070578617 68218259742505269052933963)
            ·
              refine ⟨102327389613757903579400945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68218259742505269052933963 102327389613757903579400945)
              ·
                refine ⟨76745542210318427684550709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102327389613757903579400945 76745542210318427684550709)
                ·
                  refine ⟨7194894582217352595426629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76745542210318427684550709 7194894582217352595426629)
                  ·
                    refine ⟨1349042734165753611642493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7194894582217352595426629 1349042734165753611642493)
                    ·
                      rfl

theorem cell23_7881754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_7881754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881754 prefixEnd_7881754 := by exact prefixLift 7881754
  have htrace : WordTrace (prefixWord ++ tailWord_7881754) baseStart_7881754 baseEnd_7881754 := by
    simpa [prefixWord, tailWord_7881754, baseEnd_7881754] using wordTrace_append hprefix tailTrace_7881754
  have hstable : (prefixWord ++ tailWord_7881754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881754).length < 2 ^ (prefixWord ++ tailWord_7881754).sum := by decide
  have hdescent : baseEnd_7881754 < baseStart_7881754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881761 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_7881761 : Nat := 118140960795 + 7881761 * 2 ^ 59
def prefixEnd_7881761 : Nat := 4983230072969 + 3 ^ 40 * 7881761 * 2
def baseEnd_7881761 : Nat := 4047131796861842307539947

theorem tailTrace_7881761 : CollatzResearch.WordTrace tailWord_7881761 prefixEnd_7881761 4047131796861842307539947 := by
  unfold tailWord_7881761
  simp only [CollatzResearch.WordTrace]
  refine ⟨287471440398733469455605137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191647626932488979637070091 287471440398733469455605137)
  ·
    refine ⟨215603580299050102091703853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287471440398733469455605137 215603580299050102091703853)
    ·
      refine ⟨80851342612143788284388945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215603580299050102091703853 80851342612143788284388945)
      ·
        refine ⟨60638506959107841213291709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80851342612143788284388945 60638506959107841213291709)
        ·
          refine ⟨22739440109665440454984391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60638506959107841213291709 22739440109665440454984391)
          ·
            refine ⟨34109160164498160682476587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22739440109665440454984391 34109160164498160682476587)
            ·
              refine ⟨51163740246747241023714881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34109160164498160682476587 51163740246747241023714881)
              ·
                refine ⟨38372805185060430767786161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51163740246747241023714881 38372805185060430767786161)
                ·
                  refine ⟨28779603888795323075839621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38372805185060430767786161 28779603888795323075839621)
                  ·
                    refine ⟨5396175729149123076719929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28779603888795323075839621 5396175729149123076719929)
                    ·
                      refine ⟨4047131796861842307539947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5396175729149123076719929 4047131796861842307539947)
                      ·
                        rfl

theorem cell23_7881761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_7881761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881761 prefixEnd_7881761 := by exact prefixLift 7881761
  have htrace : WordTrace (prefixWord ++ tailWord_7881761) baseStart_7881761 baseEnd_7881761 := by
    simpa [prefixWord, tailWord_7881761, baseEnd_7881761] using wordTrace_append hprefix tailTrace_7881761
  have hstable : (prefixWord ++ tailWord_7881761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881761).length < 2 ^ (prefixWord ++ tailWord_7881761).sum := by decide
  have hdescent : baseEnd_7881761 < baseStart_7881761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881771 : List Nat := [1, 1, 1, 1, 2, 1, 5, 6, 1, 4]
def baseStart_7881771 : Nat := 118140960795 + 7881771 * 2 ^ 59
def prefixEnd_7881771 : Nat := 4983230072969 + 3 ^ 40 * 7881771 * 2
def baseEnd_7881771 : Nat := 1349045643889462422804967

theorem tailTrace_7881771 : CollatzResearch.WordTrace tailWord_7881771 prefixEnd_7881771 1349045643889462422804967 := by
  unfold tailWord_7881771
  simp only [CollatzResearch.WordTrace]
  refine ⟨287471805128697241163469167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191647870085798160775646111 287471805128697241163469167)
  ·
    refine ⟨431207707693045861745203751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287471805128697241163469167 431207707693045861745203751)
    ·
      refine ⟨646811561539568792617805627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431207707693045861745203751 646811561539568792617805627)
      ·
        refine ⟨970217342309353188926708441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646811561539568792617805627 970217342309353188926708441)
        ·
          refine ⟨727663006732014891695031331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970217342309353188926708441 727663006732014891695031331)
          ·
            refine ⟨1091494510098022337542546997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727663006732014891695031331 1091494510098022337542546997)
            ·
              refine ⟨102327610321689594144613781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1091494510098022337542546997 102327610321689594144613781)
              ·
                refine ⟨4796606733829199725528771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102327610321689594144613781 4796606733829199725528771)
                ·
                  refine ⟨7194910100743799588293157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796606733829199725528771 7194910100743799588293157)
                  ·
                    refine ⟨1349045643889462422804967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7194910100743799588293157 1349045643889462422804967)
                    ·
                      rfl

theorem cell23_7881771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 4].length) (baseStart_7881771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881771 prefixEnd_7881771 := by exact prefixLift 7881771
  have htrace : WordTrace (prefixWord ++ tailWord_7881771) baseStart_7881771 baseEnd_7881771 := by
    simpa [prefixWord, tailWord_7881771, baseEnd_7881771] using wordTrace_append hprefix tailTrace_7881771
  have hstable : (prefixWord ++ tailWord_7881771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881771).length < 2 ^ (prefixWord ++ tailWord_7881771).sum := by decide
  have hdescent : baseEnd_7881771 < baseStart_7881771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881774 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_7881774 : Nat := 118140960795 + 7881774 * 2 ^ 59
def prefixEnd_7881774 : Nat := 4983230072969 + 3 ^ 40 * 7881774 * 2
def baseEnd_7881774 : Nat := 4047138472110350756677387

theorem tailTrace_7881774 : CollatzResearch.WordTrace tailWord_7881774 prefixEnd_7881774 4047138472110350756677387 := by
  unfold tailWord_7881774
  simp only [CollatzResearch.WordTrace]
  refine ⟨35933989318460796584478547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191647943031790915117218917 35933989318460796584478547)
  ·
    refine ⟨53900983977691194876717821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35933989318460796584478547 53900983977691194876717821)
    ·
      refine ⟨20212868991634198078769183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53900983977691194876717821 20212868991634198078769183)
      ·
        refine ⟨30319303487451297118153775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20212868991634198078769183 30319303487451297118153775)
        ·
          refine ⟨45478955231176945677230663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30319303487451297118153775 45478955231176945677230663)
          ·
            refine ⟨68218432846765418515845995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45478955231176945677230663 68218432846765418515845995)
            ·
              refine ⟨102327649270148127773768993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68218432846765418515845995 102327649270148127773768993)
              ·
                refine ⟨76745736952611095830326745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102327649270148127773768993 76745736952611095830326745)
                ·
                  refine ⟨57559302714458321872745059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76745736952611095830326745 57559302714458321872745059)
                  ·
                    refine ⟨86338954071687482809117589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57559302714458321872745059 86338954071687482809117589)
                    ·
                      refine ⟨4047138472110350756677387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86338954071687482809117589 4047138472110350756677387)
                      ·
                        rfl

theorem cell23_7881774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_7881774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881774 prefixEnd_7881774 := by exact prefixLift 7881774
  have htrace : WordTrace (prefixWord ++ tailWord_7881774) baseStart_7881774 baseEnd_7881774 := by
    simpa [prefixWord, tailWord_7881774, baseEnd_7881774] using wordTrace_append hprefix tailTrace_7881774
  have hstable : (prefixWord ++ tailWord_7881774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881774).length < 2 ^ (prefixWord ++ tailWord_7881774).sum := by decide
  have hdescent : baseEnd_7881774 < baseStart_7881774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881798 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_7881798 : Nat := 118140960795 + 7881798 * 2 ^ 59
def prefixEnd_7881798 : Nat := 4983230072969 + 3 ^ 40 * 7881798 * 2
def baseEnd_7881798 : Nat := 4047150795646058662777277

theorem tailTrace_7881798 : CollatzResearch.WordTrace tailWord_7881798 prefixEnd_7881798 4047150795646058662777277 := by
  unfold tailWord_7881798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8983524684362482024209439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191648526599732949849801365 8983524684362482024209439)
  ·
    refine ⟨13475287026543723036314159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8983524684362482024209439 13475287026543723036314159)
    ·
      refine ⟨20212930539815584554471239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13475287026543723036314159 20212930539815584554471239)
      ·
        refine ⟨30319395809723376831706859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20212930539815584554471239 30319395809723376831706859)
        ·
          refine ⟨45479093714585065247560289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30319395809723376831706859 45479093714585065247560289)
          ·
            refine ⟨34109320285938798935670217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45479093714585065247560289 34109320285938798935670217)
            ·
              refine ⟨25581990214454099201752663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34109320285938798935670217 25581990214454099201752663)
              ·
                refine ⟨38372985321681148802628995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25581990214454099201752663 38372985321681148802628995)
                ·
                  refine ⟨57559477982521723203943493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38372985321681148802628995 57559477982521723203943493)
                  ·
                    refine ⟨10792402121722823100739405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57559477982521723203943493 10792402121722823100739405)
                    ·
                      refine ⟨4047150795646058662777277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792402121722823100739405 4047150795646058662777277)
                      ·
                        rfl

theorem cell23_7881798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_7881798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881798 prefixEnd_7881798 := by exact prefixLift 7881798
  have htrace : WordTrace (prefixWord ++ tailWord_7881798) baseStart_7881798 baseEnd_7881798 := by
    simpa [prefixWord, tailWord_7881798, baseEnd_7881798] using wordTrace_append hprefix tailTrace_7881798
  have hstable : (prefixWord ++ tailWord_7881798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881798).length < 2 ^ (prefixWord ++ tailWord_7881798).sum := by decide
  have hdescent : baseEnd_7881798 < baseStart_7881798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881805 : List Nat := [1, 6, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_7881805 : Nat := 118140960795 + 7881805 * 2 ^ 59
def prefixEnd_7881805 : Nat := 4983230072969 + 3 ^ 40 * 7881805 * 2
def baseEnd_7881805 : Nat := 1349051463336880045129915

theorem tailTrace_7881805 : CollatzResearch.WordTrace tailWord_7881805 prefixEnd_7881805 1349051463336880045129915 := by
  unfold tailWord_7881805
  simp only [CollatzResearch.WordTrace]
  refine ⟨287473045210574064970206869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191648696807049376646804579 287473045210574064970206869)
  ·
    refine ⟨13475298994245659295478447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287473045210574064970206869 13475298994245659295478447)
    ·
      refine ⟨20212948491368488943217671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13475298994245659295478447 20212948491368488943217671)
      ·
        refine ⟨30319422737052733414826507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20212948491368488943217671 30319422737052733414826507)
        ·
          refine ⟨45479134105579100122239761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30319422737052733414826507 45479134105579100122239761)
          ·
            refine ⟨34109350579184325091679821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45479134105579100122239761 34109350579184325091679821)
            ·
              refine ⟨12791006467194121909379933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34109350579184325091679821 12791006467194121909379933)
              ·
                refine ⟨4796627425197795716017475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12791006467194121909379933 4796627425197795716017475)
                ·
                  refine ⟨7194941137796693574026213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796627425197795716017475 7194941137796693574026213)
                  ·
                    refine ⟨1349051463336880045129915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7194941137796693574026213 1349051463336880045129915)
                    ·
                      rfl

theorem cell23_7881805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_7881805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881805 prefixEnd_7881805 := by exact prefixLift 7881805
  have htrace : WordTrace (prefixWord ++ tailWord_7881805) baseStart_7881805 baseEnd_7881805 := by
    simpa [prefixWord, tailWord_7881805, baseEnd_7881805] using wordTrace_append hprefix tailTrace_7881805
  have hstable : (prefixWord ++ tailWord_7881805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881805).length < 2 ^ (prefixWord ++ tailWord_7881805).sum := by decide
  have hdescent : baseEnd_7881805 < baseStart_7881805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881807 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_7881807 : Nat := 118140960795 + 7881807 * 2 ^ 59
def prefixEnd_7881807 : Nat := 4983230072969 + 3 ^ 40 * 7881807 * 2
def baseEnd_7881807 : Nat := 4047155416971949127564735

theorem tailTrace_7881807 : CollatzResearch.WordTrace tailWord_7881807 prefixEnd_7881807 4047155416971949127564735 := by
  unfold tailWord_7881807
  simp only [CollatzResearch.WordTrace]
  refine ⟨287473118156566819311779675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191648745437711212874519783 287473118156566819311779675)
  ·
    refine ⟨431209677234850228967669513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287473118156566819311779675 431209677234850228967669513)
    ·
      refine ⟨323407257926137671725752135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431209677234850228967669513 323407257926137671725752135)
      ·
        refine ⟨485110886889206507588628203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323407257926137671725752135 485110886889206507588628203)
        ·
          refine ⟨727666330333809761382942305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485110886889206507588628203 727666330333809761382942305)
          ·
            refine ⟨545749747750357321037206729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727666330333809761382942305 545749747750357321037206729)
            ·
              refine ⟨409312310812767990777905047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545749747750357321037206729 409312310812767990777905047)
              ·
                refine ⟨613968466219151986166857571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409312310812767990777905047 613968466219151986166857571)
                ·
                  refine ⟨920952699328727979250286357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613968466219151986166857571 920952699328727979250286357)
                  ·
                    refine ⟨43169657781034124027357173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 920952699328727979250286357 43169657781034124027357173)
                    ·
                      refine ⟨4047155416971949127564735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43169657781034124027357173 4047155416971949127564735)
                      ·
                        rfl

theorem cell23_7881807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_7881807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881807 prefixEnd_7881807 := by exact prefixLift 7881807
  have htrace : WordTrace (prefixWord ++ tailWord_7881807) baseStart_7881807 baseEnd_7881807 := by
    simpa [prefixWord, tailWord_7881807, baseEnd_7881807] using wordTrace_append hprefix tailTrace_7881807
  have hstable : (prefixWord ++ tailWord_7881807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881807).length < 2 ^ (prefixWord ++ tailWord_7881807).sum := by decide
  have hdescent : baseEnd_7881807 < baseStart_7881807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881822 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_7881822 : Nat := 118140960795 + 7881822 * 2 ^ 59
def prefixEnd_7881822 : Nat := 4983230072969 + 3 ^ 40 * 7881822 * 2
def baseEnd_7881822 : Nat := 1349054373060588856292389

theorem tailTrace_7881822 : CollatzResearch.WordTrace tailWord_7881822 prefixEnd_7881822 1349054373060588856292389 := by
  unfold tailWord_7881822
  simp only [CollatzResearch.WordTrace]
  refine ⟨35934208156439059609196965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191649110167674984582383813 35934208156439059609196965)
  ·
    refine ⟨6737664029332323676724431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35934208156439059609196965 6737664029332323676724431)
    ·
      refine ⟨10106496043998485515086647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6737664029332323676724431 10106496043998485515086647)
      ·
        refine ⟨15159744065997728272629971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106496043998485515086647 15159744065997728272629971)
        ·
          refine ⟨22739616098996592408944957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15159744065997728272629971 22739616098996592408944957)
          ·
            refine ⟨8527356037123722153354359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22739616098996592408944957 8527356037123722153354359)
            ·
              refine ⟨12791034055685583230031539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8527356037123722153354359 12791034055685583230031539)
              ·
                refine ⟨19186551083528374845047309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12791034055685583230031539 19186551083528374845047309)
                ·
                  refine ⟨7194956656323140566892741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19186551083528374845047309 7194956656323140566892741)
                  ·
                    refine ⟨1349054373060588856292389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7194956656323140566892741 1349054373060588856292389)
                    ·
                      rfl

theorem cell23_7881822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_7881822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881822 prefixEnd_7881822 := by exact prefixLift 7881822
  have htrace : WordTrace (prefixWord ++ tailWord_7881822) baseStart_7881822 baseEnd_7881822 := by
    simpa [prefixWord, tailWord_7881822, baseEnd_7881822] using wordTrace_append hprefix tailTrace_7881822
  have hstable : (prefixWord ++ tailWord_7881822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881822).length < 2 ^ (prefixWord ++ tailWord_7881822).sum := by decide
  have hdescent : baseEnd_7881822 < baseStart_7881822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881861 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_7881861 : Nat := 118140960795 + 7881861 * 2 ^ 59
def prefixEnd_7881861 : Nat := 4983230072969 + 3 ^ 40 * 7881861 * 2
def baseEnd_7881861 : Nat := 1349061048309097305429829

theorem tailTrace_7881861 : CollatzResearch.WordTrace tailWord_7881861 prefixEnd_7881861 1349061048309097305429829 := by
  unfold tailWord_7881861
  simp only [CollatzResearch.WordTrace]
  refine ⟨287475087698371186534245437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191650058465580791022830291 287475087698371186534245437)
  ·
    refine ⟨107803157886889194950342039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287475087698371186534245437 107803157886889194950342039)
    ·
      refine ⟨161704736830333792425513059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107803157886889194950342039 161704736830333792425513059)
      ·
        refine ⟨242557105245500688638269589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161704736830333792425513059 242557105245500688638269589)
        ·
          refine ⟨11369864308382844779918887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 242557105245500688638269589 11369864308382844779918887)
          ·
            refine ⟨17054796462574267169878331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11369864308382844779918887 17054796462574267169878331)
            ·
              refine ⟨25582194693861400754817497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17054796462574267169878331 25582194693861400754817497)
              ·
                refine ⟨19186646020396050566113123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25582194693861400754817497 19186646020396050566113123)
                ·
                  refine ⟨28779969030594075849169685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19186646020396050566113123 28779969030594075849169685)
                  ·
                    refine ⟨1349061048309097305429829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28779969030594075849169685 1349061048309097305429829)
                    ·
                      rfl

theorem cell23_7881861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_7881861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881861 prefixEnd_7881861 := by exact prefixLift 7881861
  have htrace : WordTrace (prefixWord ++ tailWord_7881861) baseStart_7881861 baseEnd_7881861 := by
    simpa [prefixWord, tailWord_7881861, baseEnd_7881861] using wordTrace_append hprefix tailTrace_7881861
  have hstable : (prefixWord ++ tailWord_7881861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881861).length < 2 ^ (prefixWord ++ tailWord_7881861).sum := by decide
  have hdescent : baseEnd_7881861 < baseStart_7881861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881874 : List Nat := [3, 2, 3, 1, 1, 13]
def baseStart_7881874 : Nat := 118140960795 + 7881874 * 2 ^ 59
def prefixEnd_7881874 : Nat := 4983230072969 + 3 ^ 40 * 7881874 * 2
def baseEnd_7881874 : Nat := 16655102140641153767189

theorem tailTrace_7881874 : CollatzResearch.WordTrace tailWord_7881874 prefixEnd_7881874 16655102140641153767189 := by
  unfold tailWord_7881874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71868890461831022438617169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191650374564882726502979117 71868890461831022438617169)
  ·
    refine ⟨53901667846373266828962877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71868890461831022438617169 53901667846373266828962877)
    ·
      refine ⟨20213125442389975060861079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53901667846373266828962877 20213125442389975060861079)
      ·
        refine ⟨30319688163584962591291619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20213125442389975060861079 30319688163584962591291619)
        ·
          refine ⟨45479532245377443886937429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30319688163584962591291619 45479532245377443886937429)
          ·
            refine ⟨16655102140641153767189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 45479532245377443886937429 16655102140641153767189)
            ·
              rfl

theorem cell23_7881874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 13].length) (baseStart_7881874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881874 prefixEnd_7881874 := by exact prefixLift 7881874
  have htrace : WordTrace (prefixWord ++ tailWord_7881874) baseStart_7881874 baseEnd_7881874 := by
    simpa [prefixWord, tailWord_7881874, baseEnd_7881874] using wordTrace_append hprefix tailTrace_7881874
  have hstable : (prefixWord ++ tailWord_7881874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881874).length < 2 ^ (prefixWord ++ tailWord_7881874).sum := by decide
  have hdescent : baseEnd_7881874 < baseStart_7881874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881898 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7881898 : Nat := 118140960795 + 7881898 * 2 ^ 59
def prefixEnd_7881898 : Nat := 4983230072969 + 3 ^ 40 * 7881898 * 2
def baseEnd_7881898 : Nat := 4047202143711508271526817

theorem tailTrace_7881898 : CollatzResearch.WordTrace tailWord_7881898 prefixEnd_7881898 4047202143711508271526817 := by
  unfold tailWord_7881898
  simp only [CollatzResearch.WordTrace]
  refine ⟨71869109299809285463335587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191650958132824761235561565 71869109299809285463335587)
  ·
    refine ⟨107803663949713928195003381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71869109299809285463335587 107803663949713928195003381)
    ·
      refine ⟨10106593495285680768281567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107803663949713928195003381 10106593495285680768281567)
      ·
        refine ⟨15159890242928521152422351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106593495285680768281567 15159890242928521152422351)
        ·
          refine ⟨22739835364392781728633527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15159890242928521152422351 22739835364392781728633527)
          ·
            refine ⟨34109753046589172592950291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22739835364392781728633527 34109753046589172592950291)
            ·
              refine ⟨51164629569883758889425437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34109753046589172592950291 51164629569883758889425437)
              ·
                refine ⟨19186736088706409583534539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51164629569883758889425437 19186736088706409583534539)
                ·
                  refine ⟨28780104133059614375301809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19186736088706409583534539 28780104133059614375301809)
                  ·
                    refine ⟨21585078099794710781476357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28780104133059614375301809 21585078099794710781476357)
                    ·
                      refine ⟨4047202143711508271526817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21585078099794710781476357 4047202143711508271526817)
                      ·
                        rfl

theorem cell23_7881898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7881898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881898 prefixEnd_7881898 := by exact prefixLift 7881898
  have htrace : WordTrace (prefixWord ++ tailWord_7881898) baseStart_7881898 baseEnd_7881898 := by
    simpa [prefixWord, tailWord_7881898, baseEnd_7881898] using wordTrace_append hprefix tailTrace_7881898
  have hstable : (prefixWord ++ tailWord_7881898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881898).length < 2 ^ (prefixWord ++ tailWord_7881898).sum := by decide
  have hdescent : baseEnd_7881898 < baseStart_7881898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881914 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_7881914 : Nat := 118140960795 + 7881914 * 2 ^ 59
def prefixEnd_7881914 : Nat := 4983230072969 + 3 ^ 40 * 7881914 * 2
def baseEnd_7881914 : Nat := 4047210359401980208926743

theorem tailTrace_7881914 : CollatzResearch.WordTrace tailWord_7881914 prefixEnd_7881914 4047210359401980208926743 := by
  unfold tailWord_7881914
  simp only [CollatzResearch.WordTrace]
  refine ⟨71869255191794794146481199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191651347178119451057283197 71869255191794794146481199)
  ·
    refine ⟨107803882787692191219721799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71869255191794794146481199 107803882787692191219721799)
    ·
      refine ⟨161705824181538286829582699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107803882787692191219721799 161705824181538286829582699)
      ·
        refine ⟨242558736272307430244374049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161705824181538286829582699 242558736272307430244374049)
        ·
          refine ⟨181919052204230572683280537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242558736272307430244374049 181919052204230572683280537)
          ·
            refine ⟨136439289153172929512460403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181919052204230572683280537 136439289153172929512460403)
            ·
              refine ⟨204658933729759394268690605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136439289153172929512460403 204658933729759394268690605)
              ·
                refine ⟨76747100148659772850758977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204658933729759394268690605 76747100148659772850758977)
                ·
                  refine ⟨57560325111494829638069233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76747100148659772850758977 57560325111494829638069233)
                  ·
                    refine ⟨43170243833621122228551925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57560325111494829638069233 43170243833621122228551925)
                    ·
                      refine ⟨4047210359401980208926743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43170243833621122228551925 4047210359401980208926743)
                      ·
                        rfl

theorem cell23_7881914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_7881914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881914 prefixEnd_7881914 := by exact prefixLift 7881914
  have htrace : WordTrace (prefixWord ++ tailWord_7881914) baseStart_7881914 baseEnd_7881914 := by
    simpa [prefixWord, tailWord_7881914, baseEnd_7881914] using wordTrace_append hprefix tailTrace_7881914
  have hstable : (prefixWord ++ tailWord_7881914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881914).length < 2 ^ (prefixWord ++ tailWord_7881914).sum := by decide
  have hdescent : baseEnd_7881914 < baseStart_7881914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881918 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_7881918 : Nat := 118140960795 + 7881918 * 2 ^ 59
def prefixEnd_7881918 : Nat := 4983230072969 + 3 ^ 40 * 7881918 * 2
def baseEnd_7881918 : Nat := 4047212413324598193276725

theorem tailTrace_7881918 : CollatzResearch.WordTrace tailWord_7881918 prefixEnd_7881918 4047212413324598193276725 := by
  unfold tailWord_7881918
  simp only [CollatzResearch.WordTrace]
  refine ⟨35934645832395585658633801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191651444439443123512713605 35934645832395585658633801)
  ·
    refine ⟨26950984374296689243975351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35934645832395585658633801 26950984374296689243975351)
    ·
      refine ⟨40426476561445033865963027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26950984374296689243975351 40426476561445033865963027)
      ·
        refine ⟨60639714842167550798944541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40426476561445033865963027 60639714842167550798944541)
        ·
          refine ⟨22739893065812831549604203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60639714842167550798944541 22739893065812831549604203)
          ·
            refine ⟨34109839598719247324406305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22739893065812831549604203 34109839598719247324406305)
            ·
              refine ⟨25582379699039435493304729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34109839598719247324406305 25582379699039435493304729)
              ·
                refine ⟨19186784774279576619978547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25582379699039435493304729 19186784774279576619978547)
                ·
                  refine ⟨28780177161419364929967821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19186784774279576619978547 28780177161419364929967821)
                  ·
                    refine ⟨10792566435532261848737933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28780177161419364929967821 10792566435532261848737933)
                    ·
                      refine ⟨4047212413324598193276725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792566435532261848737933 4047212413324598193276725)
                      ·
                        rfl

theorem cell23_7881918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_7881918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881918 prefixEnd_7881918 := by exact prefixLift 7881918
  have htrace : WordTrace (prefixWord ++ tailWord_7881918) baseStart_7881918 baseEnd_7881918 := by
    simpa [prefixWord, tailWord_7881918, baseEnd_7881918] using wordTrace_append hprefix tailTrace_7881918
  have hstable : (prefixWord ++ tailWord_7881918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881918).length < 2 ^ (prefixWord ++ tailWord_7881918).sum := by decide
  have hdescent : baseEnd_7881918 < baseStart_7881918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7881998 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_7881998 : Nat := 118140960795 + 7881998 * 2 ^ 59
def prefixEnd_7881998 : Nat := 4983230072969 + 3 ^ 40 * 7881998 * 2
def baseEnd_7881998 : Nat := 449694832419661986697373

theorem tailTrace_7881998 : CollatzResearch.WordTrace tailWord_7881998 prefixEnd_7881998 449694832419661986697373 := by
  unfold tailWord_7881998
  simp only [CollatzResearch.WordTrace]
  refine ⟨35935010562359357366497831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191653389665916572621321765 35935010562359357366497831)
  ·
    refine ⟨53902515843539036049746747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35935010562359357366497831 53902515843539036049746747)
    ·
      refine ⟨80853773765308554074620121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53902515843539036049746747 80853773765308554074620121)
      ·
        refine ⟨60640330323981415555965091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80853773765308554074620121 60640330323981415555965091)
        ·
          refine ⟨90960495485972123333947637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60640330323981415555965091 90960495485972123333947637)
          ·
            refine ⟨8527546451809886562557591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90960495485972123333947637 8527546451809886562557591)
            ·
              refine ⟨12791319677714829843836387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8527546451809886562557591 12791319677714829843836387)
              ·
                refine ⟨19186979516572244765754581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12791319677714829843836387 19186979516572244765754581)
                ·
                  refine ⟨449694832419661986697373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19186979516572244765754581 449694832419661986697373)
                  ·
                    rfl

theorem cell23_7881998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_7881998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7881998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7881998 prefixEnd_7881998 := by exact prefixLift 7881998
  have htrace : WordTrace (prefixWord ++ tailWord_7881998) baseStart_7881998 baseEnd_7881998 := by
    simpa [prefixWord, tailWord_7881998, baseEnd_7881998] using wordTrace_append hprefix tailTrace_7881998
  have hstable : (prefixWord ++ tailWord_7881998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7881998).length < 2 ^ (prefixWord ++ tailWord_7881998).sum := by decide
  have hdescent : baseEnd_7881998 < baseStart_7881998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7881998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882048 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 2, 4, 2]
def baseStart_7882048 : Nat := 118140960795 + 7882048 * 2 ^ 59
def prefixEnd_7882048 : Nat := 4983230072969 + 3 ^ 40 * 7882048 * 2
def baseEnd_7882048 : Nat := 4047279165809682684651127

theorem tailTrace_7882048 : CollatzResearch.WordTrace tailWord_7882048 prefixEnd_7882048 4047279165809682684651127 := by
  unfold tailWord_7882048
  simp only [CollatzResearch.WordTrace]
  refine ⟨143740954074346858735651399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191654605432462478314201865 143740954074346858735651399)
  ·
    refine ⟨215611431111520288103477099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143740954074346858735651399 215611431111520288103477099)
    ·
      refine ⟨323417146667280432155215649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215611431111520288103477099 323417146667280432155215649)
      ·
        refine ⟨242562860000460324116411737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323417146667280432155215649 242562860000460324116411737)
        ·
          refine ⟨181922145000345243087308803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242562860000460324116411737 181922145000345243087308803)
          ·
            refine ⟨272883217500517864630963205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181922145000345243087308803 272883217500517864630963205)
            ·
              refine ⟨51165603281347099618305601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272883217500517864630963205 51165603281347099618305601)
              ·
                refine ⟨38374202461010324713729201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51165603281347099618305601 38374202461010324713729201)
                ·
                  refine ⟨28780651845757743535296901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38374202461010324713729201 28780651845757743535296901)
                  ·
                    refine ⟨5396372221079576912868169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28780651845757743535296901 5396372221079576912868169)
                    ·
                      refine ⟨4047279165809682684651127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5396372221079576912868169 4047279165809682684651127)
                      ·
                        rfl

theorem cell23_7882048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_7882048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882048 prefixEnd_7882048 := by exact prefixLift 7882048
  have htrace : WordTrace (prefixWord ++ tailWord_7882048) baseStart_7882048 baseEnd_7882048 := by
    simpa [prefixWord, tailWord_7882048, baseEnd_7882048] using wordTrace_append hprefix tailTrace_7882048
  have hstable : (prefixWord ++ tailWord_7882048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882048).length < 2 ^ (prefixWord ++ tailWord_7882048).sum := by decide
  have hdescent : baseEnd_7882048 < baseStart_7882048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882051 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 3]
def baseStart_7882051 : Nat := 118140960795 + 7882051 * 2 ^ 59
def prefixEnd_7882051 : Nat := 4983230072969 + 3 ^ 40 * 7882051 * 2
def baseEnd_7882051 : Nat := 4047280706251646172913613

theorem tailTrace_7882051 : CollatzResearch.WordTrace tailWord_7882051 prefixEnd_7882051 4047280706251646172913613 := by
  unfold tailWord_7882051
  simp only [CollatzResearch.WordTrace]
  refine ⟨287482017567682848983662007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191654678378455232655774671 287482017567682848983662007)
  ·
    refine ⟨431223026351524273475493011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287482017567682848983662007 431223026351524273475493011)
    ·
      refine ⟨646834539527286410213239517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431223026351524273475493011 646834539527286410213239517)
      ·
        refine ⟨242562952322732403829964819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 646834539527286410213239517 242562952322732403829964819)
        ·
          refine ⟨363844428484098605744947229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242562952322732403829964819 363844428484098605744947229)
          ·
            refine ⟨136441660681536977154355211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363844428484098605744947229 136441660681536977154355211)
            ·
              refine ⟨204662491022305465731532817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136441660681536977154355211 204662491022305465731532817)
              ·
                refine ⟨153496868266729099298649613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204662491022305465731532817 153496868266729099298649613)
                ·
                  refine ⟨57561325600023412236993605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153496868266729099298649613 57561325600023412236993605)
                  ·
                    refine ⟨10792748550004389794436301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57561325600023412236993605 10792748550004389794436301)
                    ·
                      refine ⟨4047280706251646172913613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792748550004389794436301 4047280706251646172913613)
                      ·
                        rfl

theorem cell23_7882051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_7882051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882051 prefixEnd_7882051 := by exact prefixLift 7882051
  have htrace : WordTrace (prefixWord ++ tailWord_7882051) baseStart_7882051 baseEnd_7882051 := by
    simpa [prefixWord, tailWord_7882051, baseEnd_7882051] using wordTrace_append hprefix tailTrace_7882051
  have hstable : (prefixWord ++ tailWord_7882051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882051).length < 2 ^ (prefixWord ++ tailWord_7882051).sum := by decide
  have hdescent : baseEnd_7882051 < baseStart_7882051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882068 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_7882068 : Nat := 118140960795 + 7882068 * 2 ^ 59
def prefixEnd_7882068 : Nat := 4983230072969 + 3 ^ 40 * 7882068 * 2
def baseEnd_7882068 : Nat := 4047289435422772606401035

theorem tailTrace_7882068 : CollatzResearch.WordTrace tailWord_7882068 prefixEnd_7882068 4047289435422772606401035 := by
  unfold tailWord_7882068
  simp only [CollatzResearch.WordTrace]
  refine ⟨143741318804310630443515429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191655091739080840591353905 143741318804310630443515429)
  ·
    refine ⟨26951497275808243208159143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143741318804310630443515429 26951497275808243208159143)
    ·
      refine ⟨40427245913712364812238715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26951497275808243208159143 40427245913712364812238715)
      ·
        refine ⟨60640868870568547218358073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40427245913712364812238715 60640868870568547218358073)
        ·
          refine ⟨45480651652926410413768555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60640868870568547218358073 45480651652926410413768555)
          ·
            refine ⟨68220977479389615620652833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45480651652926410413768555 68220977479389615620652833)
            ·
              refine ⟨51165733109542211715489625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68220977479389615620652833 51165733109542211715489625)
              ·
                refine ⟨38374299832156658786617219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51165733109542211715489625 38374299832156658786617219)
                ·
                  refine ⟨57561449748234988179925829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38374299832156658786617219 57561449748234988179925829)
                  ·
                    refine ⟨10792771827794060283736093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57561449748234988179925829 10792771827794060283736093)
                    ·
                      refine ⟨4047289435422772606401035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792771827794060283736093 4047289435422772606401035)
                      ·
                        rfl

theorem cell23_7882068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_7882068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882068 prefixEnd_7882068 := by exact prefixLift 7882068
  have htrace : WordTrace (prefixWord ++ tailWord_7882068) baseStart_7882068 baseEnd_7882068 := by
    simpa [prefixWord, tailWord_7882068, baseEnd_7882068] using wordTrace_append hprefix tailTrace_7882068
  have hstable : (prefixWord ++ tailWord_7882068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882068).length < 2 ^ (prefixWord ++ tailWord_7882068).sum := by decide
  have hdescent : baseEnd_7882068 < baseStart_7882068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882092 : List Nat := [2, 2, 1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_7882092 : Nat := 118140960795 + 7882092 * 2 ^ 59
def prefixEnd_7882092 : Nat := 4983230072969 + 3 ^ 40 * 7882092 * 2
def baseEnd_7882092 : Nat := 1349100586319493504166975

theorem tailTrace_7882092 : CollatzResearch.WordTrace tailWord_7882092 prefixEnd_7882092 1349100586319493504166975 := by
  unfold tailWord_7882092
  simp only [CollatzResearch.WordTrace]
  refine ⟨143741756480267156492952265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191655675307022875323936353 143741756480267156492952265)
  ·
    refine ⟨107806317360200367369714199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143741756480267156492952265 107806317360200367369714199)
    ·
      refine ⟨161709476040300551054571299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107806317360200367369714199 161709476040300551054571299)
      ·
        refine ⟨242564214060450826581856949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161709476040300551054571299 242564214060450826581856949)
        ·
          refine ⟨22740395068167264992049089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242564214060450826581856949 22740395068167264992049089)
          ·
            refine ⟨17055296301125448744036817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22740395068167264992049089 17055296301125448744036817)
            ·
              refine ⟨12791472225844086558027613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17055296301125448744036817 12791472225844086558027613)
              ·
                refine ⟨4796802084691532459260355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12791472225844086558027613 4796802084691532459260355)
                ·
                  refine ⟨7195203127037298688890533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796802084691532459260355 7195203127037298688890533)
                  ·
                    refine ⟨1349100586319493504166975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7195203127037298688890533 1349100586319493504166975)
                    ·
                      rfl

theorem cell23_7882092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_7882092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882092 prefixEnd_7882092 := by exact prefixLift 7882092
  have htrace : WordTrace (prefixWord ++ tailWord_7882092) baseStart_7882092 baseEnd_7882092 := by
    simpa [prefixWord, tailWord_7882092, baseEnd_7882092] using wordTrace_append hprefix tailTrace_7882092
  have hstable : (prefixWord ++ tailWord_7882092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882092).length < 2 ^ (prefixWord ++ tailWord_7882092).sum := by decide
  have hdescent : baseEnd_7882092 < baseStart_7882092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882115 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 3]
def baseStart_7882115 : Nat := 118140960795 + 7882115 * 2 ^ 59
def prefixEnd_7882115 : Nat := 4983230072969 + 3 ^ 40 * 7882115 * 2
def baseEnd_7882115 : Nat := 4047313569013533922513319

theorem tailTrace_7882115 : CollatzResearch.WordTrace tailWord_7882115 prefixEnd_7882115 4047313569013533922513319 := by
  unfold tailWord_7882115
  simp only [CollatzResearch.WordTrace]
  refine ⟨287484351839450987913991799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191656234559633991942661199 287484351839450987913991799)
  ·
    refine ⟨431226527759176481870987699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287484351839450987913991799 431226527759176481870987699)
    ·
      refine ⟨646839791638764722806481549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431226527759176481870987699 646839791638764722806481549)
      ·
        refine ⟨242564921864536771052430581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 646839791638764722806481549 242564921864536771052430581)
        ·
          refine ⟨22740461424800322286165367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242564921864536771052430581 22740461424800322286165367)
          ·
            refine ⟨34110692137200483429248051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22740461424800322286165367 34110692137200483429248051)
            ·
              refine ⟨51166038205800725143872077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34110692137200483429248051 51166038205800725143872077)
              ·
                refine ⟨19187264327175271928952029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51166038205800725143872077 19187264327175271928952029)
                ·
                  refine ⟨7195224122690726973357011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19187264327175271928952029 7195224122690726973357011)
                  ·
                    refine ⟨10792836184036090460035517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7195224122690726973357011 10792836184036090460035517)
                    ·
                      refine ⟨4047313569013533922513319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792836184036090460035517 4047313569013533922513319)
                      ·
                        rfl

theorem cell23_7882115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_7882115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882115 prefixEnd_7882115 := by exact prefixLift 7882115
  have htrace : WordTrace (prefixWord ++ tailWord_7882115) baseStart_7882115 baseEnd_7882115 := by
    simpa [prefixWord, tailWord_7882115, baseEnd_7882115] using wordTrace_append hprefix tailTrace_7882115
  have hstable : (prefixWord ++ tailWord_7882115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882115).length < 2 ^ (prefixWord ++ tailWord_7882115).sum := by decide
  have hdescent : baseEnd_7882115 < baseStart_7882115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882132 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_7882132 : Nat := 118140960795 + 7882132 * 2 ^ 59
def prefixEnd_7882132 : Nat := 4983230072969 + 3 ^ 40 * 7882132 * 2
def baseEnd_7882132 : Nat := 4047322298184660356000741

theorem tailTrace_7882132 : CollatzResearch.WordTrace tailWord_7882132 prefixEnd_7882132 4047322298184660356000741 := by
  unfold tailWord_7882132
  simp only [CollatzResearch.WordTrace]
  refine ⟨143742485940194699908680325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191656647920259599878240433 143742485940194699908680325)
  ·
    refine ⟨26951716113786506232877561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143742485940194699908680325 26951716113786506232877561)
    ·
      refine ⟨20213787085339879674658171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26951716113786506232877561 20213787085339879674658171)
      ·
        refine ⟨30320680628009819511987257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20213787085339879674658171 30320680628009819511987257)
        ·
          refine ⟨22740510471007364633990443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30320680628009819511987257 22740510471007364633990443)
          ·
            refine ⟨34110765706511046950985665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22740510471007364633990443 34110765706511046950985665)
            ·
              refine ⟨25583074279883285213239249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34110765706511046950985665 25583074279883285213239249)
              ·
                refine ⟨19187305709912463909929437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25583074279883285213239249 19187305709912463909929437)
                ·
                  refine ⟨7195239641217173966223539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19187305709912463909929437 7195239641217173966223539)
                  ·
                    refine ⟨10792859461825760949335309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7195239641217173966223539 10792859461825760949335309)
                    ·
                      refine ⟨4047322298184660356000741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792859461825760949335309 4047322298184660356000741)
                      ·
                        rfl

theorem cell23_7882132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_7882132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882132 prefixEnd_7882132 := by exact prefixLift 7882132
  have htrace : WordTrace (prefixWord ++ tailWord_7882132) baseStart_7882132 baseEnd_7882132 := by
    simpa [prefixWord, tailWord_7882132, baseEnd_7882132] using wordTrace_append hprefix tailTrace_7882132
  have hstable : (prefixWord ++ tailWord_7882132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882132).length < 2 ^ (prefixWord ++ tailWord_7882132).sum := by decide
  have hdescent : baseEnd_7882132 < baseStart_7882132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882165 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_7882165 : Nat := 118140960795 + 7882165 * 2 ^ 59
def prefixEnd_7882165 : Nat := 4983230072969 + 3 ^ 40 * 7882165 * 2
def baseEnd_7882165 : Nat := 1349113081015419575629363

theorem tailTrace_7882165 : CollatzResearch.WordTrace tailWord_7882165 prefixEnd_7882165 1349113081015419575629363 := by
  unfold tailWord_7882165
  simp only [CollatzResearch.WordTrace]
  refine ⟨287486175489269846453311949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191657450326179897635541299 287486175489269846453311949)
  ·
    refine ⟨107807315808476192419991981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287486175489269846453311949 107807315808476192419991981)
    ·
      refine ⟨40427743428178572157496993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107807315808476192419991981 40427743428178572157496993)
      ·
        refine ⟨30320807571133929118122745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40427743428178572157496993 30320807571133929118122745)
        ·
          refine ⟨22740605678350446838592059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30320807571133929118122745 22740605678350446838592059)
          ·
            refine ⟨34110908517525670257888089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22740605678350446838592059 34110908517525670257888089)
            ·
              refine ⟨25583181388144252693416067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34110908517525670257888089 25583181388144252693416067)
              ·
                refine ⟨38374772082216379040124101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25583181388144252693416067 38374772082216379040124101)
                ·
                  refine ⟨7195269765415571070023269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38374772082216379040124101 7195269765415571070023269)
                  ·
                    refine ⟨1349113081015419575629363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7195269765415571070023269 1349113081015419575629363)
                    ·
                      rfl

theorem cell23_7882165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_7882165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882165 prefixEnd_7882165 := by exact prefixLift 7882165
  have htrace : WordTrace (prefixWord ++ tailWord_7882165) baseStart_7882165 baseEnd_7882165 := by
    simpa [prefixWord, tailWord_7882165, baseEnd_7882165] using wordTrace_append hprefix tailTrace_7882165
  have hstable : (prefixWord ++ tailWord_7882165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882165).length < 2 ^ (prefixWord ++ tailWord_7882165).sum := by decide
  have hdescent : baseEnd_7882165 < baseStart_7882165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882205 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_7882205 : Nat := 118140960795 + 7882205 * 2 ^ 59
def prefixEnd_7882205 : Nat := 4983230072969 + 3 ^ 40 * 7882205 * 2
def baseEnd_7882205 : Nat := 4047359782272438570387905

theorem tailTrace_7882205 : CollatzResearch.WordTrace tailWord_7882205 prefixEnd_7882205 4047359782272438570387905 := by
  unfold tailWord_7882205
  simp only [CollatzResearch.WordTrace]
  refine ⟨287487634409124933284768069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191658422939416622189845379 287487634409124933284768069)
  ·
    refine ⟨53903931451710924990894013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287487634409124933284768069 53903931451710924990894013)
    ·
      refine ⟨20213974294391596871585255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53903931451710924990894013 20213974294391596871585255)
      ·
        refine ⟨30320961441587395307377883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20213974294391596871585255 30320961441587395307377883)
        ·
          refine ⟨45481442162381092961066825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30320961441587395307377883 45481442162381092961066825)
          ·
            refine ⟨34111081621785819720800119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45481442162381092961066825 34111081621785819720800119)
            ·
              refine ⟨51166622432678729581200179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34111081621785819720800119 51166622432678729581200179)
              ·
                refine ⟨76749933649018094371800269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51166622432678729581200179 76749933649018094371800269)
                ·
                  refine ⟨28781225118381785389425101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76749933649018094371800269 28781225118381785389425101)
                  ·
                    refine ⟨10792959419393169521034413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28781225118381785389425101 10792959419393169521034413)
                    ·
                      refine ⟨4047359782272438570387905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10792959419393169521034413 4047359782272438570387905)
                      ·
                        rfl

theorem cell23_7882205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_7882205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882205 prefixEnd_7882205 := by exact prefixLift 7882205
  have htrace : WordTrace (prefixWord ++ tailWord_7882205) baseStart_7882205 baseEnd_7882205 := by
    simpa [prefixWord, tailWord_7882205, baseEnd_7882205] using wordTrace_append hprefix tailTrace_7882205
  have hstable : (prefixWord ++ tailWord_7882205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882205).length < 2 ^ (prefixWord ++ tailWord_7882205).sum := by decide
  have hdescent : baseEnd_7882205 < baseStart_7882205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882246 : List Nat := [6, 2, 1, 1, 2, 1, 3, 7]
def baseStart_7882246 : Nat := 118140960795 + 7882246 * 2 ^ 59
def prefixEnd_7882246 : Nat := 4983230072969 + 3 ^ 40 * 7882246 * 2
def baseEnd_7882246 : Nat := 149902993888121218887971

theorem tailTrace_7882246 : CollatzResearch.WordTrace tailWord_7882246 prefixEnd_7882246 149902993888121218887971 := by
  unfold tailWord_7882246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984035306311762415219081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191659419867984264858007061 8984035306311762415219081)
  ·
    refine ⟨6738026479733821811414311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8984035306311762415219081 6738026479733821811414311)
    ·
      refine ⟨10107039719600732717121467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738026479733821811414311 10107039719600732717121467)
      ·
        refine ⟨15160559579401099075682201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10107039719600732717121467 15160559579401099075682201)
        ·
          refine ⟨11370419684550824306761651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15160559579401099075682201 11370419684550824306761651)
          ·
            refine ⟨17055629526826236460142477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11370419684550824306761651 17055629526826236460142477)
            ·
              refine ⟨6395861072559838672553429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17055629526826236460142477 6395861072559838672553429)
              ·
                refine ⟨149902993888121218887971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6395861072559838672553429 149902993888121218887971)
                ·
                  rfl

theorem cell23_7882246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_7882246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882246 prefixEnd_7882246 := by exact prefixLift 7882246
  have htrace : WordTrace (prefixWord ++ tailWord_7882246) baseStart_7882246 baseEnd_7882246 := by
    simpa [prefixWord, tailWord_7882246, baseEnd_7882246] using wordTrace_append hprefix tailTrace_7882246
  have hstable : (prefixWord ++ tailWord_7882246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882246).length < 2 ^ (prefixWord ++ tailWord_7882246).sum := by decide
  have hdescent : baseEnd_7882246 < baseStart_7882246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882248 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_7882248 : Nat := 118140960795 + 7882248 * 2 ^ 59
def prefixEnd_7882248 : Nat := 4983230072969 + 3 ^ 40 * 7882248 * 2
def baseEnd_7882248 : Nat := 4047381861940581902150207

theorem tailTrace_7882248 : CollatzResearch.WordTrace tailWord_7882248 prefixEnd_7882248 4047381861940581902150207 := by
  unfold tailWord_7882248
  simp only [CollatzResearch.WordTrace]
  refine ⟨143744601373984575814291699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191659468498646101085722265 143744601373984575814291699)
  ·
    refine ⟨215616902060976863721437549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143744601373984575814291699 215616902060976863721437549)
    ·
      refine ⟨80856338272866323895539081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215616902060976863721437549 80856338272866323895539081)
      ·
        refine ⟨60642253704649742921654311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80856338272866323895539081 60642253704649742921654311)
        ·
          refine ⟨90963380556974614382481467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60642253704649742921654311 90963380556974614382481467)
          ·
            refine ⟨136445070835461921573722201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90963380556974614382481467 136445070835461921573722201)
            ·
              refine ⟨102333803126596441180291651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136445070835461921573722201 102333803126596441180291651)
              ·
                refine ⟨153500704689894661770437477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102333803126596441180291651 153500704689894661770437477)
                ·
                  refine ⟨28781382129355249081957027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153500704689894661770437477 28781382129355249081957027)
                  ·
                    refine ⟨43172073194032873622935541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28781382129355249081957027 43172073194032873622935541)
                    ·
                      refine ⟨4047381861940581902150207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43172073194032873622935541 4047381861940581902150207)
                      ·
                        rfl

theorem cell23_7882248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_7882248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882248 prefixEnd_7882248 := by exact prefixLift 7882248
  have htrace : WordTrace (prefixWord ++ tailWord_7882248) baseStart_7882248 baseEnd_7882248 := by
    simpa [prefixWord, tailWord_7882248, baseEnd_7882248] using wordTrace_append hprefix tailTrace_7882248
  have hstable : (prefixWord ++ tailWord_7882248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882248).length < 2 ^ (prefixWord ++ tailWord_7882248).sum := by decide
  have hdescent : baseEnd_7882248 < baseStart_7882248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882268 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 9]
def baseStart_7882268 : Nat := 118140960795 + 7882268 * 2 ^ 59
def prefixEnd_7882268 : Nat := 4983230072969 + 3 ^ 40 * 7882268 * 2
def baseEnd_7882268 : Nat := 449710236839296869322235

theorem tailTrace_7882268 : CollatzResearch.WordTrace tailWord_7882268 prefixEnd_7882268 449710236839296869322235 := by
  unfold tailWord_7882268
  simp only [CollatzResearch.WordTrace]
  refine ⟨143744966103948347522155729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191659954805264463362874305 143744966103948347522155729)
  ·
    refine ⟨107808724577961260641616797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143744966103948347522155729 107808724577961260641616797)
    ·
      refine ⟨40428271716735472740606299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107808724577961260641616797 40428271716735472740606299)
      ·
        refine ⟨60642407575103209110909449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40428271716735472740606299 60642407575103209110909449)
        ·
          refine ⟨45481805681327406833182087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60642407575103209110909449 45481805681327406833182087)
          ·
            refine ⟨68222708521991110249773131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45481805681327406833182087 68222708521991110249773131)
            ·
              refine ⟨102334062782986665374659697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68222708521991110249773131 102334062782986665374659697)
              ·
                refine ⟨76750547087239999030994773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102334062782986665374659697 76750547087239999030994773)
                ·
                  refine ⟨449710236839296869322235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76750547087239999030994773 449710236839296869322235)
                  ·
                    rfl

theorem cell23_7882268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_7882268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882268 prefixEnd_7882268 := by exact prefixLift 7882268
  have htrace : WordTrace (prefixWord ++ tailWord_7882268) baseStart_7882268 baseEnd_7882268 := by
    simpa [prefixWord, tailWord_7882268, baseEnd_7882268] using wordTrace_append hprefix tailTrace_7882268
  have hstable : (prefixWord ++ tailWord_7882268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882268).length < 2 ^ (prefixWord ++ tailWord_7882268).sum := by decide
  have hdescent : baseEnd_7882268 < baseStart_7882268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882295 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_7882295 : Nat := 118140960795 + 7882295 * 2 ^ 59
def prefixEnd_7882295 : Nat := 4983230072969 + 3 ^ 40 * 7882295 * 2
def baseEnd_7882295 : Nat := 4047405995531343218262491

theorem tailTrace_7882295 : CollatzResearch.WordTrace tailWord_7882295 prefixEnd_7882295 4047405995531343218262491 := by
  unfold tailWord_7882295
  simp only [CollatzResearch.WordTrace]
  refine ⟨287490916978798878655544339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191660611319199252437029559 287490916978798878655544339)
  ·
    refine ⟨431236375468198317983316509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287490916978798878655544339 431236375468198317983316509)
    ·
      refine ⟨161713640800574369243743691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431236375468198317983316509 161713640800574369243743691)
      ·
        refine ⟨242570461200861553865615537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161713640800574369243743691 242570461200861553865615537)
        ·
          refine ⟨181927845900646165399211653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242570461200861553865615537 181927845900646165399211653)
          ·
            refine ⟨34111471106371156012352185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181927845900646165399211653 34111471106371156012352185)
            ·
              refine ⟨25583603329778367009264139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34111471106371156012352185 25583603329778367009264139)
              ·
                refine ⟨38375404994667550513896209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25583603329778367009264139 38375404994667550513896209)
                ·
                  refine ⟨28781553746000662885422157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38375404994667550513896209 28781553746000662885422157)
                  ·
                    refine ⟨10793082654750248582033309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28781553746000662885422157 10793082654750248582033309)
                    ·
                      refine ⟨4047405995531343218262491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10793082654750248582033309 4047405995531343218262491)
                      ·
                        rfl

theorem cell23_7882295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_7882295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882295 prefixEnd_7882295 := by exact prefixLift 7882295
  have htrace : WordTrace (prefixWord ++ tailWord_7882295) baseStart_7882295 baseEnd_7882295 := by
    simpa [prefixWord, tailWord_7882295, baseEnd_7882295] using wordTrace_append hprefix tailTrace_7882295
  have hstable : (prefixWord ++ tailWord_7882295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882295).length < 2 ^ (prefixWord ++ tailWord_7882295).sum := by decide
  have hdescent : baseEnd_7882295 < baseStart_7882295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882296 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 2, 2, 2]
def baseStart_7882296 : Nat := 118140960795 + 7882296 * 2 ^ 59
def prefixEnd_7882296 : Nat := 4983230072969 + 3 ^ 40 * 7882296 * 2
def baseEnd_7882296 : Nat := 4047406509011997714349987

theorem tailTrace_7882296 : CollatzResearch.WordTrace tailWord_7882296 prefixEnd_7882296 4047406509011997714349987 := by
  unfold tailWord_7882296
  simp only [CollatzResearch.WordTrace]
  refine ⟨143745476725897627913165371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191660635634530170550887161 143745476725897627913165371)
  ·
    refine ⟨215618215088846441869748057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143745476725897627913165371 215618215088846441869748057)
    ·
      refine ⟨161713661316634831402311043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215618215088846441869748057 161713661316634831402311043)
      ·
        refine ⟨242570491974952247103466565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161713661316634831402311043 242570491974952247103466565)
        ·
          refine ⟨45481967245303546331899981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242570491974952247103466565 45481967245303546331899981)
          ·
            refine ⟨17055737716988829874462493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45481967245303546331899981 17055737716988829874462493)
            ·
              refine ⟨6395901643870811202923435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17055737716988829874462493 6395901643870811202923435)
              ·
                refine ⟨9593852465806216804385153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6395901643870811202923435 9593852465806216804385153)
                ·
                  refine ⟨7195389349354662603288865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9593852465806216804385153 7195389349354662603288865)
                  ·
                    refine ⟨5396542012015996952466649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7195389349354662603288865 5396542012015996952466649)
                    ·
                      refine ⟨4047406509011997714349987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5396542012015996952466649 4047406509011997714349987)
                      ·
                        rfl

theorem cell23_7882296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_7882296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882296 prefixEnd_7882296 := by exact prefixLift 7882296
  have htrace : WordTrace (prefixWord ++ tailWord_7882296) baseStart_7882296 baseEnd_7882296 := by
    simpa [prefixWord, tailWord_7882296, baseEnd_7882296] using wordTrace_append hprefix tailTrace_7882296
  have hstable : (prefixWord ++ tailWord_7882296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882296).length < 2 ^ (prefixWord ++ tailWord_7882296).sum := by decide
  have hdescent : baseEnd_7882296 < baseStart_7882296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882298 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_7882298 : Nat := 118140960795 + 7882298 * 2 ^ 59
def prefixEnd_7882298 : Nat := 4983230072969 + 3 ^ 40 * 7882298 * 2
def baseEnd_7882298 : Nat := 1349135845324435568841659

theorem tailTrace_7882298 : CollatzResearch.WordTrace tailWord_7882298 prefixEnd_7882298 1349135845324435568841659 := by
  unfold tailWord_7882298
  simp only [CollatzResearch.WordTrace]
  refine ⟨71872756599447002541975887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191660684265192006778602365 71872756599447002541975887)
  ·
    refine ⟨107809134899170503812963831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71872756599447002541975887 107809134899170503812963831)
    ·
      refine ⟨161713702348755755719445747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107809134899170503812963831 161713702348755755719445747)
      ·
        refine ⟨242570553523133633579168621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161713702348755755719445747 242570553523133633579168621)
        ·
          refine ⟨90963957571175112592188233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242570553523133633579168621 90963957571175112592188233)
          ·
            refine ⟨68222968178381334444141175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90963957571175112592188233 68222968178381334444141175)
            ·
              refine ⟨102334452267572001666211763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68222968178381334444141175 102334452267572001666211763)
              ·
                refine ⟨153501678401358002499317645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102334452267572001666211763 153501678401358002499317645)
                ·
                  refine ⟨57563129400509250937244117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153501678401358002499317645 57563129400509250937244117)
                  ·
                    refine ⟨1349135845324435568841659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57563129400509250937244117 1349135845324435568841659)
                    ·
                      rfl

theorem cell23_7882298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_7882298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882298 prefixEnd_7882298 := by exact prefixLift 7882298
  have htrace : WordTrace (prefixWord ++ tailWord_7882298) baseStart_7882298 baseEnd_7882298 := by
    simpa [prefixWord, tailWord_7882298, baseEnd_7882298] using wordTrace_append hprefix tailTrace_7882298
  have hstable : (prefixWord ++ tailWord_7882298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882298).length < 2 ^ (prefixWord ++ tailWord_7882298).sum := by decide
  have hdescent : baseEnd_7882298 < baseStart_7882298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882332 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7882332 : Nat := 118140960795 + 7882332 * 2 ^ 59
def prefixEnd_7882332 : Nat := 4983230072969 + 3 ^ 40 * 7882332 * 2
def baseEnd_7882332 : Nat := 1349141664771853191166607

theorem tailTrace_7882332 : CollatzResearch.WordTrace tailWord_7882332 prefixEnd_7882332 1349141664771853191166607 := by
  unfold tailWord_7882332
  simp only [CollatzResearch.WordTrace]
  refine ⟨143746133239832416987320625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191661510986443222649760833 143746133239832416987320625)
  ·
    refine ⟨107809599929874312740490469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143746133239832416987320625 107809599929874312740490469)
    ·
      refine ⟨20214299986851433638841963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107809599929874312740490469 20214299986851433638841963)
      ·
        refine ⟨30321449980277150458262945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20214299986851433638841963 30321449980277150458262945)
        ·
          refine ⟨22741087485207862843697209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30321449980277150458262945 22741087485207862843697209)
          ·
            refine ⟨17055815613905897132772907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22741087485207862843697209 17055815613905897132772907)
            ·
              refine ⟨25583723420858845699159361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17055815613905897132772907 25583723420858845699159361)
              ·
                refine ⟨19187792565644134274369521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25583723420858845699159361 19187792565644134274369521)
                ·
                  refine ⟨14390844424233100705777141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19187792565644134274369521 14390844424233100705777141)
                  ·
                    refine ⟨1349141664771853191166607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14390844424233100705777141 1349141664771853191166607)
                    ·
                      rfl

theorem cell23_7882332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7882332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882332 prefixEnd_7882332 := by exact prefixLift 7882332
  have htrace : WordTrace (prefixWord ++ tailWord_7882332) baseStart_7882332 baseEnd_7882332 := by
    simpa [prefixWord, tailWord_7882332, baseEnd_7882332] using wordTrace_append hprefix tailTrace_7882332
  have hstable : (prefixWord ++ tailWord_7882332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882332).length < 2 ^ (prefixWord ++ tailWord_7882332).sum := by decide
  have hdescent : baseEnd_7882332 < baseStart_7882332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882392 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 6]
def baseStart_7882392 : Nat := 118140960795 + 7882392 * 2 ^ 59
def prefixEnd_7882392 : Nat := 4983230072969 + 3 ^ 40 * 7882392 * 2
def baseEnd_7882392 : Nat := 449717311461647704305505

theorem tailTrace_7882392 : CollatzResearch.WordTrace tailWord_7882392 prefixEnd_7882392 449717311461647704305505 := by
  unfold tailWord_7882392
  simp only [CollatzResearch.WordTrace]
  refine ⟨143747227429723732110912715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191662969906298309481216953 143747227429723732110912715)
  ·
    refine ⟨215620841144585598166369073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143747227429723732110912715 215620841144585598166369073)
    ·
      refine ⟨161715630858439198624776805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215620841144585598166369073 161715630858439198624776805)
      ·
        refine ⟨30321680785957349742145651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161715630858439198624776805 30321680785957349742145651)
        ·
          refine ⟨45482521178936024613218477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30321680785957349742145651 45482521178936024613218477)
          ·
            refine ⟨17055945442101009229956929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45482521178936024613218477 17055945442101009229956929)
            ·
              refine ⟨12791959081575756922467697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17055945442101009229956929 12791959081575756922467697)
              ·
                refine ⟨9593969311181817691850773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12791959081575756922467697 9593969311181817691850773)
                ·
                  refine ⟨449717311461647704305505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9593969311181817691850773 449717311461647704305505)
                  ·
                    rfl

theorem cell23_7882392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 6].length) (baseStart_7882392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882392 prefixEnd_7882392 := by exact prefixLift 7882392
  have htrace : WordTrace (prefixWord ++ tailWord_7882392) baseStart_7882392 baseEnd_7882392 := by
    simpa [prefixWord, tailWord_7882392, baseEnd_7882392] using wordTrace_append hprefix tailTrace_7882392
  have hstable : (prefixWord ++ tailWord_7882392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882392).length < 2 ^ (prefixWord ++ tailWord_7882392).sum := by decide
  have hdescent : baseEnd_7882392 < baseStart_7882392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882396 : List Nat := [2, 2, 3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_7882396 : Nat := 118140960795 + 7882396 * 2 ^ 59
def prefixEnd_7882396 : Nat := 4983230072969 + 3 ^ 40 * 7882396 * 2
def baseEnd_7882396 : Nat := 1349152619025815774366509

theorem tailTrace_7882396 : CollatzResearch.WordTrace tailWord_7882396 prefixEnd_7882396 1349152619025815774366509 := by
  unfold tailWord_7882396
  simp only [CollatzResearch.WordTrace]
  refine ⟨143747300375716486452485521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191663067167621981936647361 143747300375716486452485521)
  ·
    refine ⟨107810475281787364839364141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143747300375716486452485521 107810475281787364839364141)
    ·
      refine ⟨40428928230670261814761553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107810475281787364839364141 40428928230670261814761553)
      ·
        refine ⟨30321696173002696361071165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40428928230670261814761553 30321696173002696361071165)
        ·
          refine ⟨11370636064876011135401687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30321696173002696361071165 11370636064876011135401687)
          ·
            refine ⟨17055954097314016703102531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11370636064876011135401687 17055954097314016703102531)
            ·
              refine ⟨25583931145971025054653797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17055954097314016703102531 25583931145971025054653797)
              ·
                refine ⟨4796987089869567197747587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25583931145971025054653797 4796987089869567197747587)
                ·
                  refine ⟨7195480634804350796621381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796987089869567197747587 7195480634804350796621381)
                  ·
                    refine ⟨1349152619025815774366509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7195480634804350796621381 1349152619025815774366509)
                    ·
                      rfl

theorem cell23_7882396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_7882396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882396 prefixEnd_7882396 := by exact prefixLift 7882396
  have htrace : WordTrace (prefixWord ++ tailWord_7882396) baseStart_7882396 baseEnd_7882396 := by
    simpa [prefixWord, tailWord_7882396, baseEnd_7882396] using wordTrace_append hprefix tailTrace_7882396
  have hstable : (prefixWord ++ tailWord_7882396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882396).length < 2 ^ (prefixWord ++ tailWord_7882396).sum := by decide
  have hdescent : baseEnd_7882396 < baseStart_7882396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882405 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_7882405 : Nat := 118140960795 + 7882405 * 2 ^ 59
def prefixEnd_7882405 : Nat := 4983230072969 + 3 ^ 40 * 7882405 * 2
def baseEnd_7882405 : Nat := 1349154159467779262628995

theorem tailTrace_7882405 : CollatzResearch.WordTrace tailWord_7882405 prefixEnd_7882405 1349154159467779262628995 := by
  unfold tailWord_7882405
  simp only [CollatzResearch.WordTrace]
  refine ⟨287494929008400367442048669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191663286005600244961365779 287494929008400367442048669)
  ·
    refine ⟨107810598378150137790768251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287494929008400367442048669 107810598378150137790768251)
    ·
      refine ⟨161715897567225206686152377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107810598378150137790768251 161715897567225206686152377)
      ·
        refine ⟨121286923175418905014614283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161715897567225206686152377 121286923175418905014614283)
        ·
          refine ⟨181930384763128357521921425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121286923175418905014614283 181930384763128357521921425)
          ·
            refine ⟨136447788572346268141441069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181930384763128357521921425 136447788572346268141441069)
            ·
              refine ⟨51167920714629850553040401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136447788572346268141441069 51167920714629850553040401)
              ·
                refine ⟨38375940535972387914780301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51167920714629850553040401 38375940535972387914780301)
                ·
                  refine ⟨14390977700989645468042613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38375940535972387914780301 14390977700989645468042613)
                  ·
                    refine ⟨1349154159467779262628995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14390977700989645468042613 1349154159467779262628995)
                    ·
                      rfl

theorem cell23_7882405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_7882405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882405 prefixEnd_7882405 := by exact prefixLift 7882405
  have htrace : WordTrace (prefixWord ++ tailWord_7882405) baseStart_7882405 baseEnd_7882405 := by
    simpa [prefixWord, tailWord_7882405, baseEnd_7882405] using wordTrace_append hprefix tailTrace_7882405
  have hstable : (prefixWord ++ tailWord_7882405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882405).length < 2 ^ (prefixWord ++ tailWord_7882405).sum := by decide
  have hdescent : baseEnd_7882405 < baseStart_7882405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882455 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_7882455 : Nat := 118140960795 + 7882455 * 2 ^ 59
def prefixEnd_7882455 : Nat := 4983230072969 + 3 ^ 40 * 7882455 * 2
def baseEnd_7882455 : Nat := 4047488152436062592261755

theorem tailTrace_7882455 : CollatzResearch.WordTrace tailWord_7882455 prefixEnd_7882455 4047488152436062592261755 := by
  unfold tailWord_7882455
  simp only [CollatzResearch.WordTrace]
  refine ⟨287496752658219225981368819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191664501772146150654245879 287496752658219225981368819)
  ·
    refine ⟨431245128987328838972053229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287496752658219225981368819 431245128987328838972053229)
    ·
      refine ⟨161716923370248314614519961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431245128987328838972053229 161716923370248314614519961)
      ·
        refine ⟨121287692527686235960889971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161716923370248314614519961 121287692527686235960889971)
        ·
          refine ⟨181931538791529353941334957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121287692527686235960889971 181931538791529353941334957)
          ·
            refine ⟨68224327046823507728000609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181931538791529353941334957 68224327046823507728000609)
            ·
              refine ⟨51168245285117630796000457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68224327046823507728000609 51168245285117630796000457)
              ·
                refine ⟨38376183963838223097000343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51168245285117630796000457 38376183963838223097000343)
                ·
                  refine ⟨57564275945757334645500515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38376183963838223097000343 57564275945757334645500515)
                  ·
                    refine ⟨86346413918636001968250773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57564275945757334645500515 86346413918636001968250773)
                    ·
                      refine ⟨4047488152436062592261755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86346413918636001968250773 4047488152436062592261755)
                      ·
                        rfl

theorem cell23_7882455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_7882455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882455 prefixEnd_7882455 := by exact prefixLift 7882455
  have htrace : WordTrace (prefixWord ++ tailWord_7882455) baseStart_7882455 baseEnd_7882455 := by
    simpa [prefixWord, tailWord_7882455, baseEnd_7882455] using wordTrace_append hprefix tailTrace_7882455
  have hstable : (prefixWord ++ tailWord_7882455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882455).length < 2 ^ (prefixWord ++ tailWord_7882455).sum := by decide
  have hdescent : baseEnd_7882455 < baseStart_7882455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882472 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7882472 : Nat := 118140960795 + 7882472 * 2 ^ 59
def prefixEnd_7882472 : Nat := 4983230072969 + 3 ^ 40 * 7882472 * 2
def baseEnd_7882472 : Nat := 4047496881607189025749177

theorem tailTrace_7882472 : CollatzResearch.WordTrace tailWord_7882472 prefixEnd_7882472 4047496881607189025749177 := by
  unfold tailWord_7882472
  simp only [CollatzResearch.WordTrace]
  refine ⟨143748686349578818942368835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191664915132771758589825113 143748686349578818942368835)
  ·
    refine ⟨215623029524368228413553253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143748686349578818942368835 215623029524368228413553253)
    ·
      refine ⟨40429318035819042827541235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215623029524368228413553253 40429318035819042827541235)
      ·
        refine ⟨60643977053728564241311853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40429318035819042827541235 60643977053728564241311853)
        ·
          refine ⟨22741491395148211590491945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60643977053728564241311853 22741491395148211590491945)
          ·
            refine ⟨17056118546361158692868959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22741491395148211590491945 17056118546361158692868959)
            ·
              refine ⟨25584177819541738039303439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17056118546361158692868959 25584177819541738039303439)
              ·
                refine ⟨38376266729312607058955159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25584177819541738039303439 38376266729312607058955159)
                ·
                  refine ⟨57564400093968910588432739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38376266729312607058955159 57564400093968910588432739)
                  ·
                    refine ⟨86346600140953365882649109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57564400093968910588432739 86346600140953365882649109)
                    ·
                      refine ⟨4047496881607189025749177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86346600140953365882649109 4047496881607189025749177)
                      ·
                        rfl

theorem cell23_7882472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7882472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882472 prefixEnd_7882472 := by exact prefixLift 7882472
  have htrace : WordTrace (prefixWord ++ tailWord_7882472) baseStart_7882472 baseEnd_7882472 := by
    simpa [prefixWord, tailWord_7882472, baseEnd_7882472] using wordTrace_append hprefix tailTrace_7882472
  have hstable : (prefixWord ++ tailWord_7882472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882472).length < 2 ^ (prefixWord ++ tailWord_7882472).sum := by decide
  have hdescent : baseEnd_7882472 < baseStart_7882472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882479 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 3]
def baseStart_7882479 : Nat := 118140960795 + 7882479 * 2 ^ 59
def prefixEnd_7882479 : Nat := 4983230072969 + 3 ^ 40 * 7882479 * 2
def baseEnd_7882479 : Nat := 4047500475971770498361645

theorem tailTrace_7882479 : CollatzResearch.WordTrace tailWord_7882479 prefixEnd_7882479 4047500475971770498361645 := by
  unfold tailWord_7882479
  simp only [CollatzResearch.WordTrace]
  refine ⟨287497628010132278080242491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191665085340088185386828327 287497628010132278080242491)
  ·
    refine ⟨431246442015198417120363737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287497628010132278080242491 431246442015198417120363737)
    ·
      refine ⟨323434831511398812840272803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431246442015198417120363737 323434831511398812840272803)
      ·
        refine ⟨485152247267098219260409205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323434831511398812840272803 485152247267098219260409205)
        ·
          refine ⟨45483023181290458055663363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 485152247267098219260409205 45483023181290458055663363)
          ·
            refine ⟨68224534771935687083495045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45483023181290458055663363 68224534771935687083495045)
            ·
              refine ⟨12792100269737941328155321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68224534771935687083495045 12792100269737941328155321)
              ·
                refine ⟨9594075202303455996116491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12792100269737941328155321 9594075202303455996116491)
                ·
                  refine ⟨14391112803455183994174737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9594075202303455996116491 14391112803455183994174737)
                  ·
                    refine ⟨10793334602591387995631053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14391112803455183994174737 10793334602591387995631053)
                    ·
                      refine ⟨4047500475971770498361645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10793334602591387995631053 4047500475971770498361645)
                      ·
                        rfl

theorem cell23_7882479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 3].length) (baseStart_7882479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882479 prefixEnd_7882479 := by exact prefixLift 7882479
  have htrace : WordTrace (prefixWord ++ tailWord_7882479) baseStart_7882479 baseEnd_7882479 := by
    simpa [prefixWord, tailWord_7882479, baseEnd_7882479] using wordTrace_append hprefix tailTrace_7882479
  have hstable : (prefixWord ++ tailWord_7882479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882479).length < 2 ^ (prefixWord ++ tailWord_7882479).sum := by decide
  have hdescent : baseEnd_7882479 < baseStart_7882479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882492 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_7882492 : Nat := 118140960795 + 7882492 * 2 ^ 59
def prefixEnd_7882492 : Nat := 4983230072969 + 3 ^ 40 * 7882492 * 2
def baseEnd_7882492 : Nat := 4047507151220278947499085

theorem tailTrace_7882492 : CollatzResearch.WordTrace tailWord_7882492 prefixEnd_7882492 4047507151220278947499085 := by
  unfold tailWord_7882492
  simp only [CollatzResearch.WordTrace]
  refine ⟨143749051079542590650232865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191665401439390120866977153 143749051079542590650232865)
  ·
    refine ⟨107811788309656942987674649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143749051079542590650232865 107811788309656942987674649)
    ·
      refine ⟨80858841232242707240755987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107811788309656942987674649 80858841232242707240755987)
      ·
        refine ⟨121288261848364060861133981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80858841232242707240755987 121288261848364060861133981)
        ·
          refine ⟨45483098193136522822925243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121288261848364060861133981 45483098193136522822925243)
          ·
            refine ⟨68224647289704784234387865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45483098193136522822925243 68224647289704784234387865)
            ·
              refine ⟨51168485467278588175790899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68224647289704784234387865 51168485467278588175790899)
              ·
                refine ⟨76752728200917882263686349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51168485467278588175790899 76752728200917882263686349)
                ·
                  refine ⟨28782273075344205848882381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76752728200917882263686349 28782273075344205848882381)
                  ·
                    refine ⟨10793352403254077193330893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28782273075344205848882381 10793352403254077193330893)
                    ·
                      refine ⟨4047507151220278947499085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10793352403254077193330893 4047507151220278947499085)
                      ·
                        rfl

theorem cell23_7882492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_7882492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882492 prefixEnd_7882492 := by exact prefixLift 7882492
  have htrace : WordTrace (prefixWord ++ tailWord_7882492) baseStart_7882492 baseEnd_7882492 := by
    simpa [prefixWord, tailWord_7882492, baseEnd_7882492] using wordTrace_append hprefix tailTrace_7882492
  have hstable : (prefixWord ++ tailWord_7882492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882492).length < 2 ^ (prefixWord ++ tailWord_7882492).sum := by decide
  have hdescent : baseEnd_7882492 < baseStart_7882492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882505 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_7882505 : Nat := 118140960795 + 7882505 * 2 ^ 59
def prefixEnd_7882505 : Nat := 4983230072969 + 3 ^ 40 * 7882505 * 2
def baseEnd_7882505 : Nat := 4047513826468787396636525

theorem tailTrace_7882505 : CollatzResearch.WordTrace tailWord_7882505 prefixEnd_7882505 4047513826468787396636525 := by
  unfold tailWord_7882505
  simp only [CollatzResearch.WordTrace]
  refine ⟨287498576308038084520688969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191665717538692056347125979 287498576308038084520688969)
  ·
    refine ⟨215623932231028563390516727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287498576308038084520688969 215623932231028563390516727)
    ·
      refine ⟨323435898346542845085775091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215623932231028563390516727 323435898346542845085775091)
      ·
        refine ⟨485153847519814267628662637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323435898346542845085775091 485153847519814267628662637)
        ·
          refine ⟨181932692819930350360748489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485153847519814267628662637 181932692819930350360748489)
          ·
            refine ⟨136449519614947762770561367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181932692819930350360748489 136449519614947762770561367)
            ·
              refine ⟨204674279422421644155842051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136449519614947762770561367 204674279422421644155842051)
              ·
                refine ⟨307011419133632466233763077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204674279422421644155842051 307011419133632466233763077)
                ·
                  refine ⟨57564641087556087418830577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307011419133632466233763077 57564641087556087418830577)
                  ·
                    refine ⟨43173480815667065564122933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57564641087556087418830577 43173480815667065564122933)
                    ·
                      refine ⟨4047513826468787396636525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43173480815667065564122933 4047513826468787396636525)
                      ·
                        rfl

theorem cell23_7882505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_7882505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882505 prefixEnd_7882505 := by exact prefixLift 7882505
  have htrace : WordTrace (prefixWord ++ tailWord_7882505) baseStart_7882505 baseEnd_7882505 := by
    simpa [prefixWord, tailWord_7882505, baseEnd_7882505] using wordTrace_append hprefix tailTrace_7882505
  have hstable : (prefixWord ++ tailWord_7882505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882505).length < 2 ^ (prefixWord ++ tailWord_7882505).sum := by decide
  have hdescent : baseEnd_7882505 < baseStart_7882505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882536 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_7882536 : Nat := 118140960795 + 7882536 * 2 ^ 59
def prefixEnd_7882536 : Nat := 4983230072969 + 3 ^ 40 * 7882536 * 2
def baseEnd_7882536 : Nat := 4047529744369076775348883

theorem tailTrace_7882536 : CollatzResearch.WordTrace tailWord_7882536 prefixEnd_7882536 4047529744369076775348883 := by
  unfold tailWord_7882536
  simp only [CollatzResearch.WordTrace]
  refine ⟨143749853485462888407533731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191666471313950517876711641 143749853485462888407533731)
  ·
    refine ⟨215624780228194332611300597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143749853485462888407533731 215624780228194332611300597)
    ·
      refine ⟨20214823146393218682309431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215624780228194332611300597 20214823146393218682309431)
      ·
        refine ⟨30322234719589828023464147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20214823146393218682309431 30322234719589828023464147)
        ·
          refine ⟨45483352079384742035196221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30322234719589828023464147 45483352079384742035196221)
          ·
            refine ⟨17056257029769278263198583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45483352079384742035196221 17056257029769278263198583)
            ·
              refine ⟨25584385544653917394797875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17056257029769278263198583 25584385544653917394797875)
              ·
                refine ⟨38376578316980876092196813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25584385544653917394797875 38376578316980876092196813)
                ·
                  refine ⟨14391216868867828534573805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38376578316980876092196813 14391216868867828534573805)
                  ·
                    refine ⟨5396706325825435700465177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14391216868867828534573805 5396706325825435700465177)
                    ·
                      refine ⟨4047529744369076775348883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5396706325825435700465177 4047529744369076775348883)
                      ·
                        rfl

theorem cell23_7882536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_7882536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882536 prefixEnd_7882536 := by exact prefixLift 7882536
  have htrace : WordTrace (prefixWord ++ tailWord_7882536) baseStart_7882536 baseEnd_7882536 := by
    simpa [prefixWord, tailWord_7882536, baseEnd_7882536] using wordTrace_append hprefix tailTrace_7882536
  have hstable : (prefixWord ++ tailWord_7882536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882536).length < 2 ^ (prefixWord ++ tailWord_7882536).sum := by decide
  have hdescent : baseEnd_7882536 < baseStart_7882536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882552 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_7882552 : Nat := 118140960795 + 7882552 * 2 ^ 59
def prefixEnd_7882552 : Nat := 4983230072969 + 3 ^ 40 * 7882552 * 2
def baseEnd_7882552 : Nat := 4047537960059548712748809

theorem tailTrace_7882552 : CollatzResearch.WordTrace tailWord_7882552 prefixEnd_7882552 4047537960059548712748809 := by
  unfold tailWord_7882552
  simp only [CollatzResearch.WordTrace]
  refine ⟨143750145269433905773824955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191666860359245207698433273 143750145269433905773824955)
  ·
    refine ⟨215625217904150858660737433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143750145269433905773824955 215625217904150858660737433)
    ·
      refine ⟨161718913428113143995553075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215625217904150858660737433 161718913428113143995553075)
      ·
        refine ⟨242578370142169715993329613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161718913428113143995553075 242578370142169715993329613)
        ·
          refine ⟨90966888803313643497498605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242578370142169715993329613 90966888803313643497498605)
          ·
            refine ⟨34112583301242616311561977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90966888803313643497498605 34112583301242616311561977)
            ·
              refine ⟨25584437475931962233671483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34112583301242616311561977 25584437475931962233671483)
              ·
                refine ⟨38376656213897943350507225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25584437475931962233671483 38376656213897943350507225)
                ·
                  refine ⟨28782492160423457512880419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38376656213897943350507225 28782492160423457512880419)
                  ·
                    refine ⟨43173738240635186269320629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28782492160423457512880419 43173738240635186269320629)
                    ·
                      refine ⟨4047537960059548712748809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43173738240635186269320629 4047537960059548712748809)
                      ·
                        rfl

theorem cell23_7882552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_7882552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882552 prefixEnd_7882552 := by exact prefixLift 7882552
  have htrace : WordTrace (prefixWord ++ tailWord_7882552) baseStart_7882552 baseEnd_7882552 := by
    simpa [prefixWord, tailWord_7882552, baseEnd_7882552] using wordTrace_append hprefix tailTrace_7882552
  have hstable : (prefixWord ++ tailWord_7882552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882552).length < 2 ^ (prefixWord ++ tailWord_7882552).sum := by decide
  have hdescent : baseEnd_7882552 < baseStart_7882552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882566 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7882566 : Nat := 118140960795 + 7882566 * 2 ^ 59
def prefixEnd_7882566 : Nat := 4983230072969 + 3 ^ 40 * 7882566 * 2
def baseEnd_7882566 : Nat := 4047545148788711657973745

theorem tailTrace_7882566 : CollatzResearch.WordTrace tailWord_7882566 prefixEnd_7882566 4047545148788711657973745 := by
  unfold tailWord_7882566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984400036275534123083111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191667200773878061292439701 8984400036275534123083111)
  ·
    refine ⟨13476600054413301184624667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8984400036275534123083111 13476600054413301184624667)
    ·
      refine ⟨20214900081619951776937001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13476600054413301184624667 20214900081619951776937001)
      ·
        refine ⟨15161175061214963832702751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20214900081619951776937001 15161175061214963832702751)
        ·
          refine ⟨22741762591822445749054127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15161175061214963832702751 22741762591822445749054127)
          ·
            refine ⟨34112643887733668623581191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22741762591822445749054127 34112643887733668623581191)
            ·
              refine ⟨51168965831600502935371787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34112643887733668623581191 51168965831600502935371787)
              ·
                refine ⟨76753448747400754403057681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51168965831600502935371787 76753448747400754403057681)
                ·
                  refine ⟨57565086560550565802293261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76753448747400754403057681 57565086560550565802293261)
                  ·
                    refine ⟨21586907460206462175859973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57565086560550565802293261 21586907460206462175859973)
                    ·
                      refine ⟨4047545148788711657973745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21586907460206462175859973 4047545148788711657973745)
                      ·
                        rfl

theorem cell23_7882566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7882566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882566 prefixEnd_7882566 := by exact prefixLift 7882566
  have htrace : WordTrace (prefixWord ++ tailWord_7882566) baseStart_7882566 baseEnd_7882566 := by
    simpa [prefixWord, tailWord_7882566, baseEnd_7882566] using wordTrace_append hprefix tailTrace_7882566
  have hstable : (prefixWord ++ tailWord_7882566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882566).length < 2 ^ (prefixWord ++ tailWord_7882566).sum := by decide
  have hdescent : baseEnd_7882566 < baseStart_7882566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882606 : List Nat := [4, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_7882606 : Nat := 118140960795 + 7882606 * 2 ^ 59
def prefixEnd_7882606 : Nat := 4983230072969 + 3 ^ 40 * 7882606 * 2
def baseEnd_7882606 : Nat := 449729520890543500163729

theorem tailTrace_7882606 : CollatzResearch.WordTrace tailWord_7882606 prefixEnd_7882606 449729520890543500163729 := by
  unfold tailWord_7882606
  simp only [CollatzResearch.WordTrace]
  refine ⟨35937782510084022346264459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191668173387114785846743781 35937782510084022346264459)
  ·
    refine ⟨53906673765126033519396689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35937782510084022346264459 53906673765126033519396689)
    ·
      refine ⟨40430005323844525139547517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53906673765126033519396689 40430005323844525139547517)
      ·
        refine ⟨15161251996441696927330319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40430005323844525139547517 15161251996441696927330319)
        ·
          refine ⟨22741877994662545390995479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15161251996441696927330319 22741877994662545390995479)
          ·
            refine ⟨34112816991993818086493219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22741877994662545390995479 34112816991993818086493219)
            ·
              refine ⟨51169225487990727129739829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34112816991993818086493219 51169225487990727129739829)
              ·
                refine ⟨4797114889499130668413109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51169225487990727129739829 4797114889499130668413109)
                ·
                  refine ⟨449729520890543500163729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4797114889499130668413109 449729520890543500163729)
                  ·
                    rfl

theorem cell23_7882606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_7882606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882606 prefixEnd_7882606 := by exact prefixLift 7882606
  have htrace : WordTrace (prefixWord ++ tailWord_7882606) baseStart_7882606 baseEnd_7882606 := by
    simpa [prefixWord, tailWord_7882606, baseEnd_7882606] using wordTrace_append hprefix tailTrace_7882606
  have hstable : (prefixWord ++ tailWord_7882606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882606).length < 2 ^ (prefixWord ++ tailWord_7882606).sum := by decide
  have hdescent : baseEnd_7882606 < baseStart_7882606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882649 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 3, 4]
def baseStart_7882649 : Nat := 118140960795 + 7882649 * 2 ^ 59
def prefixEnd_7882649 : Nat := 4983230072969 + 3 ^ 40 * 7882649 * 2
def baseEnd_7882649 : Nat := 1349195922561011611078621

theorem tailTrace_7882649 : CollatzResearch.WordTrace tailWord_7882649 prefixEnd_7882649 1349195922561011611078621 := by
  unfold tailWord_7882649
  simp only [CollatzResearch.WordTrace]
  refine ⟨287503828419516397113931001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191669218946344264742620667 287503828419516397113931001)
  ·
    refine ⟨215627871314637297835448251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287503828419516397113931001 215627871314637297835448251)
    ·
      refine ⟨323441806971955946753172377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215627871314637297835448251 323441806971955946753172377)
      ·
        refine ⟨242581355228966960064879283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323441806971955946753172377 242581355228966960064879283)
        ·
          refine ⟨363872032843450440097318925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242581355228966960064879283 363872032843450440097318925)
          ·
            refine ⟨136452012316293915036494597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363872032843450440097318925 136452012316293915036494597)
            ·
              refine ⟨25584752309305109069342737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136452012316293915036494597 25584752309305109069342737)
              ·
                refine ⟨19188564231978831802007053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25584752309305109069342737 19188564231978831802007053)
                ·
                  refine ⟨7195711586992061925752645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19188564231978831802007053 7195711586992061925752645)
                  ·
                    refine ⟨1349195922561011611078621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7195711586992061925752645 1349195922561011611078621)
                    ·
                      rfl

theorem cell23_7882649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 4].length) (baseStart_7882649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882649 prefixEnd_7882649 := by exact prefixLift 7882649
  have htrace : WordTrace (prefixWord ++ tailWord_7882649) baseStart_7882649 baseEnd_7882649 := by
    simpa [prefixWord, tailWord_7882649, baseEnd_7882649] using wordTrace_append hprefix tailTrace_7882649
  have hstable : (prefixWord ++ tailWord_7882649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882649).length < 2 ^ (prefixWord ++ tailWord_7882649).sum := by decide
  have hdescent : baseEnd_7882649 < baseStart_7882649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882659 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 3]
def baseStart_7882659 : Nat := 118140960795 + 7882659 * 2 ^ 59
def prefixEnd_7882659 : Nat := 4983230072969 + 3 ^ 40 * 7882659 * 2
def baseEnd_7882659 : Nat := 4047592902489579794110817

theorem tailTrace_7882659 : CollatzResearch.WordTrace tailWord_7882659 prefixEnd_7882659 4047592902489579794110817 := by
  unfold tailWord_7882659
  simp only [CollatzResearch.WordTrace]
  refine ⟨287504193149480168821795031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191669462099653445881196687 287504193149480168821795031)
  ·
    refine ⟨431256289724220253232692547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287504193149480168821795031 431256289724220253232692547)
    ·
      refine ⟨646884434586330379849038821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431256289724220253232692547 646884434586330379849038821)
      ·
        refine ⟨121290831484936946221694779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 646884434586330379849038821 121290831484936946221694779)
        ·
          refine ⟨181936247227405419332542169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121290831484936946221694779 181936247227405419332542169)
          ·
            refine ⟨136452185420554064499406627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181936247227405419332542169 136452185420554064499406627)
            ·
              refine ⟨204678278130831096749109941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136452185420554064499406627 204678278130831096749109941)
              ·
                refine ⟨19188588574765415320229057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204678278130831096749109941 19188588574765415320229057)
                ·
                  refine ⟨14391441431074061490171793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19188588574765415320229057 14391441431074061490171793)
                  ·
                    refine ⟨10793581073305546117628845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14391441431074061490171793 10793581073305546117628845)
                    ·
                      refine ⟨4047592902489579794110817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10793581073305546117628845 4047592902489579794110817)
                      ·
                        rfl

theorem cell23_7882659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_7882659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882659 prefixEnd_7882659 := by exact prefixLift 7882659
  have htrace : WordTrace (prefixWord ++ tailWord_7882659) baseStart_7882659 baseEnd_7882659 := by
    simpa [prefixWord, tailWord_7882659, baseEnd_7882659] using wordTrace_append hprefix tailTrace_7882659
  have hstable : (prefixWord ++ tailWord_7882659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882659).length < 2 ^ (prefixWord ++ tailWord_7882659).sum := by decide
  have hdescent : baseEnd_7882659 < baseStart_7882659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882670 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7882670 : Nat := 118140960795 + 7882670 * 2 ^ 59
def prefixEnd_7882670 : Nat := 4983230072969 + 3 ^ 40 * 7882670 * 2
def baseEnd_7882670 : Nat := 1349199516925593083691089

theorem tailTrace_7882670 : CollatzResearch.WordTrace tailWord_7882670 prefixEnd_7882670 1349199516925593083691089 := by
  unfold tailWord_7882670
  simp only [CollatzResearch.WordTrace]
  refine ⟨35938074294055039712555683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191669729568293545133630309 35938074294055039712555683)
  ·
    refine ⟨53907111441082559568833525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35938074294055039712555683 53907111441082559568833525)
    ·
      refine ⟨5053791697601489959578143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53907111441082559568833525 5053791697601489959578143)
      ·
        refine ⟨7580687546402234939367215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5053791697601489959578143 7580687546402234939367215)
        ·
          refine ⟨11371031319603352409050823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7580687546402234939367215 11371031319603352409050823)
          ·
            refine ⟨17056546979405028613576235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11371031319603352409050823 17056546979405028613576235)
            ·
              refine ⟨25584820469107542920364353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17056546979405028613576235 25584820469107542920364353)
              ·
                refine ⟨19188615351830657190273265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25584820469107542920364353 19188615351830657190273265)
                ·
                  refine ⟨14391461513872992892704949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19188615351830657190273265 14391461513872992892704949)
                  ·
                    refine ⟨1349199516925593083691089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14391461513872992892704949 1349199516925593083691089)
                    ·
                      rfl

theorem cell23_7882670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7882670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882670 prefixEnd_7882670 := by exact prefixLift 7882670
  have htrace : WordTrace (prefixWord ++ tailWord_7882670) baseStart_7882670 baseEnd_7882670 := by
    simpa [prefixWord, tailWord_7882670, baseEnd_7882670] using wordTrace_append hprefix tailTrace_7882670
  have hstable : (prefixWord ++ tailWord_7882670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882670).length < 2 ^ (prefixWord ++ tailWord_7882670).sum := by decide
  have hdescent : baseEnd_7882670 < baseStart_7882670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882682 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_7882682 : Nat := 118140960795 + 7882682 * 2 ^ 59
def prefixEnd_7882682 : Nat := 4983230072969 + 3 ^ 40 * 7882682 * 2
def baseEnd_7882682 : Nat := 4047604712544633204123211

theorem tailTrace_7882682 : CollatzResearch.WordTrace tailWord_7882682 prefixEnd_7882682 4047604712544633204123211 := by
  unfold tailWord_7882682
  simp only [CollatzResearch.WordTrace]
  refine ⟨71876258007099210937470575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191670021352264562499921533 71876258007099210937470575)
  ·
    refine ⟨107814387010648816406205863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71876258007099210937470575 107814387010648816406205863)
    ·
      refine ⟨161721580515973224609308795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107814387010648816406205863 161721580515973224609308795)
      ·
        refine ⟨242582370773959836913963193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161721580515973224609308795 242582370773959836913963193)
        ·
          refine ⟨181936778080469877685472395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242582370773959836913963193 181936778080469877685472395)
          ·
            refine ⟨272905167120704816528208593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181936778080469877685472395 272905167120704816528208593)
            ·
              refine ⟨204678875340528612396156445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272905167120704816528208593 204678875340528612396156445)
              ·
                refine ⟨76754578252698229648558667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204678875340528612396156445 76754578252698229648558667)
                ·
                  refine ⟨115131867379047344472838001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76754578252698229648558667 115131867379047344472838001)
                  ·
                    refine ⟨86348900534285508354628501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115131867379047344472838001 86348900534285508354628501)
                    ·
                      refine ⟨4047604712544633204123211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86348900534285508354628501 4047604712544633204123211)
                      ·
                        rfl

theorem cell23_7882682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_7882682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882682 prefixEnd_7882682 := by exact prefixLift 7882682
  have htrace : WordTrace (prefixWord ++ tailWord_7882682) baseStart_7882682 baseEnd_7882682 := by
    simpa [prefixWord, tailWord_7882682, baseEnd_7882682] using wordTrace_append hprefix tailTrace_7882682
  have hstable : (prefixWord ++ tailWord_7882682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882682).length < 2 ^ (prefixWord ++ tailWord_7882682).sum := by decide
  have hdescent : baseEnd_7882682 < baseStart_7882682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882696 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 6]
def baseStart_7882696 : Nat := 118140960795 + 7882696 * 2 ^ 59
def prefixEnd_7882696 : Nat := 4983230072969 + 3 ^ 40 * 7882696 * 2
def baseEnd_7882696 : Nat := 449734655697088461038683

theorem tailTrace_7882696 : CollatzResearch.WordTrace tailWord_7882696 prefixEnd_7882696 449734655697088461038683 := by
  unfold tailWord_7882696
  simp only [CollatzResearch.WordTrace]
  refine ⟨143752771325173062070445971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191670361766897416093927961 143752771325173062070445971)
  ·
    refine ⟨215629156987759593105668957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143752771325173062070445971 215629156987759593105668957)
    ·
      refine ⟨80860933870409847414625859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215629156987759593105668957 80860933870409847414625859)
      ·
        refine ⟨121291400805614771121938789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80860933870409847414625859 121291400805614771121938789)
        ·
          refine ⟨22742137651052769585363523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121291400805614771121938789 22742137651052769585363523)
          ·
            refine ⟨34113206476579154378045285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22742137651052769585363523 34113206476579154378045285)
            ·
              refine ⟨6396226214358591445883491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34113206476579154378045285 6396226214358591445883491)
              ·
                refine ⟨9594339321537887168825237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6396226214358591445883491 9594339321537887168825237)
                ·
                  refine ⟨449734655697088461038683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9594339321537887168825237 449734655697088461038683)
                  ·
                    rfl

theorem cell23_7882696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 6].length) (baseStart_7882696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882696 prefixEnd_7882696 := by exact prefixLift 7882696
  have htrace : WordTrace (prefixWord ++ tailWord_7882696) baseStart_7882696 baseEnd_7882696 := by
    simpa [prefixWord, tailWord_7882696, baseEnd_7882696] using wordTrace_append hprefix tailTrace_7882696
  have hstable : (prefixWord ++ tailWord_7882696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882696).length < 2 ^ (prefixWord ++ tailWord_7882696).sum := by decide
  have hdescent : baseEnd_7882696 < baseStart_7882696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882710 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_7882710 : Nat := 118140960795 + 7882710 * 2 ^ 59
def prefixEnd_7882710 : Nat := 4983230072969 + 3 ^ 40 * 7882710 * 2
def baseEnd_7882710 : Nat := 4047619090002959094573083

theorem tailTrace_7882710 : CollatzResearch.WordTrace tailWord_7882710 prefixEnd_7882710 4047619090002959094573083 := by
  unfold tailWord_7882710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17969128329518462783243849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191670702181530269687934389 17969128329518462783243849)
  ·
    refine ⟨13476846247138847087432887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17969128329518462783243849 13476846247138847087432887)
    ·
      refine ⟨20215269370708270631149331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13476846247138847087432887 20215269370708270631149331)
      ·
        refine ⟨30322904056062405946723997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20215269370708270631149331 30322904056062405946723997)
        ·
          refine ⟨11371089021023402230021499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30322904056062405946723997 11371089021023402230021499)
          ·
            refine ⟨17056633531535103345032249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11371089021023402230021499 17056633531535103345032249)
            ·
              refine ⟨12792475148651327508774187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17056633531535103345032249 12792475148651327508774187)
              ·
                refine ⟨19188712722976991263161281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12792475148651327508774187 19188712722976991263161281)
                ·
                  refine ⟨14391534542232743447370961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19188712722976991263161281 14391534542232743447370961)
                  ·
                    refine ⟨10793650906674557585528221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14391534542232743447370961 10793650906674557585528221)
                    ·
                      refine ⟨4047619090002959094573083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10793650906674557585528221 4047619090002959094573083)
                      ·
                        rfl

theorem cell23_7882710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_7882710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882710 prefixEnd_7882710 := by exact prefixLift 7882710
  have htrace : WordTrace (prefixWord ++ tailWord_7882710) baseStart_7882710 baseEnd_7882710 := by
    simpa [prefixWord, tailWord_7882710, baseEnd_7882710] using wordTrace_append hprefix tailTrace_7882710
  have hstable : (prefixWord ++ tailWord_7882710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882710).length < 2 ^ (prefixWord ++ tailWord_7882710).sum := by decide
  have hdescent : baseEnd_7882710 < baseStart_7882710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882739 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 4, 4]
def baseStart_7882739 : Nat := 118140960795 + 7882739 * 2 ^ 59
def prefixEnd_7882739 : Nat := 4983230072969 + 3 ^ 40 * 7882739 * 2
def baseEnd_7882739 : Nat := 1349211326980646493703483

theorem tailTrace_7882739 : CollatzResearch.WordTrace tailWord_7882739 prefixEnd_7882739 1349211326980646493703483 := by
  unfold tailWord_7882739
  simp only [CollatzResearch.WordTrace]
  refine ⟨287507110989190342484707271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191671407326126894989804847 287507110989190342484707271)
  ·
    refine ⟨431260666483785513727060907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287507110989190342484707271 431260666483785513727060907)
    ·
      refine ⟨646890999725678270590591361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431260666483785513727060907 646890999725678270590591361)
      ·
        refine ⟨485168249794258702942943521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646890999725678270590591361 485168249794258702942943521)
        ·
          refine ⟨363876187345694027207207641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485168249794258702942943521 363876187345694027207207641)
          ·
            refine ⟨272907140509270520405405731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363876187345694027207207641 272907140509270520405405731)
            ·
              refine ⟨409360710763905780608108597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272907140509270520405405731 409360710763905780608108597)
              ·
                refine ⟨38377566634116166932010181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409360710763905780608108597 38377566634116166932010181)
                ·
                  refine ⟨7195793743896781299751909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38377566634116166932010181 7195793743896781299751909)
                  ·
                    refine ⟨1349211326980646493703483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7195793743896781299751909 1349211326980646493703483)
                    ·
                      rfl

theorem cell23_7882739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 4].length) (baseStart_7882739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882739 prefixEnd_7882739 := by exact prefixLift 7882739
  have htrace : WordTrace (prefixWord ++ tailWord_7882739) baseStart_7882739 baseEnd_7882739 := by
    simpa [prefixWord, tailWord_7882739, baseEnd_7882739] using wordTrace_append hprefix tailTrace_7882739
  have hstable : (prefixWord ++ tailWord_7882739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882739).length < 2 ^ (prefixWord ++ tailWord_7882739).sum := by decide
  have hdescent : baseEnd_7882739 < baseStart_7882739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882749 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_7882749 : Nat := 118140960795 + 7882749 * 2 ^ 59
def prefixEnd_7882749 : Nat := 4983230072969 + 3 ^ 40 * 7882749 * 2
def baseEnd_7882749 : Nat := 4047639115748484441985403

theorem tailTrace_7882749 : CollatzResearch.WordTrace tailWord_7882749 prefixEnd_7882749 4047639115748484441985403 := by
  unfold tailWord_7882749
  simp only [CollatzResearch.WordTrace]
  refine ⟨287507475719154114192571301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191671650479436076128380867 287507475719154114192571301)
  ·
    refine ⟨53907651697341396411107119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287507475719154114192571301 53907651697341396411107119)
    ·
      refine ⟨80861477546012094616660679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53907651697341396411107119 80861477546012094616660679)
      ·
        refine ⟨121292216319018141924991019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80861477546012094616660679 121292216319018141924991019)
        ·
          refine ⟨181938324478527212887486529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121292216319018141924991019 181938324478527212887486529)
          ·
            refine ⟨136453743358895409665614897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181938324478527212887486529 136453743358895409665614897)
            ·
              refine ⟨102340307519171557249211173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136453743358895409665614897 102340307519171557249211173)
              ·
                refine ⟨19188807659844666984227095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102340307519171557249211173 19188807659844666984227095)
                ·
                  refine ⟨28783211489767000476340643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19188807659844666984227095 28783211489767000476340643)
                  ·
                    refine ⟨43174817234650500714510965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28783211489767000476340643 43174817234650500714510965)
                    ·
                      refine ⟨4047639115748484441985403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43174817234650500714510965 4047639115748484441985403)
                      ·
                        rfl

theorem cell23_7882749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_7882749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882749 prefixEnd_7882749 := by exact prefixLift 7882749
  have htrace : WordTrace (prefixWord ++ tailWord_7882749) baseStart_7882749 baseEnd_7882749 := by
    simpa [prefixWord, tailWord_7882749, baseEnd_7882749] using wordTrace_append hprefix tailTrace_7882749
  have hstable : (prefixWord ++ tailWord_7882749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882749).length < 2 ^ (prefixWord ++ tailWord_7882749).sum := by decide
  have hdescent : baseEnd_7882749 < baseStart_7882749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882752 : List Nat := [2, 1, 1, 2, 1, 1, 1, 14]
def baseStart_7882752 : Nat := 118140960795 + 7882752 * 2 ^ 59
def prefixEnd_7882752 : Nat := 4983230072969 + 3 ^ 40 * 7882752 * 2
def baseEnd_7882752 : Nat := 149912616895942515935107

theorem tailTrace_7882752 : CollatzResearch.WordTrace tailWord_7882752 prefixEnd_7882752 149912616895942515935107 := by
  unfold tailWord_7882752
  simp only [CollatzResearch.WordTrace]
  refine ⟨143753792569071622852465255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191671723425428830469953673 143753792569071622852465255)
  ·
    refine ⟨215630688853607434278697883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143753792569071622852465255 215630688853607434278697883)
    ·
      refine ⟨323446033280411151418046825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215630688853607434278697883 323446033280411151418046825)
      ·
        refine ⟨242584524960308363563535119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323446033280411151418046825 242584524960308363563535119)
        ·
          refine ⟨363876787440462545345302679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242584524960308363563535119 363876787440462545345302679)
          ·
            refine ⟨545815181160693818017954019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363876787440462545345302679 545815181160693818017954019)
            ·
              refine ⟨818722771741040727026931029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545815181160693818017954019 818722771741040727026931029)
              ·
                refine ⟨149912616895942515935107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 818722771741040727026931029 149912616895942515935107)
                ·
                  rfl

theorem cell23_7882752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 14].length) (baseStart_7882752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882752 prefixEnd_7882752 := by exact prefixLift 7882752
  have htrace : WordTrace (prefixWord ++ tailWord_7882752) baseStart_7882752 baseEnd_7882752 := by
    simpa [prefixWord, tailWord_7882752, baseEnd_7882752] using wordTrace_append hprefix tailTrace_7882752
  have hstable : (prefixWord ++ tailWord_7882752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882752).length < 2 ^ (prefixWord ++ tailWord_7882752).sum := by decide
  have hdescent : baseEnd_7882752 < baseStart_7882752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882763 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 3, 2, 2]
def baseStart_7882763 : Nat := 118140960795 + 7882763 * 2 ^ 59
def prefixEnd_7882763 : Nat := 4983230072969 + 3 ^ 40 * 7882763 * 2
def baseEnd_7882763 : Nat := 4047646304477647387210339

theorem tailTrace_7882763 : CollatzResearch.WordTrace tailWord_7882763 prefixEnd_7882763 4047646304477647387210339 := by
  unfold tailWord_7882763
  simp only [CollatzResearch.WordTrace]
  refine ⟨287507986341103394583580943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191671990894068929722387295 287507986341103394583580943)
  ·
    refine ⟨431261979511655091875371415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287507986341103394583580943 431261979511655091875371415)
    ·
      refine ⟨646892969267482637813057123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431261979511655091875371415 646892969267482637813057123)
      ·
        refine ⟨970339453901223956719585685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646892969267482637813057123 970339453901223956719585685)
        ·
          refine ⟨45484661901619872971230579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 970339453901223956719585685 45484661901619872971230579)
          ·
            refine ⟨68226992852429809456845869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45484661901619872971230579 68226992852429809456845869)
            ·
              refine ⟨25585122319661178546317201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68226992852429809456845869 25585122319661178546317201)
              ·
                refine ⟨19188841739745883909737901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25585122319661178546317201 19188841739745883909737901)
                ·
                  refine ⟨7195815652404706466151713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19188841739745883909737901 7195815652404706466151713)
                  ·
                    refine ⟨5396861739303529849613785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7195815652404706466151713 5396861739303529849613785)
                    ·
                      refine ⟨4047646304477647387210339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5396861739303529849613785 4047646304477647387210339)
                      ·
                        rfl

theorem cell23_7882763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 2, 2].length) (baseStart_7882763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882763 prefixEnd_7882763 := by exact prefixLift 7882763
  have htrace : WordTrace (prefixWord ++ tailWord_7882763) baseStart_7882763 baseEnd_7882763 := by
    simpa [prefixWord, tailWord_7882763, baseEnd_7882763] using wordTrace_append hprefix tailTrace_7882763
  have hstable : (prefixWord ++ tailWord_7882763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882763).length < 2 ^ (prefixWord ++ tailWord_7882763).sum := by decide
  have hdescent : baseEnd_7882763 < baseStart_7882763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882766 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_7882766 : Nat := 118140960795 + 7882766 * 2 ^ 59
def prefixEnd_7882766 : Nat := 4983230072969 + 3 ^ 40 * 7882766 * 2
def baseEnd_7882766 : Nat := 4047647844919610875472825

theorem tailTrace_7882766 : CollatzResearch.WordTrace tailWord_7882766 prefixEnd_7882766 4047647844919610875472825 := by
  unfold tailWord_7882766
  simp only [CollatzResearch.WordTrace]
  refine ⟨35938511970011565761992519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191672063840061684063960101 35938511970011565761992519)
  ·
    refine ⟨53907767955017348642988779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35938511970011565761992519 53907767955017348642988779)
    ·
      refine ⟨80861651932526022964483169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53907767955017348642988779 80861651932526022964483169)
      ·
        refine ⟨60646238949394517223362377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80861651932526022964483169 60646238949394517223362377)
        ·
          refine ⟨45484679212045887917521783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60646238949394517223362377 45484679212045887917521783)
          ·
            refine ⟨68227018818068831876282675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45484679212045887917521783 68227018818068831876282675)
            ·
              refine ⟨102340528227103247814424013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68227018818068831876282675 102340528227103247814424013)
              ·
                refine ⟨38377698085163717930409005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102340528227103247814424013 38377698085163717930409005)
                ·
                  refine ⟨14391636781936394223903377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38377698085163717930409005 14391636781936394223903377)
                  ·
                    refine ⟨10793727586452295667927533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14391636781936394223903377 10793727586452295667927533)
                    ·
                      refine ⟨4047647844919610875472825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10793727586452295667927533 4047647844919610875472825)
                      ·
                        rfl

theorem cell23_7882766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_7882766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882766 prefixEnd_7882766 := by exact prefixLift 7882766
  have htrace : WordTrace (prefixWord ++ tailWord_7882766) baseStart_7882766 baseEnd_7882766 := by
    simpa [prefixWord, tailWord_7882766, baseEnd_7882766] using wordTrace_append hprefix tailTrace_7882766
  have hstable : (prefixWord ++ tailWord_7882766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882766).length < 2 ^ (prefixWord ++ tailWord_7882766).sum := by decide
  have hdescent : baseEnd_7882766 < baseStart_7882766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882779 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 3]
def baseStart_7882779 : Nat := 118140960795 + 7882779 * 2 ^ 59
def prefixEnd_7882779 : Nat := 4983230072969 + 3 ^ 40 * 7882779 * 2
def baseEnd_7882779 : Nat := 4047654520168119324610265

theorem tailTrace_7882779 : CollatzResearch.WordTrace tailWord_7882779 prefixEnd_7882779 4047654520168119324610265 := by
  unfold tailWord_7882779
  simp only [CollatzResearch.WordTrace]
  refine ⟨287508569909045429316163391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191672379939363619544108927 287508569909045429316163391)
  ·
    refine ⟨431262854863568143974245087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287508569909045429316163391 431262854863568143974245087)
    ·
      refine ⟨646894282295352215961367631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431262854863568143974245087 646894282295352215961367631)
      ·
        refine ⟨970341423443028323942051447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646894282295352215961367631 970341423443028323942051447)
        ·
          refine ⟨1455512135164542485913077171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970341423443028323942051447 1455512135164542485913077171)
          ·
            refine ⟨2183268202746813728869615757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455512135164542485913077171 2183268202746813728869615757)
            ·
              refine ⟨818725576030055148326105909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2183268202746813728869615757 818725576030055148326105909)
              ·
                refine ⟨76755522752817670155572429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 818725576030055148326105909 76755522752817670155572429)
                ·
                  refine ⟨28783321032306626308339661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76755522752817670155572429 28783321032306626308339661)
                  ·
                    refine ⟨10793745387114984865627373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28783321032306626308339661 10793745387114984865627373)
                    ·
                      refine ⟨4047654520168119324610265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10793745387114984865627373 4047654520168119324610265)
                      ·
                        rfl

theorem cell23_7882779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 3].length) (baseStart_7882779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882779 prefixEnd_7882779 := by exact prefixLift 7882779
  have htrace : WordTrace (prefixWord ++ tailWord_7882779) baseStart_7882779 baseEnd_7882779 := by
    simpa [prefixWord, tailWord_7882779, baseEnd_7882779] using wordTrace_append hprefix tailTrace_7882779
  have hstable : (prefixWord ++ tailWord_7882779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882779).length < 2 ^ (prefixWord ++ tailWord_7882779).sum := by decide
  have hdescent : baseEnd_7882779 < baseStart_7882779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882780 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_7882780 : Nat := 118140960795 + 7882780 * 2 ^ 59
def prefixEnd_7882780 : Nat := 4983230072969 + 3 ^ 40 * 7882780 * 2
def baseEnd_7882780 : Nat := 4047655033648773820697761

theorem tailTrace_7882780 : CollatzResearch.WordTrace tailWord_7882780 prefixEnd_7882780 4047655033648773820697761 := by
  unfold tailWord_7882780
  simp only [CollatzResearch.WordTrace]
  refine ⟨143754303191020903243474897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191672404254694537657966529 143754303191020903243474897)
  ·
    refine ⟨107815727393265677432606173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143754303191020903243474897 107815727393265677432606173)
    ·
      refine ⟨40430897772474629037227315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107815727393265677432606173 40430897772474629037227315)
      ·
        refine ⟨60646346658711943555840973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40430897772474629037227315 60646346658711943555840973)
        ·
          refine ⟨22742379997016978833440365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60646346658711943555840973 22742379997016978833440365)
          ·
            refine ⟨8528392498881367062540137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22742379997016978833440365 8528392498881367062540137)
            ·
              refine ⟨6396294374161025296905103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8528392498881367062540137 6396294374161025296905103)
              ·
                refine ⟨9594441561241537945357655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6396294374161025296905103 9594441561241537945357655)
                ·
                  refine ⟨14391662341862306918036483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9594441561241537945357655 14391662341862306918036483)
                  ·
                    refine ⟨21587493512793460377054725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14391662341862306918036483 21587493512793460377054725)
                    ·
                      refine ⟨4047655033648773820697761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21587493512793460377054725 4047655033648773820697761)
                      ·
                        rfl

theorem cell23_7882780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_7882780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882780 prefixEnd_7882780 := by exact prefixLift 7882780
  have htrace : WordTrace (prefixWord ++ tailWord_7882780) baseStart_7882780 baseEnd_7882780 := by
    simpa [prefixWord, tailWord_7882780, baseEnd_7882780] using wordTrace_append hprefix tailTrace_7882780
  have hstable : (prefixWord ++ tailWord_7882780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882780).length < 2 ^ (prefixWord ++ tailWord_7882780).sum := by decide
  have hdescent : baseEnd_7882780 < baseStart_7882780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882839 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_7882839 : Nat := 118140960795 + 7882839 * 2 ^ 59
def prefixEnd_7882839 : Nat := 4983230072969 + 3 ^ 40 * 7882839 * 2
def baseEnd_7882839 : Nat := 4047685329007389089859989

theorem tailTrace_7882839 : CollatzResearch.WordTrace tailWord_7882839 prefixEnd_7882839 4047685329007389089859989 := by
  unfold tailWord_7882839
  simp only [CollatzResearch.WordTrace]
  refine ⟨287510758288828059563347571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191673838859218706375565047 287510758288828059563347571)
  ·
    refine ⟨431266137433242089345021357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287510758288828059563347571 431266137433242089345021357)
    ·
      refine ⟨161724801537465783504383009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431266137433242089345021357 161724801537465783504383009)
      ·
        refine ⟨121293601153099337628287257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161724801537465783504383009 121293601153099337628287257)
        ·
          refine ⟨90970200864824503221215443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121293601153099337628287257 90970200864824503221215443)
          ·
            refine ⟨136455301297236754831823165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90970200864824503221215443 136455301297236754831823165)
            ·
              refine ⟨51170737986463783061933687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136455301297236754831823165 51170737986463783061933687)
              ·
                refine ⟨76756106979695674592900531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51170737986463783061933687 76756106979695674592900531)
                ·
                  refine ⟨115134160469543511889350797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76756106979695674592900531 115134160469543511889350797)
                  ·
                    refine ⟨43175310176078816958506549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115134160469543511889350797 43175310176078816958506549)
                    ·
                      refine ⟨4047685329007389089859989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43175310176078816958506549 4047685329007389089859989)
                      ·
                        rfl

theorem cell23_7882839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_7882839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882839 prefixEnd_7882839 := by exact prefixLift 7882839
  have htrace : WordTrace (prefixWord ++ tailWord_7882839) baseStart_7882839 baseEnd_7882839 := by
    simpa [prefixWord, tailWord_7882839, baseEnd_7882839] using wordTrace_append hprefix tailTrace_7882839
  have hstable : (prefixWord ++ tailWord_7882839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882839).length < 2 ^ (prefixWord ++ tailWord_7882839).sum := by decide
  have hdescent : baseEnd_7882839 < baseStart_7882839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882913 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_7882913 : Nat := 118140960795 + 7882913 * 2 ^ 59
def prefixEnd_7882913 : Nat := 4983230072969 + 3 ^ 40 * 7882913 * 2
def baseEnd_7882913 : Nat := 4047723326575821800334649

theorem tailTrace_7882913 : CollatzResearch.WordTrace tailWord_7882913 prefixEnd_7882913 4047723326575821800334649 := by
  unfold tailWord_7882913
  simp only [CollatzResearch.WordTrace]
  refine ⟨287513457290559970201541393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191675638193706646801027595 287513457290559970201541393)
  ·
    refine ⟨215635092967919977651156045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287513457290559970201541393 215635092967919977651156045)
    ·
      refine ⟨80863159862969991619183517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215635092967919977651156045 80863159862969991619183517)
      ·
        refine ⟨30323684948613746857193819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80863159862969991619183517 30323684948613746857193819)
        ·
          refine ⟨45485527422920620285790729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30323684948613746857193819 45485527422920620285790729)
          ·
            refine ⟨34114145567190465214343047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45485527422920620285790729 34114145567190465214343047)
            ·
              refine ⟨51171218350785697821514571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34114145567190465214343047 51171218350785697821514571)
              ·
                refine ⟨76756827526178546732271857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51171218350785697821514571 76756827526178546732271857)
                ·
                  refine ⟨57567620644633910049203893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76756827526178546732271857 57567620644633910049203893)
                  ·
                    refine ⟨5396964435434429067112865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57567620644633910049203893 5396964435434429067112865)
                    ·
                      refine ⟨4047723326575821800334649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5396964435434429067112865 4047723326575821800334649)
                      ·
                        rfl

theorem cell23_7882913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_7882913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882913 prefixEnd_7882913 := by exact prefixLift 7882913
  have htrace : WordTrace (prefixWord ++ tailWord_7882913) baseStart_7882913 baseEnd_7882913 := by
    simpa [prefixWord, tailWord_7882913, baseEnd_7882913] using wordTrace_append hprefix tailTrace_7882913
  have hstable : (prefixWord ++ tailWord_7882913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882913).length < 2 ^ (prefixWord ++ tailWord_7882913).sum := by decide
  have hdescent : baseEnd_7882913 < baseStart_7882913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882940 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_7882940 : Nat := 118140960795 + 7882940 * 2 ^ 59
def prefixEnd_7882940 : Nat := 4983230072969 + 3 ^ 40 * 7882940 * 2
def baseEnd_7882940 : Nat := 1349245730184497731565675

theorem tailTrace_7882940 : CollatzResearch.WordTrace tailWord_7882940 prefixEnd_7882940 1349245730184497731565675 := by
  unfold tailWord_7882940
  simp only [CollatzResearch.WordTrace]
  refine ⟨143757221030731076906387137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191676294707641435875182849 143757221030731076906387137)
  ·
    refine ⟨107817915773048307679790353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143757221030731076906387137 107817915773048307679790353)
    ·
      refine ⟨80863436829786230759842765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107817915773048307679790353 80863436829786230759842765)
      ·
        refine ⟨30323788811169836534941037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80863436829786230759842765 30323788811169836534941037)
        ·
          refine ⟨11371420804188688700602889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30323788811169836534941037 11371420804188688700602889)
          ·
            refine ⟨8528565603141516525452167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11371420804188688700602889 8528565603141516525452167)
            ·
              refine ⟨12792848404712274788178251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8528565603141516525452167 12792848404712274788178251)
              ·
                refine ⟨19189272607068412182267377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12792848404712274788178251 19189272607068412182267377)
                ·
                  refine ⟨14391954455301309136700533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19189272607068412182267377 14391954455301309136700533)
                  ·
                    refine ⟨1349245730184497731565675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14391954455301309136700533 1349245730184497731565675)
                    ·
                      rfl

theorem cell23_7882940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_7882940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882940 prefixEnd_7882940 := by exact prefixLift 7882940
  have htrace : WordTrace (prefixWord ++ tailWord_7882940) baseStart_7882940 baseEnd_7882940 := by
    simpa [prefixWord, tailWord_7882940, baseEnd_7882940] using wordTrace_append hprefix tailTrace_7882940
  have hstable : (prefixWord ++ tailWord_7882940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882940).length < 2 ^ (prefixWord ++ tailWord_7882940).sum := by decide
  have hdescent : baseEnd_7882940 < baseStart_7882940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882970 : List Nat := [3, 1, 1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_7882970 : Nat := 118140960795 + 7882970 * 2 ^ 59
def prefixEnd_7882970 : Nat := 4983230072969 + 3 ^ 40 * 7882970 * 2
def baseEnd_7882970 : Nat := 1349250864991042692440629

theorem tailTrace_7882970 : CollatzResearch.WordTrace tailWord_7882970 prefixEnd_7882970 1349250864991042692440629 := by
  unfold tailWord_7882970
  simp only [CollatzResearch.WordTrace]
  refine ⟨71878884062838367234091591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191677024167568979290910909 71878884062838367234091591)
  ·
    refine ⟨107818326094257550851137387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71878884062838367234091591 107818326094257550851137387)
    ·
      refine ⟨161727489141386326276706081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107818326094257550851137387 161727489141386326276706081)
      ·
        refine ⟨121295616856039744707529561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161727489141386326276706081 121295616856039744707529561)
        ·
          refine ⟨90971712642029808530647171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121295616856039744707529561 90971712642029808530647171)
          ·
            refine ⟨136457568963044712795970757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90971712642029808530647171 136457568963044712795970757)
            ·
              refine ⟨25585794180570883649244517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136457568963044712795970757 25585794180570883649244517)
              ·
                refine ⟨4797336408857040684233347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25585794180570883649244517 4797336408857040684233347)
                ·
                  refine ⟨7196004613285561026350021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797336408857040684233347 7196004613285561026350021)
                  ·
                    refine ⟨1349250864991042692440629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7196004613285561026350021 1349250864991042692440629)
                    ·
                      rfl

theorem cell23_7882970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_7882970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882970 prefixEnd_7882970 := by exact prefixLift 7882970
  have htrace : WordTrace (prefixWord ++ tailWord_7882970) baseStart_7882970 baseEnd_7882970 := by
    simpa [prefixWord, tailWord_7882970, baseEnd_7882970] using wordTrace_append hprefix tailTrace_7882970
  have hstable : (prefixWord ++ tailWord_7882970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882970).length < 2 ^ (prefixWord ++ tailWord_7882970).sum := by decide
  have hdescent : baseEnd_7882970 < baseStart_7882970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882986 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_7882986 : Nat := 118140960795 + 7882986 * 2 ^ 59
def prefixEnd_7882986 : Nat := 4983230072969 + 3 ^ 40 * 7882986 * 2
def baseEnd_7882986 : Nat := 4047760810663600014721813

theorem tailTrace_7882986 : CollatzResearch.WordTrace tailWord_7882986 prefixEnd_7882986 4047760810663600014721813 := by
  unfold tailWord_7882986
  simp only [CollatzResearch.WordTrace]
  refine ⟨71879029954823875917237203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191677413212863669112632541 71879029954823875917237203)
  ·
    refine ⟨107818544932235813875855805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71879029954823875917237203 107818544932235813875855805)
    ·
      refine ⟨40431954349588430203445927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107818544932235813875855805 40431954349588430203445927)
      ·
        refine ⟨60647931524382645305168891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40431954349588430203445927 60647931524382645305168891)
        ·
          refine ⟨90971897286573967957753337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60647931524382645305168891 90971897286573967957753337)
          ·
            refine ⟨68228922964930475968315003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90971897286573967957753337 68228922964930475968315003)
            ·
              refine ⟨102343384447395713952472505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68228922964930475968315003 102343384447395713952472505)
              ·
                refine ⟨76757538335546785464354379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102343384447395713952472505 76757538335546785464354379)
                ·
                  refine ⟨115136307503320178196531569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76757538335546785464354379 115136307503320178196531569)
                  ·
                    refine ⟨86352230627490133647398677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115136307503320178196531569 86352230627490133647398677)
                    ·
                      refine ⟨4047760810663600014721813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86352230627490133647398677 4047760810663600014721813)
                      ·
                        rfl

theorem cell23_7882986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_7882986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7882986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7882986 prefixEnd_7882986 := by exact prefixLift 7882986
  have htrace : WordTrace (prefixWord ++ tailWord_7882986) baseStart_7882986 baseEnd_7882986 := by
    simpa [prefixWord, tailWord_7882986, baseEnd_7882986] using wordTrace_append hprefix tailTrace_7882986
  have hstable : (prefixWord ++ tailWord_7882986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882986).length < 2 ^ (prefixWord ++ tailWord_7882986).sum := by decide
  have hdescent : baseEnd_7882986 < baseStart_7882986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883003 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 8, 3, 2]
def baseStart_7883003 : Nat := 118140960795 + 7883003 * 2 ^ 59
def prefixEnd_7883003 : Nat := 4983230072969 + 3 ^ 40 * 7883003 * 2
def baseEnd_7883003 : Nat := 4047769539834726448209235

theorem tailTrace_7883003 : CollatzResearch.WordTrace tailWord_7883003 prefixEnd_7883003 4047769539834726448209235 := by
  unfold tailWord_7883003
  simp only [CollatzResearch.WordTrace]
  refine ⟨287516739860233915572317663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191677826573489277048211775 287516739860233915572317663)
  ·
    refine ⟨431275109790350873358476495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287516739860233915572317663 431275109790350873358476495)
    ·
      refine ⟨646912664685526310037714743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431275109790350873358476495 646912664685526310037714743)
      ·
        refine ⟨970368997028289465056572115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646912664685526310037714743 970368997028289465056572115)
        ·
          refine ⟨1455553495542434197584858173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970368997028289465056572115 1455553495542434197584858173)
          ·
            refine ⟨545832560828412824094321815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1455553495542434197584858173 545832560828412824094321815)
            ·
              refine ⟨818748841242619236141482723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545832560828412824094321815 818748841242619236141482723)
              ·
                refine ⟨1228123261863928854212224085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818748841242619236141482723 1228123261863928854212224085)
                ·
                  refine ⟨14392069474967916260299501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1228123261863928854212224085 14392069474967916260299501)
                  ·
                    refine ⟨5397026053112968597612313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14392069474967916260299501 5397026053112968597612313)
                    ·
                      refine ⟨4047769539834726448209235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5397026053112968597612313 4047769539834726448209235)
                      ·
                        rfl

theorem cell23_7883003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 3, 2].length) (baseStart_7883003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883003 prefixEnd_7883003 := by exact prefixLift 7883003
  have htrace : WordTrace (prefixWord ++ tailWord_7883003) baseStart_7883003 baseEnd_7883003 := by
    simpa [prefixWord, tailWord_7883003, baseEnd_7883003] using wordTrace_append hprefix tailTrace_7883003
  have hstable : (prefixWord ++ tailWord_7883003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883003).length < 2 ^ (prefixWord ++ tailWord_7883003).sum := by decide
  have hdescent : baseEnd_7883003 < baseStart_7883003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883020 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 2, 3, 2]
def baseStart_7883020 : Nat := 118140960795 + 7883020 * 2 ^ 59
def prefixEnd_7883020 : Nat := 4983230072969 + 3 ^ 40 * 7883020 * 2
def baseEnd_7883020 : Nat := 4047778269005852881696657

theorem tailTrace_7883020 : CollatzResearch.WordTrace tailWord_7883020 prefixEnd_7883020 4047778269005852881696657 := by
  unfold tailWord_7883020
  simp only [CollatzResearch.WordTrace]
  refine ⟨143758679950586163737843257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191678239934114884983791009 143758679950586163737843257)
  ·
    refine ⟨107819009962939622803382443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143758679950586163737843257 107819009962939622803382443)
    ·
      refine ⟨161728514944409434205073665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107819009962939622803382443 161728514944409434205073665)
      ·
        refine ⟨121296386208307075653805249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161728514944409434205073665 121296386208307075653805249)
        ·
          refine ⟨90972289656230306740353937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121296386208307075653805249 90972289656230306740353937)
          ·
            refine ⟨68229217242172730055265453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90972289656230306740353937 68229217242172730055265453)
            ·
              refine ⟨25585956465814773770724545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68229217242172730055265453 25585956465814773770724545)
              ·
                refine ⟨19189467349361080328043409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25585956465814773770724545 19189467349361080328043409)
                ·
                  refine ⟨14392100512020810246032557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19189467349361080328043409 14392100512020810246032557)
                  ·
                    refine ⟨5397037692007803842262209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14392100512020810246032557 5397037692007803842262209)
                    ·
                      refine ⟨4047778269005852881696657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5397037692007803842262209 4047778269005852881696657)
                      ·
                        rfl

theorem cell23_7883020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_7883020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883020 prefixEnd_7883020 := by exact prefixLift 7883020
  have htrace : WordTrace (prefixWord ++ tailWord_7883020) baseStart_7883020 baseEnd_7883020 := by
    simpa [prefixWord, tailWord_7883020, baseEnd_7883020] using wordTrace_append hprefix tailTrace_7883020
  have hstable : (prefixWord ++ tailWord_7883020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883020).length < 2 ^ (prefixWord ++ tailWord_7883020).sum := by decide
  have hdescent : baseEnd_7883020 < baseStart_7883020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883060 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_7883060 : Nat := 118140960795 + 7883060 * 2 ^ 59
def prefixEnd_7883060 : Nat := 4983230072969 + 3 ^ 40 * 7883060 * 2
def baseEnd_7883060 : Nat := 1349266269410677575065491

theorem tailTrace_7883060 : CollatzResearch.WordTrace tailWord_7883060 prefixEnd_7883060 1349266269410677575065491 := by
  unfold tailWord_7883060
  simp only [CollatzResearch.WordTrace]
  refine ⟨143759409410513707153571317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191679212547351609538095089 143759409410513707153571317)
  ·
    refine ⟨13477444632235660045647311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143759409410513707153571317 13477444632235660045647311)
    ·
      refine ⟨20216166948353490068470967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13477444632235660045647311 20216166948353490068470967)
      ·
        refine ⟨30324250422530235102706451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20216166948353490068470967 30324250422530235102706451)
        ·
          refine ⟨45486375633795352654059677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30324250422530235102706451 45486375633795352654059677)
          ·
            refine ⟨17057390862673257245272379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45486375633795352654059677 17057390862673257245272379)
            ·
              refine ⟨25586086294009885867908569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17057390862673257245272379 25586086294009885867908569)
              ·
                refine ⟨19189564720507414400931427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25586086294009885867908569 19189564720507414400931427)
                ·
                  refine ⟨28784347080761121601397141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19189564720507414400931427 28784347080761121601397141)
                  ·
                    refine ⟨1349266269410677575065491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28784347080761121601397141 1349266269410677575065491)
                    ·
                      rfl

theorem cell23_7883060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_7883060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883060 prefixEnd_7883060 := by exact prefixLift 7883060
  have htrace : WordTrace (prefixWord ++ tailWord_7883060) baseStart_7883060 baseEnd_7883060 := by
    simpa [prefixWord, tailWord_7883060, baseEnd_7883060] using wordTrace_append hprefix tailTrace_7883060
  have hstable : (prefixWord ++ tailWord_7883060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883060).length < 2 ^ (prefixWord ++ tailWord_7883060).sum := by decide
  have hdescent : baseEnd_7883060 < baseStart_7883060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883070 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_7883070 : Nat := 118140960795 + 7883070 * 2 ^ 59
def prefixEnd_7883070 : Nat := 4983230072969 + 3 ^ 40 * 7883070 * 2
def baseEnd_7883070 : Nat := 4047803943038577686071427

theorem tailTrace_7883070 : CollatzResearch.WordTrace tailWord_7883070 prefixEnd_7883070 4047803943038577686071427 := by
  unfold tailWord_7883070
  simp only [CollatzResearch.WordTrace]
  refine ⟨35939897943873898251875833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191679455700660790676671109 35939897943873898251875833)
  ·
    refine ⟨26954923457905423688906875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35939897943873898251875833 26954923457905423688906875)
    ·
      refine ⟨40432385186858135533360313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26954923457905423688906875 40432385186858135533360313)
      ·
        refine ⟨30324288890143601650020235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40432385186858135533360313 30324288890143601650020235)
        ·
          refine ⟨45486433335215402475030353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30324288890143601650020235 45486433335215402475030353)
          ·
            refine ⟨34114825001411551856272765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45486433335215402475030353 34114825001411551856272765)
            ·
              refine ⟨12793059375529331946102287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34114825001411551856272765 12793059375529331946102287)
              ·
                refine ⟨19189589063293997919153431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12793059375529331946102287 19189589063293997919153431)
                ·
                  refine ⟨28784383594940996878730147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19189589063293997919153431 28784383594940996878730147)
                  ·
                    refine ⟨43176575392411495318095221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28784383594940996878730147 43176575392411495318095221)
                    ·
                      refine ⟨4047803943038577686071427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43176575392411495318095221 4047803943038577686071427)
                      ·
                        rfl

theorem cell23_7883070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_7883070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883070 prefixEnd_7883070 := by exact prefixLift 7883070
  have htrace : WordTrace (prefixWord ++ tailWord_7883070) baseStart_7883070 baseEnd_7883070 := by
    simpa [prefixWord, tailWord_7883070, baseEnd_7883070] using wordTrace_append hprefix tailTrace_7883070
  have hstable : (prefixWord ++ tailWord_7883070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883070).length < 2 ^ (prefixWord ++ tailWord_7883070).sum := by decide
  have hdescent : baseEnd_7883070 < baseStart_7883070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883073 : List Nat := [1, 2, 5, 2, 2, 11]
def baseStart_7883073 : Nat := 118140960795 + 7883073 * 2 ^ 59
def prefixEnd_7883073 : Nat := 4983230072969 + 3 ^ 40 * 7883073 * 2
def baseEnd_7883073 : Nat := 16657635734487823762691

theorem tailTrace_7883073 : CollatzResearch.WordTrace tailWord_7883073 prefixEnd_7883073 16657635734487823762691 := by
  unfold tailWord_7883073
  simp only [CollatzResearch.WordTrace]
  refine ⟨287519292969980317527365873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191679528646653545018243915 287519292969980317527365873)
  ·
    refine ⟨215639469727485238145524405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287519292969980317527365873 215639469727485238145524405)
    ·
      refine ⟨20216200286951741076142913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215639469727485238145524405 20216200286951741076142913)
      ·
        refine ⟨15162150215213805807107185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20216200286951741076142913 15162150215213805807107185)
        ·
          refine ⟨11371612661410354355330389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15162150215213805807107185 11371612661410354355330389)
          ·
            refine ⟨16657635734487823762691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11371612661410354355330389 16657635734487823762691)
            ·
              rfl

theorem cell23_7883073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 11].length) (baseStart_7883073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883073 prefixEnd_7883073 := by exact prefixLift 7883073
  have htrace : WordTrace (prefixWord ++ tailWord_7883073) baseStart_7883073 baseEnd_7883073 := by
    simpa [prefixWord, tailWord_7883073, baseEnd_7883073] using wordTrace_append hprefix tailTrace_7883073
  have hstable : (prefixWord ++ tailWord_7883073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883073).length < 2 ^ (prefixWord ++ tailWord_7883073).sum := by decide
  have hdescent : baseEnd_7883073 < baseStart_7883073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883084 : List Nat := [2, 2, 1, 3, 2, 1, 3, 4, 1, 2, 2]
def baseStart_7883084 : Nat := 118140960795 + 7883084 * 2 ^ 59
def prefixEnd_7883084 : Nat := 4983230072969 + 3 ^ 40 * 7883084 * 2
def baseEnd_7883084 : Nat := 4047811131767740631296363

theorem tailTrace_7883084 : CollatzResearch.WordTrace tailWord_7883084 prefixEnd_7883084 4047811131767740631296363 := by
  unfold tailWord_7883084
  simp only [CollatzResearch.WordTrace]
  refine ⟨143759847086470233203008153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191679796115293644270677537 143759847086470233203008153)
  ·
    refine ⟨107819885314852674902256115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143759847086470233203008153 107819885314852674902256115)
    ·
      refine ⟨161729827972279012353384173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107819885314852674902256115 161729827972279012353384173)
      ·
        refine ⟨60648685489604629632519065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161729827972279012353384173 60648685489604629632519065)
        ·
          refine ⟨45486514117203472224389299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60648685489604629632519065 45486514117203472224389299)
          ·
            refine ⟨68229771175805208336583949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45486514117203472224389299 68229771175805208336583949)
            ·
              refine ⟨25586164190926953126218981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68229771175805208336583949 25586164190926953126218981)
              ·
                refine ⟨4797405785798803711166059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25586164190926953126218981 4797405785798803711166059)
                ·
                  refine ⟨7196108678698205566749089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797405785798803711166059 7196108678698205566749089)
                  ·
                    refine ⟨5397081509023654175061817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7196108678698205566749089 5397081509023654175061817)
                    ·
                      refine ⟨4047811131767740631296363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5397081509023654175061817 4047811131767740631296363)
                      ·
                        rfl

theorem cell23_7883084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_7883084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883084 prefixEnd_7883084 := by exact prefixLift 7883084
  have htrace : WordTrace (prefixWord ++ tailWord_7883084) baseStart_7883084 baseEnd_7883084 := by
    simpa [prefixWord, tailWord_7883084, baseEnd_7883084] using wordTrace_append hprefix tailTrace_7883084
  have hstable : (prefixWord ++ tailWord_7883084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883084).length < 2 ^ (prefixWord ++ tailWord_7883084).sum := by decide
  have hdescent : baseEnd_7883084 < baseStart_7883084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883133 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_7883133 : Nat := 118140960795 + 7883133 * 2 ^ 59
def prefixEnd_7883133 : Nat := 4983230072969 + 3 ^ 40 * 7883133 * 2
def baseEnd_7883133 : Nat := 1349278764106603646527879

theorem tailTrace_7883133 : CollatzResearch.WordTrace tailWord_7883133 prefixEnd_7883133 1349278764106603646527879 := by
  unfold tailWord_7883133
  simp only [CollatzResearch.WordTrace]
  refine ⟨287521481349762947774550053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191680987566508631849700035 287521481349762947774550053)
  ·
    refine ⟨53910277753080552707728135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287521481349762947774550053 53910277753080552707728135)
    ·
      refine ⟨80865416629620829061592203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53910277753080552707728135 80865416629620829061592203)
      ·
        refine ⟨121298124944431243592388305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80865416629620829061592203 121298124944431243592388305)
        ·
          refine ⟨90973593708323432694291229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121298124944431243592388305 90973593708323432694291229)
          ·
            refine ⟨34115097640621287260359211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90973593708323432694291229 34115097640621287260359211)
            ·
              refine ⟨51172646460931930890538817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34115097640621287260359211 51172646460931930890538817)
              ·
                refine ⟨38379484845698948167904113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51172646460931930890538817 38379484845698948167904113)
                ·
                  refine ⟨28784613634274211125928085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38379484845698948167904113 28784613634274211125928085)
                  ·
                    refine ⟨1349278764106603646527879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28784613634274211125928085 1349278764106603646527879)
                    ·
                      rfl

theorem cell23_7883133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_7883133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883133 prefixEnd_7883133 := by exact prefixLift 7883133
  have htrace : WordTrace (prefixWord ++ tailWord_7883133) baseStart_7883133 baseEnd_7883133 := by
    simpa [prefixWord, tailWord_7883133, baseEnd_7883133] using wordTrace_append hprefix tailTrace_7883133
  have hstable : (prefixWord ++ tailWord_7883133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883133).length < 2 ^ (prefixWord ++ tailWord_7883133).sum := by decide
  have hdescent : baseEnd_7883133 < baseStart_7883133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883150 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_7883150 : Nat := 118140960795 + 7883150 * 2 ^ 59
def prefixEnd_7883150 : Nat := 4983230072969 + 3 ^ 40 * 7883150 * 2
def baseEnd_7883150 : Nat := 1349281673830312457690353

theorem tailTrace_7883150 : CollatzResearch.WordTrace tailWord_7883150 prefixEnd_7883150 1349281673830312457690353 := by
  unfold tailWord_7883150
  simp only [CollatzResearch.WordTrace]
  refine ⟨35940262673837669959739863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191681400927134239785279269 35940262673837669959739863)
  ·
    refine ⟨53910394010756504939609795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35940262673837669959739863 53910394010756504939609795)
    ·
      refine ⟨80865591016134757409414693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53910394010756504939609795 80865591016134757409414693)
      ·
        refine ⟨15162298315525267014265255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80865591016134757409414693 15162298315525267014265255)
        ·
          refine ⟨22743447473287900521397883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15162298315525267014265255 22743447473287900521397883)
          ·
            refine ⟨34115171209931850782096825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22743447473287900521397883 34115171209931850782096825)
            ·
              refine ⟨25586378407448888086572619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34115171209931850782096825 25586378407448888086572619)
              ·
                refine ⟨38379567611173332129858929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25586378407448888086572619 38379567611173332129858929)
                ·
                  refine ⟨28784675708379999097394197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38379567611173332129858929 28784675708379999097394197)
                  ·
                    refine ⟨1349281673830312457690353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28784675708379999097394197 1349281673830312457690353)
                    ·
                      rfl

theorem cell23_7883150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_7883150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883150 prefixEnd_7883150 := by exact prefixLift 7883150
  have htrace : WordTrace (prefixWord ++ tailWord_7883150) baseStart_7883150 baseEnd_7883150 := by
    simpa [prefixWord, tailWord_7883150, baseEnd_7883150] using wordTrace_append hprefix tailTrace_7883150
  have hstable : (prefixWord ++ tailWord_7883150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883150).length < 2 ^ (prefixWord ++ tailWord_7883150).sum := by decide
  have hdescent : baseEnd_7883150 < baseStart_7883150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883158 : List Nat := [5, 3, 1, 2, 2, 1, 2, 7]
def baseStart_7883158 : Nat := 118140960795 + 7883158 * 2 ^ 59
def prefixEnd_7883158 : Nat := 4983230072969 + 3 ^ 40 * 7883158 * 2
def baseEnd_7883158 : Nat := 149920338123561975621149

theorem tailTrace_7883158 : CollatzResearch.WordTrace tailWord_7883158 prefixEnd_7883158 149920338123561975621149 := by
  unfold tailWord_7883158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17970149573417023565263133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191681595449781584696140085 17970149573417023565263133)
  ·
    refine ⟨6738806090031383836973675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17970149573417023565263133 6738806090031383836973675)
    ·
      refine ⟨10108209135047075755460513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738806090031383836973675 10108209135047075755460513)
      ·
        refine ⟨7581156851285306816595385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10108209135047075755460513 7581156851285306816595385)
        ·
          refine ⟨5685867638463980112446539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7581156851285306816595385 5685867638463980112446539)
          ·
            refine ⟨8528801457695970168669809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685867638463980112446539 8528801457695970168669809)
            ·
              refine ⟨6396601093271977626502357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8528801457695970168669809 6396601093271977626502357)
              ·
                refine ⟨149920338123561975621149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6396601093271977626502357 149920338123561975621149)
                ·
                  rfl

theorem cell23_7883158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_7883158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883158 prefixEnd_7883158 := by exact prefixLift 7883158
  have htrace : WordTrace (prefixWord ++ tailWord_7883158) baseStart_7883158 baseEnd_7883158 := by
    simpa [prefixWord, tailWord_7883158, baseEnd_7883158] using wordTrace_append hprefix tailTrace_7883158
  have hstable : (prefixWord ++ tailWord_7883158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883158).length < 2 ^ (prefixWord ++ tailWord_7883158).sum := by decide
  have hdescent : baseEnd_7883158 < baseStart_7883158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883200 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 2, 5, 2]
def baseStart_7883200 : Nat := 118140960795 + 7883200 * 2 ^ 59
def prefixEnd_7883200 : Nat := 4983230072969 + 3 ^ 40 * 7883200 * 2
def baseEnd_7883200 : Nat := 4047870695523662177445829

theorem tailTrace_7883200 : CollatzResearch.WordTrace tailWord_7883200 prefixEnd_7883200 4047870695523662177445829 := by
  unfold tailWord_7883200
  simp only [CollatzResearch.WordTrace]
  refine ⟨143761962520260109108619527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191682616693680145478159369 143761962520260109108619527)
  ·
    refine ⟨215642943780390163662929291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143761962520260109108619527 215642943780390163662929291)
    ·
      refine ⟨323464415670585245494393937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215642943780390163662929291 323464415670585245494393937)
      ·
        refine ⟨242598311752938934120795453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323464415670585245494393937 242598311752938934120795453)
        ·
          refine ⟨90974366907352100295298295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242598311752938934120795453 90974366907352100295298295)
          ·
            refine ⟨136461550361028150442947443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90974366907352100295298295 136461550361028150442947443)
            ·
              refine ⟨204692325541542225664421165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136461550361028150442947443 204692325541542225664421165)
              ·
                refine ⟨76759622078078334624157937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204692325541542225664421165 76759622078078334624157937)
                ·
                  refine ⟨57569716558558750968118453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76759622078078334624157937 57569716558558750968118453)
                  ·
                    refine ⟨5397160927364882903261105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57569716558558750968118453 5397160927364882903261105)
                    ·
                      refine ⟨4047870695523662177445829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5397160927364882903261105 4047870695523662177445829)
                      ·
                        rfl

theorem cell23_7883200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_7883200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883200 prefixEnd_7883200 := by exact prefixLift 7883200
  have htrace : WordTrace (prefixWord ++ tailWord_7883200) baseStart_7883200 baseEnd_7883200 := by
    simpa [prefixWord, tailWord_7883200, baseEnd_7883200] using wordTrace_append hprefix tailTrace_7883200
  have hstable : (prefixWord ++ tailWord_7883200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883200).length < 2 ^ (prefixWord ++ tailWord_7883200).sum := by decide
  have hdescent : baseEnd_7883200 < baseStart_7883200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
