import V185TrunkScan23Chunk0471

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2791804 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_2791804 : Nat := 118140960795 + 2791804 * 2 ^ 59
def prefixEnd_2791804 : Nat := 4983230072969 + 3 ^ 40 * 2791804 * 2
def baseEnd_2791804 : Nat := 1433537345144900287710733

theorem tailTrace_2791804 : CollatzResearch.WordTrace tailWord_2791804 prefixEnd_2791804 1433537345144900287710733 := by
  unfold tailWord_2791804
  simp only [CollatzResearch.WordTrace]
  refine ⟨50912728588889192504075233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67883638118518923338766977 50912728588889192504075233)
  ·
    refine ⟨38184546441666894378056425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50912728588889192504075233 38184546441666894378056425)
    ·
      refine ⟨28638409831250170783542319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38184546441666894378056425 28638409831250170783542319)
      ·
        refine ⟨42957614746875256175313479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28638409831250170783542319 42957614746875256175313479)
        ·
          refine ⟨64436422120312884262970219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42957614746875256175313479 64436422120312884262970219)
          ·
            refine ⟨96654633180469326394455329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64436422120312884262970219 96654633180469326394455329)
            ·
              refine ⟨72490974885351994795841497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96654633180469326394455329 72490974885351994795841497)
              ·
                refine ⟨54368231164013996096881123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72490974885351994795841497 54368231164013996096881123)
                ·
                  refine ⟨81552346746020994145321685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54368231164013996096881123 81552346746020994145321685)
                  ·
                    refine ⟨1911383126859867050280977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 81552346746020994145321685 1911383126859867050280977)
                    ·
                      refine ⟨1433537345144900287710733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911383126859867050280977 1433537345144900287710733)
                      ·
                        rfl

theorem cell23_2791804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_2791804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791804 prefixEnd_2791804 := by exact prefixLift 2791804
  have htrace : WordTrace (prefixWord ++ tailWord_2791804) baseStart_2791804 baseEnd_2791804 := by
    simpa [prefixWord, tailWord_2791804, baseEnd_2791804] using wordTrace_append hprefix tailTrace_2791804
  have hstable : (prefixWord ++ tailWord_2791804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791804).length < 2 ^ (prefixWord ++ tailWord_2791804).sum := by decide
  have hdescent : baseEnd_2791804 < baseStart_2791804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791834 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2791834 : Nat := 118140960795 + 2791834 * 2 ^ 59
def prefixEnd_2791834 : Nat := 4983230072969 + 3 ^ 40 * 2791834 * 2
def baseEnd_2791834 : Nat := 1433552749564535170335595

theorem tailTrace_2791834 : CollatzResearch.WordTrace tailWord_2791834 prefixEnd_2791834 1433552749564535170335595 := by
  unfold tailWord_2791834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25456637841917425032935639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67884367578446466754495037 25456637841917425032935639)
  ·
    refine ⟨38184956762876137549403459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25456637841917425032935639 38184956762876137549403459)
    ·
      refine ⟨57277435144314206324105189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38184956762876137549403459 57277435144314206324105189)
      ·
        refine ⟨10739519089558913685769723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57277435144314206324105189 10739519089558913685769723)
        ·
          refine ⟨16109278634338370528654585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10739519089558913685769723 16109278634338370528654585)
          ·
            refine ⟨12081958975753777896490939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16109278634338370528654585 12081958975753777896490939)
            ·
              refine ⟨18122938463630666844736409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12081958975753777896490939 18122938463630666844736409)
              ·
                refine ⟨13592203847723000133552307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18122938463630666844736409 13592203847723000133552307)
                ·
                  refine ⟨20388305771584500200328461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13592203847723000133552307 20388305771584500200328461)
                  ·
                    refine ⟨7645614664344187575123173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20388305771584500200328461 7645614664344187575123173)
                    ·
                      refine ⟨1433552749564535170335595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7645614664344187575123173 1433552749564535170335595)
                      ·
                        rfl

theorem cell23_2791834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2791834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791834 prefixEnd_2791834 := by exact prefixLift 2791834
  have htrace : WordTrace (prefixWord ++ tailWord_2791834) baseStart_2791834 baseEnd_2791834 := by
    simpa [prefixWord, tailWord_2791834, baseEnd_2791834] using wordTrace_append hprefix tailTrace_2791834
  have hstable : (prefixWord ++ tailWord_2791834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791834).length < 2 ^ (prefixWord ++ tailWord_2791834).sum := by decide
  have hdescent : baseEnd_2791834 < baseStart_2791834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791887 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 2, 9]
def baseStart_2791887 : Nat := 118140960795 + 2791887 * 2 ^ 59
def prefixEnd_2791887 : Nat := 4983230072969 + 3 ^ 40 * 2791887 * 2
def baseEnd_2791887 : Nat := 477859988013074487657617

theorem tailTrace_2791887 : CollatzResearch.WordTrace tailWord_2791887 prefixEnd_2791887 477859988013074487657617 := by
  unfold tailWord_2791887
  simp only [CollatzResearch.WordTrace]
  refine ⟨101828484436477690183421915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67885656290985126788947943 101828484436477690183421915)
  ·
    refine ⟨152742726654716535275132873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101828484436477690183421915 152742726654716535275132873)
    ·
      refine ⟨114557044991037401456349655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152742726654716535275132873 114557044991037401456349655)
      ·
        refine ⟨171835567486556102184524483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114557044991037401456349655 171835567486556102184524483)
        ·
          refine ⟨257753351229834153276786725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171835567486556102184524483 257753351229834153276786725)
          ·
            refine ⟨48328753355593903739397511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257753351229834153276786725 48328753355593903739397511)
            ·
              refine ⟨72493130033390855609096267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48328753355593903739397511 72493130033390855609096267)
              ·
                refine ⟨108739695050086283413644401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72493130033390855609096267 108739695050086283413644401)
                ·
                  refine ⟨81554771287564712560233301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108739695050086283413644401 81554771287564712560233301)
                  ·
                    refine ⟨477859988013074487657617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 81554771287564712560233301 477859988013074487657617)
                    ·
                      rfl

theorem cell23_2791887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_2791887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791887 prefixEnd_2791887 := by exact prefixLift 2791887
  have htrace : WordTrace (prefixWord ++ tailWord_2791887) baseStart_2791887 baseEnd_2791887 := by
    simpa [prefixWord, tailWord_2791887, baseEnd_2791887] using wordTrace_append hprefix tailTrace_2791887
  have hstable : (prefixWord ++ tailWord_2791887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791887).length < 2 ^ (prefixWord ++ tailWord_2791887).sum := by decide
  have hdescent : baseEnd_2791887 < baseStart_2791887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791904 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 3, 5]
def baseStart_2791904 : Nat := 118140960795 + 2791904 * 2 ^ 59
def prefixEnd_2791904 : Nat := 4983230072969 + 3 ^ 40 * 2791904 * 2
def baseEnd_2791904 : Nat := 477862897736783298820091

theorem tailTrace_2791904 : CollatzResearch.WordTrace tailWord_2791904 prefixEnd_2791904 477862897736783298820091 := by
  unfold tailWord_2791904
  simp only [CollatzResearch.WordTrace]
  refine ⟨50914552238708051043395383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67886069651610734724527177 50914552238708051043395383)
  ·
    refine ⟨76371828358062076565093075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50914552238708051043395383 76371828358062076565093075)
    ·
      refine ⟨114557742537093114847639613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76371828358062076565093075 114557742537093114847639613)
      ·
        refine ⟨42959153451409918067864855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114557742537093114847639613 42959153451409918067864855)
        ·
          refine ⟨64438730177114877101797283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42959153451409918067864855 64438730177114877101797283)
          ·
            refine ⟨96658095265672315652695925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64438730177114877101797283 96658095265672315652695925)
            ·
              refine ⟨9061696431156779592440243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96658095265672315652695925 9061696431156779592440243)
              ·
                refine ⟨13592544646735169388660365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9061696431156779592440243 13592544646735169388660365)
                ·
                  refine ⟨5097204242525688520747637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13592544646735169388660365 5097204242525688520747637)
                  ·
                    refine ⟨477862897736783298820091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5097204242525688520747637 477862897736783298820091)
                    ·
                      rfl

theorem cell23_2791904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_2791904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791904 prefixEnd_2791904 := by exact prefixLift 2791904
  have htrace : WordTrace (prefixWord ++ tailWord_2791904) baseStart_2791904 baseEnd_2791904 := by
    simpa [prefixWord, tailWord_2791904, baseEnd_2791904] using wordTrace_append hprefix tailTrace_2791904
  have hstable : (prefixWord ++ tailWord_2791904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791904).length < 2 ^ (prefixWord ++ tailWord_2791904).sum := by decide
  have hdescent : baseEnd_2791904 < baseStart_2791904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791944 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2791944 : Nat := 118140960795 + 2791944 * 2 ^ 59
def prefixEnd_2791944 : Nat := 4983230072969 + 3 ^ 40 * 2791944 * 2
def baseEnd_2791944 : Nat := 1433609232436529739960089

theorem tailTrace_2791944 : CollatzResearch.WordTrace tailWord_2791944 prefixEnd_2791944 1433609232436529739960089 := by
  unfold tailWord_2791944
  simp only [CollatzResearch.WordTrace]
  refine ⟨50915281698635594459123443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67887042264847459278831257 50915281698635594459123443)
  ·
    refine ⟨76372922547953391688685165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50915281698635594459123443 76372922547953391688685165)
    ·
      refine ⟨28639845955482521883256937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76372922547953391688685165 28639845955482521883256937)
      ·
        refine ⟨21479884466611891412442703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28639845955482521883256937 21479884466611891412442703)
        ·
          refine ⟨32219826699917837118664055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21479884466611891412442703 32219826699917837118664055)
          ·
            refine ⟨48329740049876755677996083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32219826699917837118664055 48329740049876755677996083)
            ·
              refine ⟨72494610074815133516994125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48329740049876755677996083 72494610074815133516994125)
              ·
                refine ⟨27185478778055675068872797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72494610074815133516994125 27185478778055675068872797)
                ·
                  refine ⟨10194554541770878150827299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27185478778055675068872797 10194554541770878150827299)
                  ·
                    refine ⟨15291831812656317226240949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10194554541770878150827299 15291831812656317226240949)
                    ·
                      refine ⟨1433609232436529739960089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15291831812656317226240949 1433609232436529739960089)
                      ·
                        rfl

theorem cell23_2791944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2791944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791944 prefixEnd_2791944 := by exact prefixLift 2791944
  have htrace : WordTrace (prefixWord ++ tailWord_2791944) baseStart_2791944 baseEnd_2791944 := by
    simpa [prefixWord, tailWord_2791944, baseEnd_2791944] using wordTrace_append hprefix tailTrace_2791944
  have hstable : (prefixWord ++ tailWord_2791944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791944).length < 2 ^ (prefixWord ++ tailWord_2791944).sum := by decide
  have hdescent : baseEnd_2791944 < baseStart_2791944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791971 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 4]
def baseStart_2791971 : Nat := 118140960795 + 2791971 * 2 ^ 59
def prefixEnd_2791971 : Nat := 4983230072969 + 3 ^ 40 * 2791971 * 2
def baseEnd_2791971 : Nat := 1433623096414201134322465

theorem tailTrace_2791971 : CollatzResearch.WordTrace tailWord_2791971 prefixEnd_2791971 1433623096414201134322465 := by
  unfold tailWord_2791971
  simp only [CollatzResearch.WordTrace]
  refine ⟨101831548168173372529479767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67887698778782248352986511 101831548168173372529479767)
  ·
    refine ⟨152747322252260058794219651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101831548168173372529479767 152747322252260058794219651)
    ·
      refine ⟨229120983378390088191329477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152747322252260058794219651 229120983378390088191329477)
      ·
        refine ⟨42960184383448141535874277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229120983378390088191329477 42960184383448141535874277)
        ·
          refine ⟨8055034571896526537976427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42960184383448141535874277 8055034571896526537976427)
          ·
            refine ⟨12082551857844789806964641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8055034571896526537976427 12082551857844789806964641)
            ·
              refine ⟨9061913893383592355223481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12082551857844789806964641 9061913893383592355223481)
              ·
                refine ⟨6796435420037694266417611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9061913893383592355223481 6796435420037694266417611)
                ·
                  refine ⟨10194653130056541399626417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6796435420037694266417611 10194653130056541399626417)
                  ·
                    refine ⟨7645989847542406049719813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10194653130056541399626417 7645989847542406049719813)
                    ·
                      refine ⟨1433623096414201134322465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7645989847542406049719813 1433623096414201134322465)
                      ·
                        rfl

theorem cell23_2791971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_2791971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791971 prefixEnd_2791971 := by exact prefixLift 2791971
  have htrace : WordTrace (prefixWord ++ tailWord_2791971) baseStart_2791971 baseEnd_2791971 := by
    simpa [prefixWord, tailWord_2791971, baseEnd_2791971] using wordTrace_append hprefix tailTrace_2791971
  have hstable : (prefixWord ++ tailWord_2791971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791971).length < 2 ^ (prefixWord ++ tailWord_2791971).sum := by decide
  have hdescent : baseEnd_2791971 < baseStart_2791971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791972 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_2791972 : Nat := 118140960795 + 2791972 * 2 ^ 59
def prefixEnd_2791972 : Nat := 4983230072969 + 3 ^ 40 * 2791972 * 2
def baseEnd_2791972 : Nat := 477874536631618543469987

theorem tailTrace_2791972 : CollatzResearch.WordTrace tailWord_2791972 prefixEnd_2791972 477874536631618543469987 := by
  unfold tailWord_2791972
  simp only [CollatzResearch.WordTrace]
  refine ⟨50915792320584874850133085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67887723094113166466844113 50915792320584874850133085)
  ·
    refine ⟨19093422120219328068799907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50915792320584874850133085 19093422120219328068799907)
    ·
      refine ⟨28640133180328992103199861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19093422120219328068799907 28640133180328992103199861)
      ·
        refine ⟨2685012485655843009674987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28640133180328992103199861 2685012485655843009674987)
        ·
          refine ⟨4027518728483764514512481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685012485655843009674987 4027518728483764514512481)
          ·
            refine ⟨3020639046362823385884361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4027518728483764514512481 3020639046362823385884361)
            ·
              refine ⟨2265479284772117539413271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3020639046362823385884361 2265479284772117539413271)
              ·
                refine ⟨3398218927158176309119907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265479284772117539413271 3398218927158176309119907)
                ·
                  refine ⟨5097328390737264463679861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398218927158176309119907 5097328390737264463679861)
                  ·
                    refine ⟨477874536631618543469987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5097328390737264463679861 477874536631618543469987)
                    ·
                      rfl

theorem cell23_2791972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_2791972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791972 prefixEnd_2791972 := by exact prefixLift 2791972
  have htrace : WordTrace (prefixWord ++ tailWord_2791972) baseStart_2791972 baseEnd_2791972 := by
    simpa [prefixWord, tailWord_2791972, baseEnd_2791972] using wordTrace_append hprefix tailTrace_2791972
  have hstable : (prefixWord ++ tailWord_2791972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791972).length < 2 ^ (prefixWord ++ tailWord_2791972).sum := by decide
  have hdescent : baseEnd_2791972 < baseStart_2791972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792008 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_2792008 : Nat := 118140960795 + 2792008 * 2 ^ 59
def prefixEnd_2792008 : Nat := 4983230072969 + 3 ^ 40 * 2792008 * 2
def baseEnd_2792008 : Nat := 1433642095198417489559795

theorem tailTrace_2792008 : CollatzResearch.WordTrace tailWord_2792008 prefixEnd_2792008 1433642095198417489559795 := by
  unfold tailWord_2792008
  simp only [CollatzResearch.WordTrace]
  refine ⟨50916448834519663924288339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67888598446026218565717785 50916448834519663924288339)
  ·
    refine ⟨76374673251779495886432509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50916448834519663924288339 76374673251779495886432509)
    ·
      refine ⟨28640502469417310957412191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76374673251779495886432509 28640502469417310957412191)
      ·
        refine ⟨42960753704125966436118287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28640502469417310957412191 42960753704125966436118287)
        ·
          refine ⟨64441130556188949654177431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42960753704125966436118287 64441130556188949654177431)
          ·
            refine ⟨96661695834283424481266147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64441130556188949654177431 96661695834283424481266147)
            ·
              refine ⟨144992543751425136721899221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96661695834283424481266147 144992543751425136721899221)
              ·
                refine ⟨3398262744174026641919513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144992543751425136721899221 3398262744174026641919513)
                ·
                  refine ⟨2548697058130519981439635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3398262744174026641919513 2548697058130519981439635)
                  ·
                    refine ⟨3823045587195779972159453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2548697058130519981439635 3823045587195779972159453)
                    ·
                      refine ⟨1433642095198417489559795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823045587195779972159453 1433642095198417489559795)
                      ·
                        rfl

theorem cell23_2792008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_2792008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792008 prefixEnd_2792008 := by exact prefixLift 2792008
  have htrace : WordTrace (prefixWord ++ tailWord_2792008) baseStart_2792008 baseEnd_2792008 := by
    simpa [prefixWord, tailWord_2792008, baseEnd_2792008] using wordTrace_append hprefix tailTrace_2792008
  have hstable : (prefixWord ++ tailWord_2792008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792008).length < 2 ^ (prefixWord ++ tailWord_2792008).sum := by decide
  have hdescent : baseEnd_2792008 < baseStart_2792008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792024 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 1, 8]
def baseStart_2792024 : Nat := 118140960795 + 2792024 * 2 ^ 59
def prefixEnd_2792024 : Nat := 4983230072969 + 3 ^ 40 * 2792024 * 2
def baseEnd_2792024 : Nat := 477883436962963142319907

theorem tailTrace_2792024 : CollatzResearch.WordTrace tailWord_2792024 prefixEnd_2792024 477883436962963142319907 := by
  unfold tailWord_2792024
  simp only [CollatzResearch.WordTrace]
  refine ⟨50916740618490681290579563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67888987491320908387439417 50916740618490681290579563)
  ·
    refine ⟨76375110927736021935869345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50916740618490681290579563 76375110927736021935869345)
    ·
      refine ⟨57281333195802016451902009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76375110927736021935869345 57281333195802016451902009)
      ·
        refine ⟨42960999896851512338926507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57281333195802016451902009 42960999896851512338926507)
        ·
          refine ⟨64441499845277268508389761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42960999896851512338926507 64441499845277268508389761)
          ·
            refine ⟨48331124883957951381292321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64441499845277268508389761 48331124883957951381292321)
            ·
              refine ⟨36248343662968463535969241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48331124883957951381292321 36248343662968463535969241)
              ·
                refine ⟨27186257747226347651976931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36248343662968463535969241 27186257747226347651976931)
                ·
                  refine ⟨40779386620839521477965397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27186257747226347651976931 40779386620839521477965397)
                  ·
                    refine ⟨477883436962963142319907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40779386620839521477965397 477883436962963142319907)
                    ·
                      rfl

theorem cell23_2792024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_2792024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792024 prefixEnd_2792024 := by exact prefixLift 2792024
  have htrace : WordTrace (prefixWord ++ tailWord_2792024) baseStart_2792024 baseEnd_2792024 := by
    simpa [prefixWord, tailWord_2792024, baseEnd_2792024] using wordTrace_append hprefix tailTrace_2792024
  have hstable : (prefixWord ++ tailWord_2792024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792024).length < 2 ^ (prefixWord ++ tailWord_2792024).sum := by decide
  have hdescent : baseEnd_2792024 < baseStart_2792024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792088 : List Nat := [2, 1, 2, 4, 1, 1, 2, 5, 5]
def baseStart_2792088 : Nat := 118140960795 + 2792088 * 2 ^ 59
def prefixEnd_2792088 : Nat := 4983230072969 + 3 ^ 40 * 2792088 * 2
def baseEnd_2792088 : Nat := 159298130405641908506603

theorem tailTrace_2792088 : CollatzResearch.WordTrace tailWord_2792088 prefixEnd_2792088 159298130405641908506603 := by
  unfold tailWord_2792088
  simp only [CollatzResearch.WordTrace]
  refine ⟨50917907754374750755744459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67890543672499667674325945 50917907754374750755744459)
  ·
    refine ⟨76376861631562126133616689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50917907754374750755744459 76376861631562126133616689)
    ·
      refine ⟨57282646223671594600212517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76376861631562126133616689 57282646223671594600212517)
      ·
        refine ⟨10740496166938423987539847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57282646223671594600212517 10740496166938423987539847)
        ·
          refine ⟨16110744250407635981309771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10740496166938423987539847 16110744250407635981309771)
          ·
            refine ⟨24166116375611453971964657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16110744250407635981309771 24166116375611453971964657)
            ·
              refine ⟨18124587281708590478973493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24166116375611453971964657 18124587281708590478973493)
              ·
                refine ⟨1699180057660180357403765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18124587281708590478973493 1699180057660180357403765)
                ·
                  refine ⟨159298130405641908506603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1699180057660180357403765 159298130405641908506603)
                  ·
                    rfl

theorem cell23_2792088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 5].length) (baseStart_2792088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792088 prefixEnd_2792088 := by exact prefixLift 2792088
  have htrace : WordTrace (prefixWord ++ tailWord_2792088) baseStart_2792088 baseEnd_2792088 := by
    simpa [prefixWord, tailWord_2792088, baseEnd_2792088] using wordTrace_append hprefix tailTrace_2792088
  have hstable : (prefixWord ++ tailWord_2792088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792088).length < 2 ^ (prefixWord ++ tailWord_2792088).sum := by decide
  have hdescent : baseEnd_2792088 < baseStart_2792088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792111 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_2792111 : Nat := 118140960795 + 2792111 * 2 ^ 59
def prefixEnd_2792111 : Nat := 4983230072969 + 3 ^ 40 * 2792111 * 2
def baseEnd_2792111 : Nat := 1433694983705830586571821

theorem tailTrace_2792111 : CollatzResearch.WordTrace tailWord_2792111 prefixEnd_2792111 1433694983705830586571821 := by
  unfold tailWord_2792111
  simp only [CollatzResearch.WordTrace]
  refine ⟨101836654387666176439576187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67891102925110784293050791 101836654387666176439576187)
  ·
    refine ⟨152754981581499264659364281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101836654387666176439576187 152754981581499264659364281)
    ·
      refine ⟨114566236186124448494523211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152754981581499264659364281 114566236186124448494523211)
      ·
        refine ⟨171849354279186672741784817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114566236186124448494523211 171849354279186672741784817)
        ·
          refine ⟨128887015709390004556338613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171849354279186672741784817 128887015709390004556338613)
          ·
            refine ⟨12083157722755312927156745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128887015709390004556338613 12083157722755312927156745)
            ·
              refine ⟨9062368292066484695367559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12083157722755312927156745 9062368292066484695367559)
              ·
                refine ⟨13593552438099727043051339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9062368292066484695367559 13593552438099727043051339)
                ·
                  refine ⟨20390328657149590564577009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13593552438099727043051339 20390328657149590564577009)
                  ·
                    refine ⟨15292746492862192923432757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20390328657149590564577009 15292746492862192923432757)
                    ·
                      refine ⟨1433694983705830586571821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15292746492862192923432757 1433694983705830586571821)
                      ·
                        rfl

theorem cell23_2792111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_2792111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792111 prefixEnd_2792111 := by exact prefixLift 2792111
  have htrace : WordTrace (prefixWord ++ tailWord_2792111) baseStart_2792111 baseEnd_2792111 := by
    simpa [prefixWord, tailWord_2792111, baseEnd_2792111] using wordTrace_append hprefix tailTrace_2792111
  have hstable : (prefixWord ++ tailWord_2792111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792111).length < 2 ^ (prefixWord ++ tailWord_2792111).sum := by decide
  have hdescent : baseEnd_2792111 < baseStart_2792111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792121 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2792121 : Nat := 118140960795 + 2792121 * 2 ^ 59
def prefixEnd_2792121 : Nat := 4983230072969 + 3 ^ 40 * 2792121 * 2
def baseEnd_2792121 : Nat := 1433700118512375547446775

theorem tailTrace_2792121 : CollatzResearch.WordTrace tailWord_2792121 prefixEnd_2792121 1433700118512375547446775 := by
  unfold tailWord_2792121
  simp only [CollatzResearch.WordTrace]
  refine ⟨101837019117629948147440217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67891346078419965431626811 101837019117629948147440217)
  ·
    refine ⟨76377764338222461110580163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101837019117629948147440217 76377764338222461110580163)
    ·
      refine ⟨114566646507333691665870245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76377764338222461110580163 114566646507333691665870245)
      ·
        refine ⟨21481246220125067187350671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114566646507333691665870245 21481246220125067187350671)
        ·
          refine ⟨32221869330187600781026007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21481246220125067187350671 32221869330187600781026007)
          ·
            refine ⟨48332803995281401171539011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32221869330187600781026007 48332803995281401171539011)
            ·
              refine ⟨72499205992922101757308517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48332803995281401171539011 72499205992922101757308517)
              ·
                refine ⟨13593601123672894079495347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72499205992922101757308517 13593601123672894079495347)
                ·
                  refine ⟨20390401685509341119243021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13593601123672894079495347 20390401685509341119243021)
                  ·
                    refine ⟨7646400632066002919716133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20390401685509341119243021 7646400632066002919716133)
                    ·
                      refine ⟨1433700118512375547446775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7646400632066002919716133 1433700118512375547446775)
                      ·
                        rfl

theorem cell23_2792121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2792121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792121 prefixEnd_2792121 := by exact prefixLift 2792121
  have htrace : WordTrace (prefixWord ++ tailWord_2792121) baseStart_2792121 baseEnd_2792121 := by
    simpa [prefixWord, tailWord_2792121, baseEnd_2792121] using wordTrace_append hprefix tailTrace_2792121
  have hstable : (prefixWord ++ tailWord_2792121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792121).length < 2 ^ (prefixWord ++ tailWord_2792121).sum := by decide
  have hdescent : baseEnd_2792121 < baseStart_2792121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792138 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_2792138 : Nat := 118140960795 + 2792138 * 2 ^ 59
def prefixEnd_2792138 : Nat := 4983230072969 + 3 ^ 40 * 2792138 * 2
def baseEnd_2792138 : Nat := 1433708847683501980934197

theorem tailTrace_2792138 : CollatzResearch.WordTrace tailWord_2792138 prefixEnd_2792138 1433708847683501980934197 := by
  unfold tailWord_2792138
  simp only [CollatzResearch.WordTrace]
  refine ⟨25459409789642090012702267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67891759439045573367206045 25459409789642090012702267)
  ·
    refine ⟨38189114684463135019053401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25459409789642090012702267 38189114684463135019053401)
    ·
      refine ⟨28641836013347351264290051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38189114684463135019053401 28641836013347351264290051)
      ·
        refine ⟨42962754020021026896435077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28641836013347351264290051 42962754020021026896435077)
        ·
          refine ⟨8055516378753942543081577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42962754020021026896435077 8055516378753942543081577)
          ·
            refine ⟨6041637284065456907311183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8055516378753942543081577 6041637284065456907311183)
            ·
              refine ⟨9062455926098185360966775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6041637284065456907311183 9062455926098185360966775)
              ·
                refine ⟨13593683889147278041450163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9062455926098185360966775 13593683889147278041450163)
                ·
                  refine ⟨20390525833720917062175245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13593683889147278041450163 20390525833720917062175245)
                  ·
                    refine ⟨7646447187645343898315717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20390525833720917062175245 7646447187645343898315717)
                    ·
                      refine ⟨1433708847683501980934197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7646447187645343898315717 1433708847683501980934197)
                      ·
                        rfl

theorem cell23_2792138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_2792138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792138 prefixEnd_2792138 := by exact prefixLift 2792138
  have htrace : WordTrace (prefixWord ++ tailWord_2792138) baseStart_2792138 baseEnd_2792138 := by
    simpa [prefixWord, tailWord_2792138, baseEnd_2792138] using wordTrace_append hprefix tailTrace_2792138
  have hstable : (prefixWord ++ tailWord_2792138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792138).length < 2 ^ (prefixWord ++ tailWord_2792138).sum := by decide
  have hdescent : baseEnd_2792138 < baseStart_2792138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792151 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_2792151 : Nat := 118140960795 + 2792151 * 2 ^ 59
def prefixEnd_2792151 : Nat := 4983230072969 + 3 ^ 40 * 2792151 * 2
def baseEnd_2792151 : Nat := 1433715522932010430071637

theorem tailTrace_2792151 : CollatzResearch.WordTrace tailWord_2792151 prefixEnd_2792151 1433715522932010430071637 := by
  unfold tailWord_2792151
  simp only [CollatzResearch.WordTrace]
  refine ⟨101838113307521263271032307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67892075538347508847354871 101838113307521263271032307)
  ·
    refine ⟨152757169961281894906548461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101838113307521263271032307 152757169961281894906548461)
    ·
      refine ⟨57283938735480710589955673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152757169961281894906548461 57283938735480710589955673)
      ·
        refine ⟨42962954051610532942466755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57283938735480710589955673 42962954051610532942466755)
        ·
          refine ⟨64444431077415799413700133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42962954051610532942466755 64444431077415799413700133)
          ·
            refine ⟨12083330827015462390068775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64444431077415799413700133 12083330827015462390068775)
            ·
              refine ⟨18124996240523193585103163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12083330827015462390068775 18124996240523193585103163)
              ·
                refine ⟨27187494360784790377654745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18124996240523193585103163 27187494360784790377654745)
                ·
                  refine ⟨20390620770588592783241059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27187494360784790377654745 20390620770588592783241059)
                  ·
                    refine ⟨30585931155882889174861589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20390620770588592783241059 30585931155882889174861589)
                    ·
                      refine ⟨1433715522932010430071637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30585931155882889174861589 1433715522932010430071637)
                      ·
                        rfl

theorem cell23_2792151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_2792151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792151 prefixEnd_2792151 := by exact prefixLift 2792151
  have htrace : WordTrace (prefixWord ++ tailWord_2792151) baseStart_2792151 baseEnd_2792151 := by
    simpa [prefixWord, tailWord_2792151, baseEnd_2792151] using wordTrace_append hprefix tailTrace_2792151
  have hstable : (prefixWord ++ tailWord_2792151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792151).length < 2 ^ (prefixWord ++ tailWord_2792151).sum := by decide
  have hdescent : baseEnd_2792151 < baseStart_2792151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792165 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_2792165 : Nat := 118140960795 + 2792165 * 2 ^ 59
def prefixEnd_2792165 : Nat := 4983230072969 + 3 ^ 40 * 2792165 * 2
def baseEnd_2792165 : Nat := 477907570553724458432191

theorem tailTrace_2792165 : CollatzResearch.WordTrace tailWord_2792165 prefixEnd_2792165 477907570553724458432191 := by
  unfold tailWord_2792165
  simp only [CollatzResearch.WordTrace]
  refine ⟨101838623929470543662041949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67892415952980362441361299 101838623929470543662041949)
  ·
    refine ⟨38189483973551453873265731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101838623929470543662041949 38189483973551453873265731)
    ·
      refine ⟨57284225960327180809898597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38189483973551453873265731 57284225960327180809898597)
      ·
        refine ⟨10740792367561346401855987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57284225960327180809898597 10740792367561346401855987)
        ·
          refine ⟨16111188551342019602783981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10740792367561346401855987 16111188551342019602783981)
          ·
            refine ⟨6041695706753257351043993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16111188551342019602783981 6041695706753257351043993)
            ·
              refine ⟨4531271780064943013282995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6041695706753257351043993 4531271780064943013282995)
              ·
                refine ⟨6796907670097414519924493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531271780064943013282995 6796907670097414519924493)
                ·
                  refine ⟨2548840376286530444971685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6796907670097414519924493 2548840376286530444971685)
                  ·
                    refine ⟨477907570553724458432191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2548840376286530444971685 477907570553724458432191)
                    ·
                      rfl

theorem cell23_2792165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_2792165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792165 prefixEnd_2792165 := by exact prefixLift 2792165
  have htrace : WordTrace (prefixWord ++ tailWord_2792165) baseStart_2792165 baseEnd_2792165 := by
    simpa [prefixWord, tailWord_2792165, baseEnd_2792165] using wordTrace_append hprefix tailTrace_2792165
  have hstable : (prefixWord ++ tailWord_2792165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792165).length < 2 ^ (prefixWord ++ tailWord_2792165).sum := by decide
  have hdescent : baseEnd_2792165 < baseStart_2792165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792199 : List Nat := [1, 1, 4, 4, 1, 3, 1, 3, 1, 4]
def baseStart_2792199 : Nat := 118140960795 + 2792199 * 2 ^ 59
def prefixEnd_2792199 : Nat := 4983230072969 + 3 ^ 40 * 2792199 * 2
def baseEnd_2792199 : Nat := 477913390001142080757139

theorem tailTrace_2792199 : CollatzResearch.WordTrace tailWord_2792199 prefixEnd_2792199 477913390001142080757139 := by
  unfold tailWord_2792199
  simp only [CollatzResearch.WordTrace]
  refine ⟨101839864011347367468779651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67893242674231578312519767 101839864011347367468779651)
  ·
    refine ⟨152759796017021051203169477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101839864011347367468779651 152759796017021051203169477)
    ·
      refine ⟨28642461753191447100594277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152759796017021051203169477 28642461753191447100594277)
      ·
        refine ⟨5370461578723396331361427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28642461753191447100594277 5370461578723396331361427)
        ·
          refine ⟨8055692368085094497042141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370461578723396331361427 8055692368085094497042141)
          ·
            refine ⟨3020884638031910436390803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8055692368085094497042141 3020884638031910436390803)
            ·
              refine ⟨4531326957047865654586205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020884638031910436390803 4531326957047865654586205)
              ·
                refine ⟨1699247608892949620469827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4531326957047865654586205 1699247608892949620469827)
                ·
                  refine ⟨2548871413339424430704741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699247608892949620469827 2548871413339424430704741)
                  ·
                    refine ⟨477913390001142080757139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2548871413339424430704741 477913390001142080757139)
                    ·
                      rfl

theorem cell23_2792199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_2792199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792199 prefixEnd_2792199 := by exact prefixLift 2792199
  have htrace : WordTrace (prefixWord ++ tailWord_2792199) baseStart_2792199 baseEnd_2792199 := by
    simpa [prefixWord, tailWord_2792199, baseEnd_2792199] using wordTrace_append hprefix tailTrace_2792199
  have hstable : (prefixWord ++ tailWord_2792199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792199).length < 2 ^ (prefixWord ++ tailWord_2792199).sum := by decide
  have hdescent : baseEnd_2792199 < baseStart_2792199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792245 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_2792245 : Nat := 118140960795 + 2792245 * 2 ^ 59
def prefixEnd_2792245 : Nat := 4983230072969 + 3 ^ 40 * 2792245 * 2
def baseEnd_2792245 : Nat := 1433763790113533062296205

theorem tailTrace_2792245 : CollatzResearch.WordTrace tailWord_2792245 prefixEnd_2792245 1433763790113533062296205 := by
  unfold tailWord_2792245
  simp only [CollatzResearch.WordTrace]
  refine ⟨101841541769180717324954189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67894361179453811549969459 101841541769180717324954189)
  ·
    refine ⟨38190578163442768996857821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101841541769180717324954189 38190578163442768996857821)
    ·
      refine ⟨14321466811291038373821683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38190578163442768996857821 14321466811291038373821683)
      ·
        refine ⟨21482200216936557560732525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14321466811291038373821683 21482200216936557560732525)
        ·
          refine ⟨8055825081351209085274697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21482200216936557560732525 8055825081351209085274697)
          ·
            refine ⟨6041868811013406813956023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8055825081351209085274697 6041868811013406813956023)
            ·
              refine ⟨9062803216520110220934035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6041868811013406813956023 9062803216520110220934035)
              ·
                refine ⟨13594204824780165331401053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9062803216520110220934035 13594204824780165331401053)
                ·
                  refine ⟨5097826809292561999275395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13594204824780165331401053 5097826809292561999275395)
                  ·
                    refine ⟨7646740213938842998913093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5097826809292561999275395 7646740213938842998913093)
                    ·
                      refine ⟨1433763790113533062296205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7646740213938842998913093 1433763790113533062296205)
                      ·
                        rfl

theorem cell23_2792245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_2792245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792245 prefixEnd_2792245 := by exact prefixLift 2792245
  have htrace : WordTrace (prefixWord ++ tailWord_2792245) baseStart_2792245 baseEnd_2792245 := by
    simpa [prefixWord, tailWord_2792245, baseEnd_2792245] using wordTrace_append hprefix tailTrace_2792245
  have hstable : (prefixWord ++ tailWord_2792245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792245).length < 2 ^ (prefixWord ++ tailWord_2792245).sum := by decide
  have hdescent : baseEnd_2792245 < baseStart_2792245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792265 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 5]
def baseStart_2792265 : Nat := 118140960795 + 2792265 * 2 ^ 59
def prefixEnd_2792265 : Nat := 4983230072969 + 3 ^ 40 * 2792265 * 2
def baseEnd_2792265 : Nat := 1433774059726622984046113

theorem tailTrace_2792265 : CollatzResearch.WordTrace tailWord_2792265 prefixEnd_2792265 1433774059726622984046113 := by
  unfold tailWord_2792265
  simp only [CollatzResearch.WordTrace]
  refine ⟨101842271229108260740682249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67894847486072173827121499 101842271229108260740682249)
  ·
    refine ⟨76381703421831195555511687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101842271229108260740682249 76381703421831195555511687)
    ·
      refine ⟨114572555132746793333267531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76381703421831195555511687 114572555132746793333267531)
      ·
        refine ⟨171858832699120189999901297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114572555132746793333267531 171858832699120189999901297)
        ·
          refine ⟨128894124524340142499925973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171858832699120189999901297 128894124524340142499925973)
          ·
            refine ⟨3020956043539222089842015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128894124524340142499925973 3020956043539222089842015)
            ·
              refine ⟨4531434065308833134763023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020956043539222089842015 4531434065308833134763023)
              ·
                refine ⟨6797151097963249702144535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531434065308833134763023 6797151097963249702144535)
                ·
                  refine ⟨10195726646944874553216803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797151097963249702144535 10195726646944874553216803)
                  ·
                    refine ⟨15293589970417311829825205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10195726646944874553216803 15293589970417311829825205)
                    ·
                      refine ⟨1433774059726622984046113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15293589970417311829825205 1433774059726622984046113)
                      ·
                        rfl

theorem cell23_2792265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 5].length) (baseStart_2792265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792265 prefixEnd_2792265 := by exact prefixLift 2792265
  have htrace : WordTrace (prefixWord ++ tailWord_2792265) baseStart_2792265 baseEnd_2792265 := by
    simpa [prefixWord, tailWord_2792265, baseEnd_2792265] using wordTrace_append hprefix tailTrace_2792265
  have hstable : (prefixWord ++ tailWord_2792265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792265).length < 2 ^ (prefixWord ++ tailWord_2792265).sum := by decide
  have hdescent : baseEnd_2792265 < baseStart_2792265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792271 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_2792271 : Nat := 118140960795 + 2792271 * 2 ^ 59
def prefixEnd_2792271 : Nat := 4983230072969 + 3 ^ 40 * 2792271 * 2
def baseEnd_2792271 : Nat := 1433777140610549960571085

theorem tailTrace_2792271 : CollatzResearch.WordTrace tailWord_2792271 prefixEnd_2792271 1433777140610549960571085 := by
  unfold tailWord_2792271
  simp only [CollatzResearch.WordTrace]
  refine ⟨101842490067086523765400667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67894993378057682510267111 101842490067086523765400667)
  ·
    refine ⟨152763735100629785648101001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101842490067086523765400667 152763735100629785648101001)
    ·
      refine ⟨114572801325472339236075751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152763735100629785648101001 114572801325472339236075751)
      ·
        refine ⟨171859201988208508854113627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114572801325472339236075751 171859201988208508854113627)
        ·
          refine ⟨257788802982312763281170441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171859201988208508854113627 257788802982312763281170441)
          ·
            refine ⟨193341602236734572460877831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257788802982312763281170441 193341602236734572460877831)
            ·
              refine ⟨290012403355101858691316747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193341602236734572460877831 290012403355101858691316747)
              ·
                refine ⟨435018605032652788036975121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290012403355101858691316747 435018605032652788036975121)
                ·
                  refine ⟨326263953774489591027731341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435018605032652788036975121 326263953774489591027731341)
                  ·
                    refine ⟨122348982665433596635399253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 326263953774489591027731341 122348982665433596635399253)
                    ·
                      refine ⟨1433777140610549960571085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 122348982665433596635399253 1433777140610549960571085)
                      ·
                        rfl

theorem cell23_2792271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_2792271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792271 prefixEnd_2792271 := by exact prefixLift 2792271
  have htrace : WordTrace (prefixWord ++ tailWord_2792271) baseStart_2792271 baseEnd_2792271 := by
    simpa [prefixWord, tailWord_2792271, baseEnd_2792271] using wordTrace_append hprefix tailTrace_2792271
  have hstable : (prefixWord ++ tailWord_2792271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792271).length < 2 ^ (prefixWord ++ tailWord_2792271).sum := by decide
  have hdescent : baseEnd_2792271 < baseStart_2792271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792273 : List Nat := [1, 2, 2, 1, 7, 1, 2, 2, 1, 1, 3]
def baseStart_2792273 : Nat := 118140960795 + 2792273 * 2 ^ 59
def prefixEnd_2792273 : Nat := 4983230072969 + 3 ^ 40 * 2792273 * 2
def baseEnd_2792273 : Nat := 1433778167571858952746077

theorem tailTrace_2792273 : CollatzResearch.WordTrace tailWord_2792273 prefixEnd_2792273 1433778167571858952746077 := by
  unfold tailWord_2792273
  simp only [CollatzResearch.WordTrace]
  refine ⟨101842563013079278106973473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67895042008719518737982315 101842563013079278106973473)
  ·
    refine ⟨76381922259809458580230105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101842563013079278106973473 76381922259809458580230105)
    ·
      refine ⟨57286441694857093935172579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76381922259809458580230105 57286441694857093935172579)
      ·
        refine ⟨85929662542285640902758869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57286441694857093935172579 85929662542285640902758869)
        ·
          refine ⟨2013976465834819708658411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 85929662542285640902758869 2013976465834819708658411)
          ·
            refine ⟨3020964698752229562987617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013976465834819708658411 3020964698752229562987617)
            ·
              refine ⟨2265723524064172172240713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3020964698752229562987617 2265723524064172172240713)
              ·
                refine ⟨1699292643048129129180535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265723524064172172240713 1699292643048129129180535)
                ·
                  refine ⟨2548938964572193693770803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699292643048129129180535 2548938964572193693770803)
                  ·
                    refine ⟨3823408446858290540656205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2548938964572193693770803 3823408446858290540656205)
                    ·
                      refine ⟨1433778167571858952746077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823408446858290540656205 1433778167571858952746077)
                      ·
                        rfl

theorem cell23_2792273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 1, 3].length) (baseStart_2792273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792273 prefixEnd_2792273 := by exact prefixLift 2792273
  have htrace : WordTrace (prefixWord ++ tailWord_2792273) baseStart_2792273 baseEnd_2792273 := by
    simpa [prefixWord, tailWord_2792273, baseEnd_2792273] using wordTrace_append hprefix tailTrace_2792273
  have hstable : (prefixWord ++ tailWord_2792273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792273).length < 2 ^ (prefixWord ++ tailWord_2792273).sum := by decide
  have hdescent : baseEnd_2792273 < baseStart_2792273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792295 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_2792295 : Nat := 118140960795 + 2792295 * 2 ^ 59
def prefixEnd_2792295 : Nat := 4983230072969 + 3 ^ 40 * 2792295 * 2
def baseEnd_2792295 : Nat := 1433789464146257866670975

theorem tailTrace_2792295 : CollatzResearch.WordTrace tailWord_2792295 prefixEnd_2792295 1433789464146257866670975 := by
  unfold tailWord_2792295
  simp only [CollatzResearch.WordTrace]
  refine ⟨101843365418999575864274339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67895576945999717242849559 101843365418999575864274339)
  ·
    refine ⟨152765048128499363796411509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101843365418999575864274339 152765048128499363796411509)
    ·
      refine ⟨14321723262046815355913579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152765048128499363796411509 14321723262046815355913579)
      ·
        refine ⟨21482584893070223033870369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14321723262046815355913579 21482584893070223033870369)
        ·
          refine ⟨16111938669802667275402777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21482584893070223033870369 16111938669802667275402777)
          ·
            refine ⟨12083954002352000456552083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16111938669802667275402777 12083954002352000456552083)
            ·
              refine ⟨18125931003528000684828125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12083954002352000456552083 18125931003528000684828125)
              ·
                refine ⟨6797224126323000256810547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18125931003528000684828125 6797224126323000256810547)
                ·
                  refine ⟨10195836189484500385215821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797224126323000256810547 10195836189484500385215821)
                  ·
                    refine ⟨3823438571056687644455933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10195836189484500385215821 3823438571056687644455933)
                    ·
                      refine ⟨1433789464146257866670975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823438571056687644455933 1433789464146257866670975)
                      ·
                        rfl

theorem cell23_2792295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_2792295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792295 prefixEnd_2792295 := by exact prefixLift 2792295
  have htrace : WordTrace (prefixWord ++ tailWord_2792295) baseStart_2792295 baseEnd_2792295 := by
    simpa [prefixWord, tailWord_2792295, baseEnd_2792295] using wordTrace_append hprefix tailTrace_2792295
  have hstable : (prefixWord ++ tailWord_2792295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792295).length < 2 ^ (prefixWord ++ tailWord_2792295).sum := by decide
  have hdescent : baseEnd_2792295 < baseStart_2792295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792302 : List Nat := [4, 1, 2, 3, 2, 1, 3, 7]
def baseStart_2792302 : Nat := 118140960795 + 2792302 * 2 ^ 59
def prefixEnd_2792302 : Nat := 4983230072969 + 3 ^ 40 * 2792302 * 2
def baseEnd_2792302 : Nat := 53103446611512568121609

theorem tailTrace_2792302 : CollatzResearch.WordTrace tailWord_2792302 prefixEnd_2792302 53103446611512568121609 := by
  unfold tailWord_2792302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12730452591246777007472395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67895747153316144039852773 12730452591246777007472395)
  ·
    refine ⟨19095678886870165511208593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12730452591246777007472395 19095678886870165511208593)
    ·
      refine ⟨14321759165152624133406445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19095678886870165511208593 14321759165152624133406445)
      ·
        refine ⟨5370659686932234050027417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14321759165152624133406445 5370659686932234050027417)
        ·
          refine ⟨4027994765199175537520563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5370659686932234050027417 4027994765199175537520563)
          ·
            refine ⟨6041992147798763306280845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4027994765199175537520563 6041992147798763306280845)
            ·
              refine ⟨2265747055424536239855317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6041992147798763306280845 2265747055424536239855317)
              ·
                refine ⟨53103446611512568121609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2265747055424536239855317 53103446611512568121609)
                ·
                  rfl

theorem cell23_2792302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_2792302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792302 prefixEnd_2792302 := by exact prefixLift 2792302
  have htrace : WordTrace (prefixWord ++ tailWord_2792302) baseStart_2792302 baseEnd_2792302 := by
    simpa [prefixWord, tailWord_2792302, baseEnd_2792302] using wordTrace_append hprefix tailTrace_2792302
  have hstable : (prefixWord ++ tailWord_2792302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792302).length < 2 ^ (prefixWord ++ tailWord_2792302).sum := by decide
  have hdescent : baseEnd_2792302 < baseStart_2792302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792329 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 3]
def baseStart_2792329 : Nat := 118140960795 + 2792329 * 2 ^ 59
def prefixEnd_2792329 : Nat := 4983230072969 + 3 ^ 40 * 2792329 * 2
def baseEnd_2792329 : Nat := 1433806922488510733645819

theorem tailTrace_2792329 : CollatzResearch.WordTrace tailWord_2792329 prefixEnd_2792329 1433806922488510733645819 := by
  unfold tailWord_2792329
  simp only [CollatzResearch.WordTrace]
  refine ⟨101844605500876399671012041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67896403667250933114008027 101844605500876399671012041)
  ·
    refine ⟨76383454125657299753259031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101844605500876399671012041 76383454125657299753259031)
    ·
      refine ⟨114575181188485949629888547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76383454125657299753259031 114575181188485949629888547)
      ·
        refine ⟨171862771782728924444832821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114575181188485949629888547 171862771782728924444832821)
        ·
          refine ⟨16112134854630836666703077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171862771782728924444832821 16112134854630836666703077)
          ·
            refine ⟨3021025285243281875006827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16112134854630836666703077 3021025285243281875006827)
            ·
              refine ⟨4531537927864922812510241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021025285243281875006827 4531537927864922812510241)
              ·
                refine ⟨3398653445898692109382681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4531537927864922812510241 3398653445898692109382681)
                ·
                  refine ⟨2548990084424019082037011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3398653445898692109382681 2548990084424019082037011)
                  ·
                    refine ⟨3823485126636028623055517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2548990084424019082037011 3823485126636028623055517)
                    ·
                      refine ⟨1433806922488510733645819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823485126636028623055517 1433806922488510733645819)
                      ·
                        rfl

theorem cell23_2792329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 3].length) (baseStart_2792329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792329 prefixEnd_2792329 := by exact prefixLift 2792329
  have htrace : WordTrace (prefixWord ++ tailWord_2792329) baseStart_2792329 baseEnd_2792329 := by
    simpa [prefixWord, tailWord_2792329, baseEnd_2792329] using wordTrace_append hprefix tailTrace_2792329
  have hstable : (prefixWord ++ tailWord_2792329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792329).length < 2 ^ (prefixWord ++ tailWord_2792329).sum := by decide
  have hdescent : baseEnd_2792329 < baseStart_2792329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792346 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3]
def baseStart_2792346 : Nat := 118140960795 + 2792346 * 2 ^ 59
def prefixEnd_2792346 : Nat := 4983230072969 + 3 ^ 40 * 2792346 * 2
def baseEnd_2792346 : Nat := 1433815651659637167133241

theorem tailTrace_2792346 : CollatzResearch.WordTrace tailWord_2792346 prefixEnd_2792346 1433815651659637167133241 := by
  unfold tailWord_2792346
  simp only [CollatzResearch.WordTrace]
  refine ⟨25461306385453702893595223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67896817027876541049587261 25461306385453702893595223)
  ·
    refine ⟨38191959578180554340392835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25461306385453702893595223 38191959578180554340392835)
    ·
      refine ⟨57287939367270831510589253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38191959578180554340392835 57287939367270831510589253)
      ·
        refine ⟨10741488631363280908235485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57287939367270831510589253 10741488631363280908235485)
        ·
          refine ⟨4028058236761230340588307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10741488631363280908235485 4028058236761230340588307)
          ·
            refine ⟨6042087355141845510882461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028058236761230340588307 6042087355141845510882461)
            ·
              refine ⟨2265782758178192066580923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6042087355141845510882461 2265782758178192066580923)
              ·
                refine ⟨3398674137267288099871385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265782758178192066580923 3398674137267288099871385)
                ·
                  refine ⟨2549005602950466074903539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3398674137267288099871385 2549005602950466074903539)
                  ·
                    refine ⟨3823508404425699112355309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549005602950466074903539 3823508404425699112355309)
                    ·
                      refine ⟨1433815651659637167133241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823508404425699112355309 1433815651659637167133241)
                      ·
                        rfl

theorem cell23_2792346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_2792346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792346 prefixEnd_2792346 := by exact prefixLift 2792346
  have htrace : WordTrace (prefixWord ++ tailWord_2792346) baseStart_2792346 baseEnd_2792346 := by
    simpa [prefixWord, tailWord_2792346, baseEnd_2792346] using wordTrace_append hprefix tailTrace_2792346
  have hstable : (prefixWord ++ tailWord_2792346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792346).length < 2 ^ (prefixWord ++ tailWord_2792346).sum := by decide
  have hdescent : baseEnd_2792346 < baseStart_2792346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792352 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 1, 4, 2]
def baseStart_2792352 : Nat := 118140960795 + 2792352 * 2 ^ 59
def prefixEnd_2792352 : Nat := 4983230072969 + 3 ^ 40 * 2792352 * 2
def baseEnd_2792352 : Nat := 1433818732543564143658213

theorem tailTrace_2792352 : CollatzResearch.WordTrace tailWord_2792352 prefixEnd_2792352 1433818732543564143658213 := by
  unfold tailWord_2792352
  simp only [CollatzResearch.WordTrace]
  refine ⟨50922722189896537299549655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67896962919862049732732873 50922722189896537299549655)
  ·
    refine ⟨76384083284844805949324483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50922722189896537299549655 76384083284844805949324483)
    ·
      refine ⟨114576124927267208923986725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76384083284844805949324483 114576124927267208923986725)
      ·
        refine ⟨21483023423862601673247511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114576124927267208923986725 21483023423862601673247511)
        ·
          refine ⟨32224535135793902509871267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21483023423862601673247511 32224535135793902509871267)
          ·
            refine ⟨48336802703690853764806901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32224535135793902509871267 48336802703690853764806901)
            ·
              refine ⟨4531575253471017540450647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48336802703690853764806901 4531575253471017540450647)
              ·
                refine ⟨6797362880206526310675971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531575253471017540450647 6797362880206526310675971)
                ·
                  refine ⟨10196044320309789466013957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797362880206526310675971 10196044320309789466013957)
                  ·
                    refine ⟨1911758310058085524877617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10196044320309789466013957 1911758310058085524877617)
                    ·
                      refine ⟨1433818732543564143658213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911758310058085524877617 1433818732543564143658213)
                      ·
                        rfl

theorem cell23_2792352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_2792352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792352 prefixEnd_2792352 := by exact prefixLift 2792352
  have htrace : WordTrace (prefixWord ++ tailWord_2792352) baseStart_2792352 baseEnd_2792352 := by
    simpa [prefixWord, tailWord_2792352, baseEnd_2792352] using wordTrace_append hprefix tailTrace_2792352
  have hstable : (prefixWord ++ tailWord_2792352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792352).length < 2 ^ (prefixWord ++ tailWord_2792352).sum := by decide
  have hdescent : baseEnd_2792352 < baseStart_2792352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792372 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2792372 : Nat := 118140960795 + 2792372 * 2 ^ 59
def prefixEnd_2792372 : Nat := 4983230072969 + 3 ^ 40 * 2792372 * 2
def baseEnd_2792372 : Nat := 1433829002156654065408121

theorem tailTrace_2792372 : CollatzResearch.WordTrace tailWord_2792372 prefixEnd_2792372 1433829002156654065408121 := by
  unfold tailWord_2792372
  simp only [CollatzResearch.WordTrace]
  refine ⟨50923086919860309007413685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67897449226480412009884913 50923086919860309007413685)
  ·
    refine ⟨4774039398736903969445033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50923086919860309007413685 4774039398736903969445033)
    ·
      refine ⟨3580529549052677977083775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4774039398736903969445033 3580529549052677977083775)
      ·
        refine ⟨5370794323579016965625663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580529549052677977083775 5370794323579016965625663)
        ·
          refine ⟨8056191485368525448438495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370794323579016965625663 8056191485368525448438495)
          ·
            refine ⟨12084287228052788172657743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8056191485368525448438495 12084287228052788172657743)
            ·
              refine ⟨18126430842079182258986615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12084287228052788172657743 18126430842079182258986615)
              ·
                refine ⟨27189646263118773388479923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18126430842079182258986615 27189646263118773388479923)
                ·
                  refine ⟨40784469394678160082719885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27189646263118773388479923 40784469394678160082719885)
                  ·
                    refine ⟨15294176023004310031019957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40784469394678160082719885 15294176023004310031019957)
                    ·
                      refine ⟨1433829002156654065408121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15294176023004310031019957 1433829002156654065408121)
                      ·
                        rfl

theorem cell23_2792372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2792372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792372 prefixEnd_2792372 := by exact prefixLift 2792372
  have htrace : WordTrace (prefixWord ++ tailWord_2792372) baseStart_2792372 baseEnd_2792372 := by
    simpa [prefixWord, tailWord_2792372, baseEnd_2792372] using wordTrace_append hprefix tailTrace_2792372
  have hstable : (prefixWord ++ tailWord_2792372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792372).length < 2 ^ (prefixWord ++ tailWord_2792372).sum := by decide
  have hdescent : baseEnd_2792372 < baseStart_2792372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792392 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 7]
def baseStart_2792392 : Nat := 118140960795 + 2792392 * 2 ^ 59
def prefixEnd_2792392 : Nat := 4983230072969 + 3 ^ 40 * 2792392 * 2
def baseEnd_2792392 : Nat := 159315474641082665239781

theorem tailTrace_2792392 : CollatzResearch.WordTrace tailWord_2792392 prefixEnd_2792392 159315474641082665239781 := by
  unfold tailWord_2792392
  simp only [CollatzResearch.WordTrace]
  refine ⟨50923451649824080715277715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67897935533098774287036953 50923451649824080715277715)
  ·
    refine ⟨76385177474736121072916573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50923451649824080715277715 76385177474736121072916573)
    ·
      refine ⟨28644441553026045402343715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76385177474736121072916573 28644441553026045402343715)
      ·
        refine ⟨42966662329539068103515573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28644441553026045402343715 42966662329539068103515573)
        ·
          refine ⟨4028124593394287634704585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42966662329539068103515573 4028124593394287634704585)
          ·
            refine ⟨3021093445045715726028439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4028124593394287634704585 3021093445045715726028439)
            ·
              refine ⟨4531640167568573589042659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021093445045715726028439 4531640167568573589042659)
              ·
                refine ⟨6797460251352860383563989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531640167568573589042659 6797460251352860383563989)
                ·
                  refine ⟨159315474641082665239781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6797460251352860383563989 159315474641082665239781)
                  ·
                    rfl

theorem cell23_2792392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 7].length) (baseStart_2792392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792392 prefixEnd_2792392 := by exact prefixLift 2792392
  have htrace : WordTrace (prefixWord ++ tailWord_2792392) baseStart_2792392 baseEnd_2792392 := by
    simpa [prefixWord, tailWord_2792392, baseEnd_2792392] using wordTrace_append hprefix tailTrace_2792392
  have hstable : (prefixWord ++ tailWord_2792392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792392).length < 2 ^ (prefixWord ++ tailWord_2792392).sum := by decide
  have hdescent : baseEnd_2792392 < baseStart_2792392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792397 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2792397 : Nat := 118140960795 + 2792397 * 2 ^ 59
def prefixEnd_2792397 : Nat := 4983230072969 + 3 ^ 40 * 2792397 * 2
def baseEnd_2792397 : Nat := 1433841839173016467595507

theorem tailTrace_2792397 : CollatzResearch.WordTrace tailWord_2792397 prefixEnd_2792397 1433841839173016467595507 := by
  unfold tailWord_2792397
  simp only [CollatzResearch.WordTrace]
  refine ⟨101847085664630047284487445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67898057109753364856324963 101847085664630047284487445)
  ·
    refine ⟨4774082140529533466460349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101847085664630047284487445 4774082140529533466460349)
    ·
      refine ⟨1790280802698575049922631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4774082140529533466460349 1790280802698575049922631)
      ·
        refine ⟨2685421204047862574883947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790280802698575049922631 2685421204047862574883947)
        ·
          refine ⟨4028131806071793862325921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685421204047862574883947 4028131806071793862325921)
          ·
            refine ⟨3021098854553845396744441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4028131806071793862325921 3021098854553845396744441)
            ·
              refine ⟨2265824140915384047558331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3021098854553845396744441 2265824140915384047558331)
              ·
                refine ⟨3398736211373076071337497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265824140915384047558331 3398736211373076071337497)
                ·
                  refine ⟨2549052158529807053503123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3398736211373076071337497 2549052158529807053503123)
                  ·
                    refine ⟨3823578237794710580254685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549052158529807053503123 3823578237794710580254685)
                    ·
                      refine ⟨1433841839173016467595507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823578237794710580254685 1433841839173016467595507)
                      ·
                        rfl

theorem cell23_2792397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2792397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792397 prefixEnd_2792397 := by exact prefixLift 2792397
  have htrace : WordTrace (prefixWord ++ tailWord_2792397) baseStart_2792397 baseEnd_2792397 := by
    simpa [prefixWord, tailWord_2792397, baseEnd_2792397] using wordTrace_append hprefix tailTrace_2792397
  have hstable : (prefixWord ++ tailWord_2792397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792397).length < 2 ^ (prefixWord ++ tailWord_2792397).sum := by decide
  have hdescent : baseEnd_2792397 < baseStart_2792397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792428 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2792428 : Nat := 118140960795 + 2792428 * 2 ^ 59
def prefixEnd_2792428 : Nat := 4983230072969 + 3 ^ 40 * 2792428 * 2
def baseEnd_2792428 : Nat := 1433857757073305846307863

theorem tailTrace_2792428 : CollatzResearch.WordTrace tailWord_2792428 prefixEnd_2792428 1433857757073305846307863 := by
  unfold tailWord_2792428
  simp only [CollatzResearch.WordTrace]
  refine ⟨50924108163758869789432969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67898810885011826385910625 50924108163758869789432969)
  ·
    refine ⟨38193081122819152342074727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50924108163758869789432969 38193081122819152342074727)
    ·
      refine ⟨57289621684228728513112091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38193081122819152342074727 57289621684228728513112091)
      ·
        refine ⟨85934432526343092769668137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57289621684228728513112091 85934432526343092769668137)
        ·
          refine ⟨64450824394757319577251103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85934432526343092769668137 64450824394757319577251103)
          ·
            refine ⟨96676236592135979365876655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64450824394757319577251103 96676236592135979365876655)
            ·
              refine ⟨145014354888203969048814983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96676236592135979365876655 145014354888203969048814983)
              ·
                refine ⟨217521532332305953573222475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145014354888203969048814983 217521532332305953573222475)
                ·
                  refine ⟨326282298498458930359833713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217521532332305953573222475 326282298498458930359833713)
                  ·
                    refine ⟨244711723873844197769875285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 326282298498458930359833713 244711723873844197769875285)
                    ·
                      refine ⟨1433857757073305846307863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 244711723873844197769875285 1433857757073305846307863)
                      ·
                        rfl

theorem cell23_2792428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2792428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792428 prefixEnd_2792428 := by exact prefixLift 2792428
  have htrace : WordTrace (prefixWord ++ tailWord_2792428) baseStart_2792428 baseEnd_2792428 := by
    simpa [prefixWord, tailWord_2792428, baseEnd_2792428] using wordTrace_append hprefix tailTrace_2792428
  have hstable : (prefixWord ++ tailWord_2792428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792428).length < 2 ^ (prefixWord ++ tailWord_2792428).sum := by decide
  have hdescent : baseEnd_2792428 < baseStart_2792428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792445 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_2792445 : Nat := 118140960795 + 2792445 * 2 ^ 59
def prefixEnd_2792445 : Nat := 4983230072969 + 3 ^ 40 * 2792445 * 2
def baseEnd_2792445 : Nat := 1433866486244432279795285

theorem tailTrace_2792445 : CollatzResearch.WordTrace tailWord_2792445 prefixEnd_2792445 1433866486244432279795285 := by
  unfold tailWord_2792445
  simp only [CollatzResearch.WordTrace]
  refine ⟨101848836368456151482234789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67899224245637434321489859 101848836368456151482234789)
  ·
    refine ⟨19096656819085528402919023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101848836368456151482234789 19096656819085528402919023)
    ·
      refine ⟨28644985228628292604378535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19096656819085528402919023 28644985228628292604378535)
      ·
        refine ⟨42967477842942438906567803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28644985228628292604378535 42967477842942438906567803)
        ·
          refine ⟨64451216764413658359851705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42967477842942438906567803 64451216764413658359851705)
          ·
            refine ⟨48338412573310243769888779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64451216764413658359851705 48338412573310243769888779)
            ·
              refine ⟨72507618859965365654833169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48338412573310243769888779 72507618859965365654833169)
              ·
                refine ⟨54380714144974024241124877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72507618859965365654833169 54380714144974024241124877)
                ·
                  refine ⟨20392767804365259090421829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54380714144974024241124877 20392767804365259090421829)
                  ·
                    refine ⟨3823643963318486079454093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20392767804365259090421829 3823643963318486079454093)
                    ·
                      refine ⟨1433866486244432279795285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823643963318486079454093 1433866486244432279795285)
                      ·
                        rfl

theorem cell23_2792445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_2792445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792445 prefixEnd_2792445 := by exact prefixLift 2792445
  have htrace : WordTrace (prefixWord ++ tailWord_2792445) baseStart_2792445 baseEnd_2792445 := by
    simpa [prefixWord, tailWord_2792445, baseEnd_2792445] using wordTrace_append hprefix tailTrace_2792445
  have hstable : (prefixWord ++ tailWord_2792445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792445).length < 2 ^ (prefixWord ++ tailWord_2792445).sum := by decide
  have hdescent : baseEnd_2792445 < baseStart_2792445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792448 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 12]
def baseStart_2792448 : Nat := 118140960795 + 2792448 * 2 ^ 59
def prefixEnd_2792448 : Nat := 4983230072969 + 3 ^ 40 * 2792448 * 2
def baseEnd_2792448 : Nat := 159318669631821752006419

theorem tailTrace_2792448 : CollatzResearch.WordTrace tailWord_2792448 prefixEnd_2792448 159318669631821752006419 := by
  unfold tailWord_2792448
  simp only [CollatzResearch.WordTrace]
  refine ⟨50924472893722641497296999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67899297191630188663062665 50924472893722641497296999)
  ·
    refine ⟨76386709340583962245945499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50924472893722641497296999 76386709340583962245945499)
    ·
      refine ⟨114580064010875943368918249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76386709340583962245945499 114580064010875943368918249)
      ·
        refine ⟨85935048008156957526688687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114580064010875943368918249 85935048008156957526688687)
        ·
          refine ⟨128902572012235436290033031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85935048008156957526688687 128902572012235436290033031)
          ·
            refine ⟨193353858018353154435049547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128902572012235436290033031 193353858018353154435049547)
            ·
              refine ⟨290030787027529731652574321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193353858018353154435049547 290030787027529731652574321)
              ·
                refine ⟨217523090270647298739430741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290030787027529731652574321 217523090270647298739430741)
                ·
                  refine ⟨159318669631821752006419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 217523090270647298739430741 159318669631821752006419)
                  ·
                    rfl

theorem cell23_2792448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 12].length) (baseStart_2792448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792448 prefixEnd_2792448 := by exact prefixLift 2792448
  have htrace : WordTrace (prefixWord ++ tailWord_2792448) baseStart_2792448 baseEnd_2792448 := by
    simpa [prefixWord, tailWord_2792448, baseEnd_2792448] using wordTrace_append hprefix tailTrace_2792448
  have hstable : (prefixWord ++ tailWord_2792448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792448).length < 2 ^ (prefixWord ++ tailWord_2792448).sum := by decide
  have hdescent : baseEnd_2792448 < baseStart_2792448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792476 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_2792476 : Nat := 118140960795 + 2792476 * 2 ^ 59
def prefixEnd_2792476 : Nat := 4983230072969 + 3 ^ 40 * 2792476 * 2
def baseEnd_2792476 : Nat := 1433882404144721658507643

theorem tailTrace_2792476 : CollatzResearch.WordTrace tailWord_2792476 prefixEnd_2792476 1433882404144721658507643 := by
  unfold tailWord_2792476
  simp only [CollatzResearch.WordTrace]
  refine ⟨50924983515671921888306641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67899978020895895851075521 50924983515671921888306641)
  ·
    refine ⟨38193737636753941416229981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50924983515671921888306641 38193737636753941416229981)
    ·
      refine ⟨14322651613782728031086243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38193737636753941416229981 14322651613782728031086243)
      ·
        refine ⟨21483977420674092046629365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14322651613782728031086243 21483977420674092046629365)
        ·
          refine ⟨2014122883188196129371503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21483977420674092046629365 2014122883188196129371503)
          ·
            refine ⟨3021184324782294194057255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014122883188196129371503 3021184324782294194057255)
            ·
              refine ⟨4531776487173441291085883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021184324782294194057255 4531776487173441291085883)
              ·
                refine ⟨6797664730760161936628825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531776487173441291085883 6797664730760161936628825)
                ·
                  refine ⟨5098248548070121452471619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6797664730760161936628825 5098248548070121452471619)
                  ·
                    refine ⟨7647372822105182178707429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5098248548070121452471619 7647372822105182178707429)
                    ·
                      refine ⟨1433882404144721658507643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7647372822105182178707429 1433882404144721658507643)
                      ·
                        rfl

theorem cell23_2792476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_2792476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792476 prefixEnd_2792476 := by exact prefixLift 2792476
  have htrace : WordTrace (prefixWord ++ tailWord_2792476) baseStart_2792476 baseEnd_2792476 := by
    simpa [prefixWord, tailWord_2792476, baseEnd_2792476] using wordTrace_append hprefix tailTrace_2792476
  have hstable : (prefixWord ++ tailWord_2792476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792476).length < 2 ^ (prefixWord ++ tailWord_2792476).sum := by decide
  have hdescent : baseEnd_2792476 < baseStart_2792476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792479 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 3]
def baseStart_2792479 : Nat := 118140960795 + 2792479 * 2 ^ 59
def prefixEnd_2792479 : Nat := 4983230072969 + 3 ^ 40 * 2792479 * 2
def baseEnd_2792479 : Nat := 1433883944586685146770129

theorem tailTrace_2792479 : CollatzResearch.WordTrace tailWord_2792479 prefixEnd_2792479 1433883944586685146770129 := by
  unfold tailWord_2792479
  simp only [CollatzResearch.WordTrace]
  refine ⟨101850076450332975288972491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67900050966888650192648327 101850076450332975288972491)
  ·
    refine ⟨152775114675499462933458737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101850076450332975288972491 152775114675499462933458737)
    ·
      refine ⟨114581336006624597200094053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152775114675499462933458737 114581336006624597200094053)
      ·
        refine ⟨21484000501242111975017635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114581336006624597200094053 21484000501242111975017635)
        ·
          refine ⟨32226000751863167962526453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21484000501242111975017635 32226000751863167962526453)
          ·
            refine ⟨3021187570487171996486855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32226000751863167962526453 3021187570487171996486855)
            ·
              refine ⟨4531781355730757994730283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021187570487171996486855 4531781355730757994730283)
              ·
                refine ⟨6797672033596136992095425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531781355730757994730283 6797672033596136992095425)
                ·
                  refine ⟨5098254025197102744071569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6797672033596136992095425 5098254025197102744071569)
                  ·
                    refine ⟨3823690518897827058053677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5098254025197102744071569 3823690518897827058053677)
                    ·
                      refine ⟨1433883944586685146770129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823690518897827058053677 1433883944586685146770129)
                      ·
                        rfl

theorem cell23_2792479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_2792479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792479 prefixEnd_2792479 := by exact prefixLift 2792479
  have htrace : WordTrace (prefixWord ++ tailWord_2792479) baseStart_2792479 baseEnd_2792479 := by
    simpa [prefixWord, tailWord_2792479, baseEnd_2792479] using wordTrace_append hprefix tailTrace_2792479
  have hstable : (prefixWord ++ tailWord_2792479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792479).length < 2 ^ (prefixWord ++ tailWord_2792479).sum := by decide
  have hdescent : baseEnd_2792479 < baseStart_2792479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792492 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 3]
def baseStart_2792492 : Nat := 118140960795 + 2792492 * 2 ^ 59
def prefixEnd_2792492 : Nat := 4983230072969 + 3 ^ 40 * 2792492 * 2
def baseEnd_2792492 : Nat := 1433890619835193595907569

theorem tailTrace_2792492 : CollatzResearch.WordTrace tailWord_2792492 prefixEnd_2792492 1433890619835193595907569 := by
  unfold tailWord_2792492
  simp only [CollatzResearch.WordTrace]
  refine ⟨50925275299642939254597865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67900367066190585672797153 50925275299642939254597865)
  ·
    refine ⟨38193956474732204440948399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50925275299642939254597865 38193956474732204440948399)
    ·
      refine ⟨57290934712098306661422599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38193956474732204440948399 57290934712098306661422599)
      ·
        refine ⟨85936402068147459992133899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57290934712098306661422599 85936402068147459992133899)
        ·
          refine ⟨128904603102221189988200849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85936402068147459992133899 128904603102221189988200849)
          ·
            refine ⟨96678452326665892491150637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128904603102221189988200849 96678452326665892491150637)
            ·
              refine ⟨36254419622499709684181489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96678452326665892491150637 36254419622499709684181489)
              ·
                refine ⟨27190814716874782263136117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36254419622499709684181489 27190814716874782263136117)
                ·
                  refine ⟨2549138879707010837169011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27190814716874782263136117 2549138879707010837169011)
                  ·
                    refine ⟨3823708319560516255753517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549138879707010837169011 3823708319560516255753517)
                    ·
                      refine ⟨1433890619835193595907569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823708319560516255753517 1433890619835193595907569)
                      ·
                        rfl

theorem cell23_2792492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_2792492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792492 prefixEnd_2792492 := by exact prefixLift 2792492
  have htrace : WordTrace (prefixWord ++ tailWord_2792492) baseStart_2792492 baseEnd_2792492 := by
    simpa [prefixWord, tailWord_2792492, baseEnd_2792492] using wordTrace_append hprefix tailTrace_2792492
  have hstable : (prefixWord ++ tailWord_2792492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792492).length < 2 ^ (prefixWord ++ tailWord_2792492).sum := by decide
  have hdescent : baseEnd_2792492 < baseStart_2792492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792502 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2792502 : Nat := 118140960795 + 2792502 * 2 ^ 59
def prefixEnd_2792502 : Nat := 4983230072969 + 3 ^ 40 * 2792502 * 2
def baseEnd_2792502 : Nat := 1433895754641738556782523

theorem tailTrace_2792502 : CollatzResearch.WordTrace tailWord_2792502 prefixEnd_2792502 1433895754641738556782523 := by
  unfold tailWord_2792502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6365682208078103138566235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67900610219499766811373173 6365682208078103138566235)
  ·
    refine ⟨9548523312117154707849353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6365682208078103138566235 9548523312117154707849353)
    ·
      refine ⟨7161392484087866030887015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9548523312117154707849353 7161392484087866030887015)
      ·
        refine ⟨10742088726131799046330523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7161392484087866030887015 10742088726131799046330523)
        ·
          refine ⟨16113133089197698569495785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10742088726131799046330523 16113133089197698569495785)
          ·
            refine ⟨12084849816898273927121839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16113133089197698569495785 12084849816898273927121839)
            ·
              refine ⟨18127274725347410890682759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12084849816898273927121839 18127274725347410890682759)
              ·
                refine ⟨27190912088021116336024139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18127274725347410890682759 27190912088021116336024139)
                ·
                  refine ⟨40786368132031674504036209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27190912088021116336024139 40786368132031674504036209)
                  ·
                    refine ⟨30589776099023755878027157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40786368132031674504036209 30589776099023755878027157)
                    ·
                      refine ⟨1433895754641738556782523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30589776099023755878027157 1433895754641738556782523)
                      ·
                        rfl

theorem cell23_2792502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2792502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792502 prefixEnd_2792502 := by exact prefixLift 2792502
  have htrace : WordTrace (prefixWord ++ tailWord_2792502) baseStart_2792502 baseEnd_2792502 := by
    simpa [prefixWord, tailWord_2792502, baseEnd_2792502] using wordTrace_append hprefix tailTrace_2792502
  have hstable : (prefixWord ++ tailWord_2792502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792502).length < 2 ^ (prefixWord ++ tailWord_2792502).sum := by decide
  have hdescent : baseEnd_2792502 < baseStart_2792502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792509 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2792509 : Nat := 118140960795 + 2792509 * 2 ^ 59
def prefixEnd_2792509 : Nat := 4983230072969 + 3 ^ 40 * 2792509 * 2
def baseEnd_2792509 : Nat := 1433899349006320029394991

theorem tailTrace_2792509 : CollatzResearch.WordTrace tailWord_2792509 prefixEnd_2792509 1433899349006320029394991 := by
  unfold tailWord_2792509
  simp only [CollatzResearch.WordTrace]
  refine ⟨101851170640224290412564581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67900780426816193608376387 101851170640224290412564581)
  ·
    refine ⟨19097094495042054452355859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101851170640224290412564581 19097094495042054452355859)
    ·
      refine ⟨28645641742563081678533789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19097094495042054452355859 28645641742563081678533789)
      ·
        refine ⟨10742115653461155629450171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28645641742563081678533789 10742115653461155629450171)
        ·
          refine ⟨16113173480191733444175257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10742115653461155629450171 16113173480191733444175257)
          ·
            refine ⟨12084880110143800083131443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16113173480191733444175257 12084880110143800083131443)
            ·
              refine ⟨18127320165215700124697165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12084880110143800083131443 18127320165215700124697165)
              ·
                refine ⟨6797745061955887546761437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18127320165215700124697165 6797745061955887546761437)
                ·
                  refine ⟨2549154398233457830035539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6797745061955887546761437 2549154398233457830035539)
                  ·
                    refine ⟨3823731597350186745053309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549154398233457830035539 3823731597350186745053309)
                    ·
                      refine ⟨1433899349006320029394991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823731597350186745053309 1433899349006320029394991)
                      ·
                        rfl

theorem cell23_2792509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2792509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792509 prefixEnd_2792509 := by exact prefixLift 2792509
  have htrace : WordTrace (prefixWord ++ tailWord_2792509) baseStart_2792509 baseEnd_2792509 := by
    simpa [prefixWord, tailWord_2792509, baseEnd_2792509] using wordTrace_append hprefix tailTrace_2792509
  have hstable : (prefixWord ++ tailWord_2792509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792509).length < 2 ^ (prefixWord ++ tailWord_2792509).sum := by decide
  have hdescent : baseEnd_2792509 < baseStart_2792509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792532 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_2792532 : Nat := 118140960795 + 2792532 * 2 ^ 59
def prefixEnd_2792532 : Nat := 4983230072969 + 3 ^ 40 * 2792532 * 2
def baseEnd_2792532 : Nat := 1433911159061373439407385

theorem tailTrace_2792532 : CollatzResearch.WordTrace tailWord_2792532 prefixEnd_2792532 1433911159061373439407385 := by
  unfold tailWord_2792532
  simp only [CollatzResearch.WordTrace]
  refine ⟨50926004759570482670325925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67901339679427310227101233 50926004759570482670325925)
  ·
    refine ⟨9548625892419465500686111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50926004759570482670325925 9548625892419465500686111)
    ·
      refine ⟨14322938838629198251029167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9548625892419465500686111 14322938838629198251029167)
      ·
        refine ⟨21484408257943797376543751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14322938838629198251029167 21484408257943797376543751)
        ·
          refine ⟨32226612386915696064815627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21484408257943797376543751 32226612386915696064815627)
          ·
            refine ⟨48339918580373544097223441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32226612386915696064815627 48339918580373544097223441)
            ·
              refine ⟨36254938935280158072917581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48339918580373544097223441 36254938935280158072917581)
              ·
                refine ⟨13595602100730059277344093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36254938935280158072917581 13595602100730059277344093)
                ·
                  refine ⟨5098350787773772229004035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13595602100730059277344093 5098350787773772229004035)
                  ·
                    refine ⟨7647526181660658343506053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5098350787773772229004035 7647526181660658343506053)
                    ·
                      refine ⟨1433911159061373439407385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7647526181660658343506053 1433911159061373439407385)
                      ·
                        rfl

theorem cell23_2792532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_2792532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792532 prefixEnd_2792532 := by exact prefixLift 2792532
  have htrace : WordTrace (prefixWord ++ tailWord_2792532) baseStart_2792532 baseEnd_2792532 := by
    simpa [prefixWord, tailWord_2792532, baseEnd_2792532] using wordTrace_append hprefix tailTrace_2792532
  have hstable : (prefixWord ++ tailWord_2792532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792532).length < 2 ^ (prefixWord ++ tailWord_2792532).sum := by decide
  have hdescent : baseEnd_2792532 < baseStart_2792532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792535 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_2792535 : Nat := 118140960795 + 2792535 * 2 ^ 59
def prefixEnd_2792535 : Nat := 4983230072969 + 3 ^ 40 * 2792535 * 2
def baseEnd_2792535 : Nat := 1433912699503336927669871

theorem tailTrace_2792535 : CollatzResearch.WordTrace tailWord_2792535 prefixEnd_2792535 1433912699503336927669871 := by
  unfold tailWord_2792535
  simp only [CollatzResearch.WordTrace]
  refine ⟨101852118938130096853011059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67901412625420064568674039 101852118938130096853011059)
  ·
    refine ⟨152778178407195145279516589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101852118938130096853011059 152778178407195145279516589)
    ·
      refine ⟨57291816902698179479818721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152778178407195145279516589 57291816902698179479818721)
      ·
        refine ⟨42968862677023634609864041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57291816902698179479818721 42968862677023634609864041)
        ·
          refine ⟨32226647007767725957398031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42968862677023634609864041 32226647007767725957398031)
          ·
            refine ⟨48339970511651588936097047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32226647007767725957398031 48339970511651588936097047)
            ·
              refine ⟨72509955767477383404145571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48339970511651588936097047 72509955767477383404145571)
              ·
                refine ⟨108764933651216075106218357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72509955767477383404145571 108764933651216075106218357)
                ·
                  refine ⟨10196712529801507041207971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108764933651216075106218357 10196712529801507041207971)
                  ·
                    refine ⟨15295068794702260561811957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10196712529801507041207971 15295068794702260561811957)
                    ·
                      refine ⟨1433912699503336927669871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15295068794702260561811957 1433912699503336927669871)
                      ·
                        rfl

theorem cell23_2792535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_2792535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792535 prefixEnd_2792535 := by exact prefixLift 2792535
  have htrace : WordTrace (prefixWord ++ tailWord_2792535) baseStart_2792535 baseEnd_2792535 := by
    simpa [prefixWord, tailWord_2792535, baseEnd_2792535] using wordTrace_append hprefix tailTrace_2792535
  have hstable : (prefixWord ++ tailWord_2792535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792535).length < 2 ^ (prefixWord ++ tailWord_2792535).sum := by decide
  have hdescent : baseEnd_2792535 < baseStart_2792535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792595 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 5]
def baseStart_2792595 : Nat := 118140960795 + 2792595 * 2 ^ 59
def prefixEnd_2792595 : Nat := 4983230072969 + 3 ^ 40 * 2792595 * 2
def baseEnd_2792595 : Nat := 1433943508342606692919595

theorem tailTrace_2792595 : CollatzResearch.WordTrace tailWord_2792595 prefixEnd_2792595 1433943508342606692919595 := by
  unfold tailWord_2792595
  simp only [CollatzResearch.WordTrace]
  refine ⟨101854307317912727100195239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67902871545275151400130159 101854307317912727100195239)
  ·
    refine ⟨152781460976869090650292859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101854307317912727100195239 152781460976869090650292859)
    ·
      refine ⟨229172191465303635975439289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152781460976869090650292859 229172191465303635975439289)
      ·
        refine ⟨171879143598977726981579467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229172191465303635975439289 171879143598977726981579467)
        ·
          refine ⟨257818715398466590472369201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171879143598977726981579467 257818715398466590472369201)
          ·
            refine ⟨193364036548849942854276901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257818715398466590472369201 193364036548849942854276901)
            ·
              refine ⟨36255756852909364285176919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193364036548849942854276901 36255756852909364285176919)
              ·
                refine ⟨54383635279364046427765379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36255756852909364285176919 54383635279364046427765379)
                ·
                  refine ⟨81575452919046069641648069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54383635279364046427765379 81575452919046069641648069)
                  ·
                    refine ⟨15295397422321138057809013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81575452919046069641648069 15295397422321138057809013)
                    ·
                      refine ⟨1433943508342606692919595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15295397422321138057809013 1433943508342606692919595)
                      ·
                        rfl

theorem cell23_2792595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_2792595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792595 prefixEnd_2792595 := by exact prefixLift 2792595
  have htrace : WordTrace (prefixWord ++ tailWord_2792595) baseStart_2792595 baseEnd_2792595 := by
    simpa [prefixWord, tailWord_2792595, baseEnd_2792595] using wordTrace_append hprefix tailTrace_2792595
  have hstable : (prefixWord ++ tailWord_2792595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792595).length < 2 ^ (prefixWord ++ tailWord_2792595).sum := by decide
  have hdescent : baseEnd_2792595 < baseStart_2792595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792599 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_2792599 : Nat := 118140960795 + 2792599 * 2 ^ 59
def prefixEnd_2792599 : Nat := 4983230072969 + 3 ^ 40 * 2792599 * 2
def baseEnd_2792599 : Nat := 1433945562265224677269577

theorem tailTrace_2792599 : CollatzResearch.WordTrace tailWord_2792599 prefixEnd_2792599 1433945562265224677269577 := by
  unfold tailWord_2792599
  simp only [CollatzResearch.WordTrace]
  refine ⟨101854453209898235783340851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67902968806598823855560567 101854453209898235783340851)
  ·
    refine ⟨152781679814847353675011277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101854453209898235783340851 152781679814847353675011277)
    ·
      refine ⟨57293129930567757628129229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152781679814847353675011277 57293129930567757628129229)
      ·
        refine ⟨21484923723962909110548461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57293129930567757628129229 21484923723962909110548461)
        ·
          refine ⟨8056846396486090916455673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21484923723962909110548461 8056846396486090916455673)
          ·
            refine ⟨6042634797364568187341755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8056846396486090916455673 6042634797364568187341755)
            ·
              refine ⟨9063952196046852281012633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042634797364568187341755 9063952196046852281012633)
              ·
                refine ⟨6797964147035139210759475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9063952196046852281012633 6797964147035139210759475)
                ·
                  refine ⟨10196946220552708816139213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797964147035139210759475 10196946220552708816139213)
                  ·
                    refine ⟨3823854832707265806052205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10196946220552708816139213 3823854832707265806052205)
                    ·
                      refine ⟨1433945562265224677269577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3823854832707265806052205 1433945562265224677269577)
                      ·
                        rfl

theorem cell23_2792599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_2792599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792599 prefixEnd_2792599 := by exact prefixLift 2792599
  have htrace : WordTrace (prefixWord ++ tailWord_2792599) baseStart_2792599 baseEnd_2792599 := by
    simpa [prefixWord, tailWord_2792599, baseEnd_2792599] using wordTrace_append hprefix tailTrace_2792599
  have hstable : (prefixWord ++ tailWord_2792599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792599).length < 2 ^ (prefixWord ++ tailWord_2792599).sum := by decide
  have hdescent : baseEnd_2792599 < baseStart_2792599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792639 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 1, 4, 2]
def baseStart_2792639 : Nat := 118140960795 + 2792639 * 2 ^ 59
def prefixEnd_2792639 : Nat := 4983230072969 + 3 ^ 40 * 2792639 * 2
def baseEnd_2792639 : Nat := 1433966101491404520769393

theorem tailTrace_2792639 : CollatzResearch.WordTrace tailWord_2792639 prefixEnd_2792639 1433966101491404520769393 := by
  unfold tailWord_2792639
  simp only [CollatzResearch.WordTrace]
  refine ⟨101855912129753322614796971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67903941419835548409864647 101855912129753322614796971)
  ·
    refine ⟨152783868194629983922195457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101855912129753322614796971 152783868194629983922195457)
    ·
      refine ⟨114587901145972487941646593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152783868194629983922195457 114587901145972487941646593)
      ·
        refine ⟨85940925859479365956234945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114587901145972487941646593 85940925859479365956234945)
        ·
          refine ⟨64455694394609524467176209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85940925859479365956234945 64455694394609524467176209)
          ·
            refine ⟨48341770795957143350382157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64455694394609524467176209 48341770795957143350382157)
            ·
              refine ⟨18128164048483928756393309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48341770795957143350382157 18128164048483928756393309)
              ·
                refine ⟨6798061518181473283647491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18128164048483928756393309 6798061518181473283647491)
                ·
                  refine ⟨10197092277272209925471237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6798061518181473283647491 10197092277272209925471237)
                  ·
                    refine ⟨1911954801988539361025857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10197092277272209925471237 1911954801988539361025857)
                    ·
                      refine ⟨1433966101491404520769393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911954801988539361025857 1433966101491404520769393)
                      ·
                        rfl

theorem cell23_2792639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_2792639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792639 prefixEnd_2792639 := by exact prefixLift 2792639
  have htrace : WordTrace (prefixWord ++ tailWord_2792639) baseStart_2792639 baseEnd_2792639 := by
    simpa [prefixWord, tailWord_2792639, baseEnd_2792639] using wordTrace_append hprefix tailTrace_2792639
  have hstable : (prefixWord ++ tailWord_2792639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792639).length < 2 ^ (prefixWord ++ tailWord_2792639).sum := by decide
  have hdescent : baseEnd_2792639 < baseStart_2792639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792660 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2792660 : Nat := 118140960795 + 2792660 * 2 ^ 59
def prefixEnd_2792660 : Nat := 4983230072969 + 3 ^ 40 * 2792660 * 2
def baseEnd_2792660 : Nat := 1433976884585148938606797

theorem tailTrace_2792660 : CollatzResearch.WordTrace tailWord_2792660 prefixEnd_2792660 1433976884585148938606797 := by
  unfold tailWord_2792660
  simp only [CollatzResearch.WordTrace]
  refine ⟨50928339031338621600655717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67904452041784828800874289 50928339031338621600655717)
  ·
    refine ⟨9549063568375991550122947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50928339031338621600655717 9549063568375991550122947)
    ·
      refine ⟨14323595352563987325184421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9549063568375991550122947 14323595352563987325184421)
      ·
        refine ⟨2685674128605747623472079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14323595352563987325184421 2685674128605747623472079)
        ·
          refine ⟨4028511192908621435208119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685674128605747623472079 4028511192908621435208119)
          ·
            refine ⟨6042766789362932152812179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028511192908621435208119 6042766789362932152812179)
            ·
              refine ⟨9064150184044398229218269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042766789362932152812179 9064150184044398229218269)
              ·
                refine ⟨3399056319016649335956851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9064150184044398229218269 3399056319016649335956851)
                ·
                  refine ⟨5098584478524974003935277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399056319016649335956851 5098584478524974003935277)
                  ·
                    refine ⟨1911969179446865251475729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5098584478524974003935277 1911969179446865251475729)
                    ·
                      refine ⟨1433976884585148938606797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911969179446865251475729 1433976884585148938606797)
                      ·
                        rfl

theorem cell23_2792660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2792660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792660 prefixEnd_2792660 := by exact prefixLift 2792660
  have htrace : WordTrace (prefixWord ++ tailWord_2792660) baseStart_2792660 baseEnd_2792660 := by
    simpa [prefixWord, tailWord_2792660, baseEnd_2792660] using wordTrace_append hprefix tailTrace_2792660
  have hstable : (prefixWord ++ tailWord_2792660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792660).length < 2 ^ (prefixWord ++ tailWord_2792660).sum := by decide
  have hdescent : baseEnd_2792660 < baseStart_2792660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792673 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_2792673 : Nat := 118140960795 + 2792673 * 2 ^ 59
def prefixEnd_2792673 : Nat := 4983230072969 + 3 ^ 40 * 2792673 * 2
def baseEnd_2792673 : Nat := 1433983559833657387744237

theorem tailTrace_2792673 : CollatzResearch.WordTrace tailWord_2792673 prefixEnd_2792673 1433983559833657387744237 := by
  unfold tailWord_2792673
  simp only [CollatzResearch.WordTrace]
  refine ⟨101857152211630146421534673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67904768141086764281023115 101857152211630146421534673)
  ·
    refine ⟨76392864158722609816151005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101857152211630146421534673 76392864158722609816151005)
    ·
      refine ⟨28647324059520978681056627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76392864158722609816151005 28647324059520978681056627)
      ·
        refine ⟨42970986089281468021584941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28647324059520978681056627 42970986089281468021584941)
        ·
          refine ⟨16114119783480550508094353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42970986089281468021584941 16114119783480550508094353)
          ·
            refine ⟨12085589837610412881070765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16114119783480550508094353 12085589837610412881070765)
            ·
              refine ⟨4532096189103904830401537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12085589837610412881070765 4532096189103904830401537)
              ·
                refine ⟨3399072141827928622801153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4532096189103904830401537 3399072141827928622801153)
                ·
                  refine ⟨2549304106370946467100865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3399072141827928622801153 2549304106370946467100865)
                  ·
                    refine ⟨1911978079778209850325649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2549304106370946467100865 1911978079778209850325649)
                    ·
                      refine ⟨1433983559833657387744237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911978079778209850325649 1433983559833657387744237)
                      ·
                        rfl

theorem cell23_2792673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_2792673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792673 prefixEnd_2792673 := by exact prefixLift 2792673
  have htrace : WordTrace (prefixWord ++ tailWord_2792673) baseStart_2792673 baseEnd_2792673 := by
    simpa [prefixWord, tailWord_2792673, baseEnd_2792673] using wordTrace_append hprefix tailTrace_2792673
  have hstable : (prefixWord ++ tailWord_2792673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792673).length < 2 ^ (prefixWord ++ tailWord_2792673).sum := by decide
  have hdescent : baseEnd_2792673 < baseStart_2792673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792690 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_2792690 : Nat := 118140960795 + 2792690 * 2 ^ 59
def prefixEnd_2792690 : Nat := 4983230072969 + 3 ^ 40 * 2792690 * 2
def baseEnd_2792690 : Nat := 1433992289004783821231659

theorem tailTrace_2792690 : CollatzResearch.WordTrace tailWord_2792690 prefixEnd_2792690 1433992289004783821231659 := by
  unfold tailWord_2792690
  simp only [CollatzResearch.WordTrace]
  refine ⟨25464443063142139581225881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67905181501712372216602349 25464443063142139581225881)
  ·
    refine ⟨19098332297356604685919411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25464443063142139581225881 19098332297356604685919411)
    ·
      refine ⟨28647498446034907028879117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19098332297356604685919411 28647498446034907028879117)
      ·
        refine ⟨10742811917263090135829669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28647498446034907028879117 10742811917263090135829669)
        ·
          refine ⟨2014277234486829400468063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10742811917263090135829669 2014277234486829400468063)
          ·
            refine ⟨3021415851730244100702095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014277234486829400468063 3021415851730244100702095)
            ·
              refine ⟨4532123777595366151053143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021415851730244100702095 4532123777595366151053143)
              ·
                refine ⟨6798185666393049226579715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532123777595366151053143 6798185666393049226579715)
                ·
                  refine ⟨10197278499589573839869573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6798185666393049226579715 10197278499589573839869573)
                  ·
                    refine ⟨1911989718673045094975545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10197278499589573839869573 1911989718673045094975545)
                    ·
                      refine ⟨1433992289004783821231659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911989718673045094975545 1433992289004783821231659)
                      ·
                        rfl

theorem cell23_2792690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_2792690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792690 prefixEnd_2792690 := by exact prefixLift 2792690
  have htrace : WordTrace (prefixWord ++ tailWord_2792690) baseStart_2792690 baseEnd_2792690 := by
    simpa [prefixWord, tailWord_2792690, baseEnd_2792690] using wordTrace_append hprefix tailTrace_2792690
  have hstable : (prefixWord ++ tailWord_2792690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792690).length < 2 ^ (prefixWord ++ tailWord_2792690).sum := by decide
  have hdescent : baseEnd_2792690 < baseStart_2792690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792756 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2792756 : Nat := 118140960795 + 2792756 * 2 ^ 59
def prefixEnd_2792756 : Nat := 4983230072969 + 3 ^ 40 * 2792756 * 2
def baseEnd_2792756 : Nat := 478008726242660187668785

theorem tailTrace_2792756 : CollatzResearch.WordTrace tailWord_2792756 prefixEnd_2792756 478008726242660187668785 := by
  unfold tailWord_2792756
  simp only [CollatzResearch.WordTrace]
  refine ⟨50930089735164725798403061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67906786313552967731204081 50930089735164725798403061)
  ·
    refine ⟨4774695912671693043600287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50930089735164725798403061 4774695912671693043600287)
    ·
      refine ⟨7162043869007539565400431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4774695912671693043600287 7162043869007539565400431)
      ·
        refine ⟨10743065803511309348100647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7162043869007539565400431 10743065803511309348100647)
        ·
          refine ⟨16114598705266964022150971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10743065803511309348100647 16114598705266964022150971)
          ·
            refine ⟨24171898057900446033226457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16114598705266964022150971 24171898057900446033226457)
            ·
              refine ⟨18128923543425334524919843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24171898057900446033226457 18128923543425334524919843)
              ·
                refine ⟨27193385315138001787379765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18128923543425334524919843 27193385315138001787379765)
                ·
                  refine ⟨2549379873294187667566853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27193385315138001787379765 2549379873294187667566853)
                  ·
                    refine ⟨478008726242660187668785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2549379873294187667566853 478008726242660187668785)
                    ·
                      rfl

theorem cell23_2792756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2792756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792756 prefixEnd_2792756 := by exact prefixLift 2792756
  have htrace : WordTrace (prefixWord ++ tailWord_2792756) baseStart_2792756 baseEnd_2792756 := by
    simpa [prefixWord, tailWord_2792756, baseEnd_2792756] using wordTrace_append hprefix tailTrace_2792756
  have hstable : (prefixWord ++ tailWord_2792756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792756).length < 2 ^ (prefixWord ++ tailWord_2792756).sum := by decide
  have hdescent : baseEnd_2792756 < baseStart_2792756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792797 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2792797 : Nat := 118140960795 + 2792797 * 2 ^ 59
def prefixEnd_2792797 : Nat := 4983230072969 + 3 ^ 40 * 2792797 * 2
def baseEnd_2792797 : Nat := 1434047231434814902593667

theorem tailTrace_2792797 : CollatzResearch.WordTrace tailWord_2792797 prefixEnd_2792797 1434047231434814902593667 := by
  unfold tailWord_2792797
  simp only [CollatzResearch.WordTrace]
  refine ⟨101861674863180915599048645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67907783242120610399365763 101861674863180915599048645)
  ·
    refine ⟨19099064036846421674821621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101861674863180915599048645 19099064036846421674821621)
    ·
      refine ⟨1790537253454352032014527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19099064036846421674821621 1790537253454352032014527)
      ·
        refine ⟨2685805880181528048021791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790537253454352032014527 2685805880181528048021791)
        ·
          refine ⟨4028708820272292072032687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685805880181528048021791 4028708820272292072032687)
          ·
            refine ⟨6043063230408438108049031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028708820272292072032687 6043063230408438108049031)
            ·
              refine ⟨9064594845612657162073547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043063230408438108049031 9064594845612657162073547)
              ·
                refine ⟨13596892268418985743110321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9064594845612657162073547 13596892268418985743110321)
                ·
                  refine ⟨10197669201314239307332741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13596892268418985743110321 10197669201314239307332741)
                  ·
                    refine ⟨1912062975246419870124889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10197669201314239307332741 1912062975246419870124889)
                    ·
                      refine ⟨1434047231434814902593667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912062975246419870124889 1434047231434814902593667)
                      ·
                        rfl

theorem cell23_2792797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2792797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792797 prefixEnd_2792797 := by exact prefixLift 2792797
  have htrace : WordTrace (prefixWord ++ tailWord_2792797) baseStart_2792797 baseEnd_2792797 := by
    simpa [prefixWord, tailWord_2792797, baseEnd_2792797] using wordTrace_append hprefix tailTrace_2792797
  have hstable : (prefixWord ++ tailWord_2792797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792797).length < 2 ^ (prefixWord ++ tailWord_2792797).sum := by decide
  have hdescent : baseEnd_2792797 < baseStart_2792797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792813 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_2792813 : Nat := 118140960795 + 2792813 * 2 ^ 59
def prefixEnd_2792813 : Nat := 4983230072969 + 3 ^ 40 * 2792813 * 2
def baseEnd_2792813 : Nat := 1434055447125286839993593

theorem tailTrace_2792813 : CollatzResearch.WordTrace tailWord_2792813 prefixEnd_2792813 1434055447125286839993593 := by
  unfold tailWord_2792813
  simp only [CollatzResearch.WordTrace]
  refine ⟨101862258431122950331631093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67908172287415300221087395 101862258431122950331631093)
  ·
    refine ⟨9549586727917776593590415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101862258431122950331631093 9549586727917776593590415)
    ·
      refine ⟨14324380091876664890385623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9549586727917776593590415 14324380091876664890385623)
      ·
        refine ⟨21486570137814997335578435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14324380091876664890385623 21486570137814997335578435)
        ·
          refine ⟨32229855206722496003367653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21486570137814997335578435 32229855206722496003367653)
          ·
            refine ⟨6043097851260468000631435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32229855206722496003367653 6043097851260468000631435)
            ·
              refine ⟨9064646776890702000947153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043097851260468000631435 9064646776890702000947153)
              ·
                refine ⟨6798485082668026500710365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9064646776890702000947153 6798485082668026500710365)
                ·
                  refine ⟨2549431906000509937766387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6798485082668026500710365 2549431906000509937766387)
                  ·
                    refine ⟨3824147859000764906649581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549431906000509937766387 3824147859000764906649581)
                    ·
                      refine ⟨1434055447125286839993593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3824147859000764906649581 1434055447125286839993593)
                      ·
                        rfl

theorem cell23_2792813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_2792813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792813 prefixEnd_2792813 := by exact prefixLift 2792813
  have htrace : WordTrace (prefixWord ++ tailWord_2792813) baseStart_2792813 baseEnd_2792813 := by
    simpa [prefixWord, tailWord_2792813, baseEnd_2792813] using wordTrace_append hprefix tailTrace_2792813
  have hstable : (prefixWord ++ tailWord_2792813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792813).length < 2 ^ (prefixWord ++ tailWord_2792813).sum := by decide
  have hdescent : baseEnd_2792813 < baseStart_2792813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792829 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_2792829 : Nat := 118140960795 + 2792829 * 2 ^ 59
def prefixEnd_2792829 : Nat := 4983230072969 + 3 ^ 40 * 2792829 * 2
def baseEnd_2792829 : Nat := 478021220938586259131173

theorem tailTrace_2792829 : CollatzResearch.WordTrace tailWord_2792829 prefixEnd_2792829 478021220938586259131173 := by
  unfold tailWord_2792829
  simp only [CollatzResearch.WordTrace]
  refine ⟨101862841999064985064213541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67908561332709990042809027 101862841999064985064213541)
  ·
    refine ⟨19099282874824684699540039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101862841999064985064213541 19099282874824684699540039)
    ·
      refine ⟨28648924312237027049310059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19099282874824684699540039 28648924312237027049310059)
      ·
        refine ⟨42973386468355540573965089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28648924312237027049310059 42973386468355540573965089)
        ·
          refine ⟨32230039851266655430473817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42973386468355540573965089 32230039851266655430473817)
          ·
            refine ⟨24172529888449991572855363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32230039851266655430473817 24172529888449991572855363)
            ·
              refine ⟨36258794832674987359283045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24172529888449991572855363 36258794832674987359283045)
              ·
                refine ⟨6798524031126560129865571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36258794832674987359283045 6798524031126560129865571)
                ·
                  refine ⟨10197786046689840194798357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6798524031126560129865571 10197786046689840194798357)
                  ·
                    refine ⟨478021220938586259131173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10197786046689840194798357 478021220938586259131173)
                    ·
                      rfl

theorem cell23_2792829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_2792829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792829 prefixEnd_2792829 := by exact prefixLift 2792829
  have htrace : WordTrace (prefixWord ++ tailWord_2792829) baseStart_2792829 baseEnd_2792829 := by
    simpa [prefixWord, tailWord_2792829, baseEnd_2792829] using wordTrace_append hprefix tailTrace_2792829
  have hstable : (prefixWord ++ tailWord_2792829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792829).length < 2 ^ (prefixWord ++ tailWord_2792829).sum := by decide
  have hdescent : baseEnd_2792829 < baseStart_2792829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792833 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 1, 5]
def baseStart_2792833 : Nat := 118140960795 + 2792833 * 2 ^ 59
def prefixEnd_2792833 : Nat := 4983230072969 + 3 ^ 40 * 2792833 * 2
def baseEnd_2792833 : Nat := 478021905579458920581167

theorem tailTrace_2792833 : CollatzResearch.WordTrace tailWord_2792833 prefixEnd_2792833 478021905579458920581167 := by
  unfold tailWord_2792833
  simp only [CollatzResearch.WordTrace]
  refine ⟨101862987891050493747359153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67908658594033662498239435 101862987891050493747359153)
  ·
    refine ⟨76397240918287870310519365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101862987891050493747359153 76397240918287870310519365)
    ·
      refine ⟨14324482672178975683222381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76397240918287870310519365 14324482672178975683222381)
      ·
        refine ⟨5371681002067115881208393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14324482672178975683222381 5371681002067115881208393)
        ·
          refine ⟨4028760751550336910906295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5371681002067115881208393 4028760751550336910906295)
          ·
            refine ⟨6043141127325505366359443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028760751550336910906295 6043141127325505366359443)
            ·
              refine ⟨9064711690988258049539165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043141127325505366359443 9064711690988258049539165)
              ·
                refine ⟨3399266884120596768577187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9064711690988258049539165 3399266884120596768577187)
                ·
                  refine ⟨5098900326180895152865781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399266884120596768577187 5098900326180895152865781)
                  ·
                    refine ⟨478021905579458920581167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5098900326180895152865781 478021905579458920581167)
                    ·
                      rfl

theorem cell23_2792833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_2792833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792833 prefixEnd_2792833 := by exact prefixLift 2792833
  have htrace : WordTrace (prefixWord ++ tailWord_2792833) baseStart_2792833 baseEnd_2792833 := by
    simpa [prefixWord, tailWord_2792833, baseEnd_2792833] using wordTrace_append hprefix tailTrace_2792833
  have hstable : (prefixWord ++ tailWord_2792833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792833).length < 2 ^ (prefixWord ++ tailWord_2792833).sum := by decide
  have hdescent : baseEnd_2792833 < baseStart_2792833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792853 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_2792853 : Nat := 118140960795 + 2792853 * 2 ^ 59
def prefixEnd_2792853 : Nat := 4983230072969 + 3 ^ 40 * 2792853 * 2
def baseEnd_2792853 : Nat := 1434075986351466683493409

theorem tailTrace_2792853 : CollatzResearch.WordTrace tailWord_2792853 prefixEnd_2792853 1434075986351466683493409 := by
  unfold tailWord_2792853
  simp only [CollatzResearch.WordTrace]
  refine ⟨101863717350978037163087213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67909144900652024775391475 101863717350978037163087213)
  ·
    refine ⟨38198894006616763936157705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101863717350978037163087213 38198894006616763936157705)
    ·
      refine ⟨28649170504962572952118279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38198894006616763936157705 28649170504962572952118279)
      ·
        refine ⟨42973755757443859428177419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28649170504962572952118279 42973755757443859428177419)
        ·
          refine ⟨64460633636165789142266129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42973755757443859428177419 64460633636165789142266129)
          ·
            refine ⟨48345475227124341856699597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64460633636165789142266129 48345475227124341856699597)
            ·
              refine ⟨18129553210171628196262349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48345475227124341856699597 18129553210171628196262349)
              ·
                refine ⟨6798582453814360573598381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18129553210171628196262349 6798582453814360573598381)
                ·
                  refine ⟨2549468420180385215099393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6798582453814360573598381 2549468420180385215099393)
                  ·
                    refine ⟨1912101315135288911324545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2549468420180385215099393 1912101315135288911324545)
                    ·
                      refine ⟨1434075986351466683493409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912101315135288911324545 1434075986351466683493409)
                      ·
                        rfl

theorem cell23_2792853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_2792853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792853 prefixEnd_2792853 := by exact prefixLift 2792853
  have htrace : WordTrace (prefixWord ++ tailWord_2792853) baseStart_2792853 baseEnd_2792853 := by
    simpa [prefixWord, tailWord_2792853, baseEnd_2792853] using wordTrace_append hprefix tailTrace_2792853
  have hstable : (prefixWord ++ tailWord_2792853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792853).length < 2 ^ (prefixWord ++ tailWord_2792853).sum := by decide
  have hdescent : baseEnd_2792853 < baseStart_2792853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792866 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2792866 : Nat := 118140960795 + 2792866 * 2 ^ 59
def prefixEnd_2792866 : Nat := 4983230072969 + 3 ^ 40 * 2792866 * 2
def baseEnd_2792866 : Nat := 1434082661599975132630849

theorem tailTrace_2792866 : CollatzResearch.WordTrace tailWord_2792866 prefixEnd_2792866 1434082661599975132630849 := by
  unfold tailWord_2792866
  simp only [CollatzResearch.WordTrace]
  refine ⟨25466047874982735095827613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67909460999953960255540301 25466047874982735095827613)
  ·
    refine ⟨9549767953118525660935355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25466047874982735095827613 9549767953118525660935355)
    ·
      refine ⟨14324651929677788491403033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9549767953118525660935355 14324651929677788491403033)
      ·
        refine ⟨10743488947258341368552275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14324651929677788491403033 10743488947258341368552275)
        ·
          refine ⟨16115233420887512052828413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10743488947258341368552275 16115233420887512052828413)
          ·
            refine ⟨6043212532832817019810655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16115233420887512052828413 6043212532832817019810655)
            ·
              refine ⟨9064818799249225529715983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043212532832817019810655 9064818799249225529715983)
              ·
                refine ⟨13597228198873838294573975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9064818799249225529715983 13597228198873838294573975)
                ·
                  refine ⟨20395842298310757441860963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13597228198873838294573975 20395842298310757441860963)
                  ·
                    refine ⟨30593763447466136162791445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20395842298310757441860963 30593763447466136162791445)
                    ·
                      refine ⟨1434082661599975132630849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30593763447466136162791445 1434082661599975132630849)
                      ·
                        rfl

theorem cell23_2792866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2792866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792866 prefixEnd_2792866 := by exact prefixLift 2792866
  have htrace : WordTrace (prefixWord ++ tailWord_2792866) baseStart_2792866 baseEnd_2792866 := by
    simpa [prefixWord, tailWord_2792866, baseEnd_2792866] using wordTrace_append hprefix tailTrace_2792866
  have hstable : (prefixWord ++ tailWord_2792866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792866).length < 2 ^ (prefixWord ++ tailWord_2792866).sum := by decide
  have hdescent : baseEnd_2792866 < baseStart_2792866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792898 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2792898 : Nat := 118140960795 + 2792898 * 2 ^ 59
def prefixEnd_2792898 : Nat := 4983230072969 + 3 ^ 40 * 2792898 * 2
def baseEnd_2792898 : Nat := 1434099092980919007430703

theorem tailTrace_2792898 : CollatzResearch.WordTrace tailWord_2792898 prefixEnd_2792898 1434099092980919007430703 := by
  unfold tailWord_2792898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25466339658953752462118837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67910239090543339898983565 25466339658953752462118837)
  ·
    refine ⟨2387469343026914293323641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25466339658953752462118837 2387469343026914293323641)
    ·
      refine ⟨1790602007270185719992731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2387469343026914293323641 1790602007270185719992731)
      ·
        refine ⟨2685903010905278579989097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790602007270185719992731 2685903010905278579989097)
        ·
          refine ⟨2014427258178958934991823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685903010905278579989097 2014427258178958934991823)
          ·
            refine ⟨3021640887268438402487735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014427258178958934991823 3021640887268438402487735)
            ·
              refine ⟨4532461330902657603731603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021640887268438402487735 4532461330902657603731603)
              ·
                refine ⟨6798691996353986405597405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532461330902657603731603 6798691996353986405597405)
                ·
                  refine ⟨2549509498632744902099027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6798691996353986405597405 2549509498632744902099027)
                  ·
                    refine ⟨3824264247949117353148541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549509498632744902099027 3824264247949117353148541)
                    ·
                      refine ⟨1434099092980919007430703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3824264247949117353148541 1434099092980919007430703)
                      ·
                        rfl

theorem cell23_2792898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2792898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792898 prefixEnd_2792898 := by exact prefixLift 2792898
  have htrace : WordTrace (prefixWord ++ tailWord_2792898) baseStart_2792898 baseEnd_2792898 := by
    simpa [prefixWord, tailWord_2792898, baseEnd_2792898] using wordTrace_append hprefix tailTrace_2792898
  have hstable : (prefixWord ++ tailWord_2792898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792898).length < 2 ^ (prefixWord ++ tailWord_2792898).sum := by decide
  have hdescent : baseEnd_2792898 < baseStart_2792898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792903 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_2792903 : Nat := 118140960795 + 2792903 * 2 ^ 59
def prefixEnd_2792903 : Nat := 4983230072969 + 3 ^ 40 * 2792903 * 2
def baseEnd_2792903 : Nat := 1434101660384191487868179

theorem tailTrace_2792903 : CollatzResearch.WordTrace tailWord_2792903 prefixEnd_2792903 1434101660384191487868179 := by
  unfold tailWord_2792903
  simp only [CollatzResearch.WordTrace]
  refine ⟨101865541000796895702407363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67910360667197930468271575 101865541000796895702407363)
  ·
    refine ⟨152798311501195343553611045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101865541000796895702407363 152798311501195343553611045)
    ·
      refine ⟨28649683406474126916302071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152798311501195343553611045 28649683406474126916302071)
      ·
        refine ⟨42974525109711190374453107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28649683406474126916302071 42974525109711190374453107)
        ·
          refine ⟨64461787664566785561679661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42974525109711190374453107 64461787664566785561679661)
          ·
            refine ⟨24173170374212544585629873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64461787664566785561679661 24173170374212544585629873)
            ·
              refine ⟨18129877780659408439222405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24173170374212544585629873 18129877780659408439222405)
              ·
                refine ⟨3399352083873639082354201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18129877780659408439222405 3399352083873639082354201)
                ·
                  refine ⟨2549514062905229311765651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3399352083873639082354201 2549514062905229311765651)
                  ·
                    refine ⟨3824271094357843967648477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549514062905229311765651 3824271094357843967648477)
                    ·
                      refine ⟨1434101660384191487868179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3824271094357843967648477 1434101660384191487868179)
                      ·
                        rfl

theorem cell23_2792903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_2792903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792903 prefixEnd_2792903 := by exact prefixLift 2792903
  have htrace : WordTrace (prefixWord ++ tailWord_2792903) baseStart_2792903 baseEnd_2792903 := by
    simpa [prefixWord, tailWord_2792903, baseEnd_2792903] using wordTrace_append hprefix tailTrace_2792903
  have hstable : (prefixWord ++ tailWord_2792903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792903).length < 2 ^ (prefixWord ++ tailWord_2792903).sum := by decide
  have hdescent : baseEnd_2792903 < baseStart_2792903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792919 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 2, 6]
def baseStart_2792919 : Nat := 118140960795 + 2792919 * 2 ^ 59
def prefixEnd_2792919 : Nat := 4983230072969 + 3 ^ 40 * 2792919 * 2
def baseEnd_2792919 : Nat := 478036625358221141756035

theorem tailTrace_2792919 : CollatzResearch.WordTrace tailWord_2792919 prefixEnd_2792919 478036625358221141756035 := by
  unfold tailWord_2792919
  simp only [CollatzResearch.WordTrace]
  refine ⟨101866124568738930434989811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67910749712492620289993207 101866124568738930434989811)
  ·
    refine ⟨152799186853108395652484717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101866124568738930434989811 152799186853108395652484717)
    ·
      refine ⟨57299695069915648369681769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152799186853108395652484717 57299695069915648369681769)
      ·
        refine ⟨42974771302436736277261327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57299695069915648369681769 42974771302436736277261327)
        ·
          refine ⟨64462156953655104415891991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42974771302436736277261327 64462156953655104415891991)
          ·
            refine ⟨96693235430482656623837987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64462156953655104415891991 96693235430482656623837987)
            ·
              refine ⟨145039853145723984935756981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96693235430482656623837987 145039853145723984935756981)
              ·
                refine ⟨13597486232411623587727217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145039853145723984935756981 13597486232411623587727217)
                ·
                  refine ⟨10198114674308717690795413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13597486232411623587727217 10198114674308717690795413)
                  ·
                    refine ⟨478036625358221141756035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10198114674308717690795413 478036625358221141756035)
                    ·
                      rfl

theorem cell23_2792919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_2792919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792919 prefixEnd_2792919 := by exact prefixLift 2792919
  have htrace : WordTrace (prefixWord ++ tailWord_2792919) baseStart_2792919 baseEnd_2792919 := by
    simpa [prefixWord, tailWord_2792919, baseEnd_2792919] using wordTrace_append hprefix tailTrace_2792919
  have hstable : (prefixWord ++ tailWord_2792919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792919).length < 2 ^ (prefixWord ++ tailWord_2792919).sum := by decide
  have hdescent : baseEnd_2792919 < baseStart_2792919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792920 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 2, 1, 3]
def baseStart_2792920 : Nat := 118140960795 + 2792920 * 2 ^ 59
def prefixEnd_2792920 : Nat := 4983230072969 + 3 ^ 40 * 2792920 * 2
def baseEnd_2792920 : Nat := 1434110389555317921355601

theorem tailTrace_2792920 : CollatzResearch.WordTrace tailWord_2792920 prefixEnd_2792920 1434110389555317921355601 := by
  unfold tailWord_2792920
  simp only [CollatzResearch.WordTrace]
  refine ⟨50933080520867653802888107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67910774027823538403850809 50933080520867653802888107)
  ·
    refine ⟨76399620781301480704332161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50933080520867653802888107 76399620781301480704332161)
    ·
      refine ⟨57299715585976110528249121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76399620781301480704332161 57299715585976110528249121)
      ·
        refine ⟨42974786689482082896186841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57299715585976110528249121 42974786689482082896186841)
        ·
          refine ⟨32231090017111562172140131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42974786689482082896186841 32231090017111562172140131)
          ·
            refine ⟨48346635025667343258210197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32231090017111562172140131 48346635025667343258210197)
            ·
              refine ⟨2266248516828156715228603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48346635025667343258210197 2266248516828156715228603)
              ·
                refine ⟨3399372775242235072842905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266248516828156715228603 3399372775242235072842905)
                ·
                  refine ⟨2549529581431676304632179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3399372775242235072842905 2549529581431676304632179)
                  ·
                    refine ⟨3824294372147514456948269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549529581431676304632179 3824294372147514456948269)
                    ·
                      refine ⟨1434110389555317921355601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3824294372147514456948269 1434110389555317921355601)
                      ·
                        rfl

theorem cell23_2792920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_2792920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792920 prefixEnd_2792920 := by exact prefixLift 2792920
  have htrace : WordTrace (prefixWord ++ tailWord_2792920) baseStart_2792920 baseEnd_2792920 := by
    simpa [prefixWord, tailWord_2792920, baseEnd_2792920] using wordTrace_append hprefix tailTrace_2792920
  have hstable : (prefixWord ++ tailWord_2792920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792920).length < 2 ^ (prefixWord ++ tailWord_2792920).sum := by decide
  have hdescent : baseEnd_2792920 < baseStart_2792920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792939 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 4]
def baseStart_2792939 : Nat := 118140960795 + 2792939 * 2 ^ 59
def prefixEnd_2792939 : Nat := 4983230072969 + 3 ^ 40 * 2792939 * 2
def baseEnd_2792939 : Nat := 1434120145687753347018013

theorem tailTrace_2792939 : CollatzResearch.WordTrace tailWord_2792939 prefixEnd_2792939 1434120145687753347018013 := by
  unfold tailWord_2792939
  simp only [CollatzResearch.WordTrace]
  refine ⟨101866854028666473850717871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67911236019110982567145247 101866854028666473850717871)
  ·
    refine ⟨152800281042999710776076807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101866854028666473850717871 152800281042999710776076807)
    ·
      refine ⟨229200421564499566164115211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152800281042999710776076807 229200421564499566164115211)
      ·
        refine ⟨343800632346749349246172817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229200421564499566164115211 343800632346749349246172817)
        ·
          refine ⟨257850474260062011934629613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343800632346749349246172817 257850474260062011934629613)
          ·
            refine ⟨96693927847523254475486105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257850474260062011934629613 96693927847523254475486105)
            ·
              refine ⟨72520445885642440856614579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96693927847523254475486105 72520445885642440856614579)
              ·
                refine ⟨108780668828463661284921869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72520445885642440856614579 108780668828463661284921869)
                ·
                  refine ⟨40792750810673872981845701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108780668828463661284921869 40792750810673872981845701)
                  ·
                    refine ⟨7648640777001351184096069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40792750810673872981845701 7648640777001351184096069)
                    ·
                      refine ⟨1434120145687753347018013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7648640777001351184096069 1434120145687753347018013)
                      ·
                        rfl

theorem cell23_2792939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 4].length) (baseStart_2792939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792939 prefixEnd_2792939 := by exact prefixLift 2792939
  have htrace : WordTrace (prefixWord ++ tailWord_2792939) baseStart_2792939 baseEnd_2792939 := by
    simpa [prefixWord, tailWord_2792939, baseEnd_2792939] using wordTrace_append hprefix tailTrace_2792939
  have hstable : (prefixWord ++ tailWord_2792939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792939).length < 2 ^ (prefixWord ++ tailWord_2792939).sum := by decide
  have hdescent : baseEnd_2792939 < baseStart_2792939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792943 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 6, 2, 2]
def baseStart_2792943 : Nat := 118140960795 + 2792943 * 2 ^ 59
def prefixEnd_2792943 : Nat := 4983230072969 + 3 ^ 40 * 2792943 * 2
def baseEnd_2792943 : Nat := 1434122199610371331367995

theorem tailTrace_2792943 : CollatzResearch.WordTrace tailWord_2792943 prefixEnd_2792943 1434122199610371331367995 := by
  unfold tailWord_2792943
  simp only [CollatzResearch.WordTrace]
  refine ⟨101866999920651982533863483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67911333280434655022575655 101866999920651982533863483)
  ·
    refine ⟨152800499880977973800795225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101866999920651982533863483 152800499880977973800795225)
    ·
      refine ⟨114600374910733480350596419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152800499880977973800795225 114600374910733480350596419)
      ·
        refine ⟨171900562366100220525894629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114600374910733480350596419 171900562366100220525894629)
        ·
          refine ⟨32231355443643791348605243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171900562366100220525894629 32231355443643791348605243)
          ·
            refine ⟨48347033165465687022907865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32231355443643791348605243 48347033165465687022907865)
            ·
              refine ⟨36260274874099265267180899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48347033165465687022907865 36260274874099265267180899)
              ·
                refine ⟨54390412311148897900771349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36260274874099265267180899 54390412311148897900771349)
                ·
                  refine ⟨2549550577085104589098657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54390412311148897900771349 2549550577085104589098657)
                  ·
                    refine ⟨1912162932813828441823993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2549550577085104589098657 1912162932813828441823993)
                    ·
                      refine ⟨1434122199610371331367995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912162932813828441823993 1434122199610371331367995)
                      ·
                        rfl

theorem cell23_2792943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 2, 2].length) (baseStart_2792943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2792943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2792943 prefixEnd_2792943 := by exact prefixLift 2792943
  have htrace : WordTrace (prefixWord ++ tailWord_2792943) baseStart_2792943 baseEnd_2792943 := by
    simpa [prefixWord, tailWord_2792943, baseEnd_2792943] using wordTrace_append hprefix tailTrace_2792943
  have hstable : (prefixWord ++ tailWord_2792943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792943).length < 2 ^ (prefixWord ++ tailWord_2792943).sum := by decide
  have hdescent : baseEnd_2792943 < baseStart_2792943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793019 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 11]
def baseStart_2793019 : Nat := 118140960795 + 2793019 * 2 ^ 59
def prefixEnd_2793019 : Nat := 4983230072969 + 3 ^ 40 * 2793019 * 2
def baseEnd_2793019 : Nat := 1434161224140113034017645

theorem tailTrace_2793019 : CollatzResearch.WordTrace tailWord_2793019 prefixEnd_2793019 1434161224140113034017645 := by
  unfold tailWord_2793019
  simp only [CollatzResearch.WordTrace]
  refine ⟨101869771868376647513630111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67913181245584431675753407 101869771868376647513630111)
  ·
    refine ⟨152804657802564971270445167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101869771868376647513630111 152804657802564971270445167)
    ·
      refine ⟨229206986703847456905667751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152804657802564971270445167 229206986703847456905667751)
      ·
        refine ⟨343810480055771185358501627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229206986703847456905667751 343810480055771185358501627)
        ·
          refine ⟨515715720083656778037752441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343810480055771185358501627 515715720083656778037752441)
          ·
            refine ⟨386786790062742583528314331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515715720083656778037752441 386786790062742583528314331)
            ·
              refine ⟨580180185094113875292471497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386786790062742583528314331 580180185094113875292471497)
              ·
                refine ⟨435135138820585406469353623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580180185094113875292471497 435135138820585406469353623)
                ·
                  refine ⟨652702708230878109704030435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435135138820585406469353623 652702708230878109704030435)
                  ·
                    refine ⟨979054062346317164556045653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 652702708230878109704030435 979054062346317164556045653)
                    ·
                      refine ⟨1434161224140113034017645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 979054062346317164556045653 1434161224140113034017645)
                      ·
                        rfl

theorem cell23_2793019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_2793019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793019 prefixEnd_2793019 := by exact prefixLift 2793019
  have htrace : WordTrace (prefixWord ++ tailWord_2793019) baseStart_2793019 baseEnd_2793019 := by
    simpa [prefixWord, tailWord_2793019, baseEnd_2793019] using wordTrace_append hprefix tailTrace_2793019
  have hstable : (prefixWord ++ tailWord_2793019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793019).length < 2 ^ (prefixWord ++ tailWord_2793019).sum := by decide
  have hdescent : baseEnd_2793019 < baseStart_2793019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793077 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2793077 : Nat := 118140960795 + 2793077 * 2 ^ 59
def prefixEnd_2793077 : Nat := 4983230072969 + 3 ^ 40 * 2793077 * 2
def baseEnd_2793077 : Nat := 478063668672691269030793

theorem tailTrace_2793077 : CollatzResearch.WordTrace tailWord_2793077 prefixEnd_2793077 478063668672691269030793 := by
  unfold tailWord_2793077
  simp only [CollatzResearch.WordTrace]
  refine ⟨101871887302166523419241485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67914591534777682279494323 101871887302166523419241485)
  ·
    refine ⟨38201957738312446282215557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101871887302166523419241485 38201957738312446282215557)
    ·
      refine ⟨7162867075933583677915417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38201957738312446282215557 7162867075933583677915417)
      ·
        refine ⟨5372150306950187758436563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7162867075933583677915417 5372150306950187758436563)
        ·
          refine ⟨8058225460425281637654845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5372150306950187758436563 8058225460425281637654845)
          ·
            refine ⟨3021834547659480614120567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8058225460425281637654845 3021834547659480614120567)
            ·
              refine ⟨4532751821489220921180851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021834547659480614120567 4532751821489220921180851)
              ·
                refine ⟨6799127732233831381771277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532751821489220921180851 6799127732233831381771277)
                ·
                  refine ⟨2549672899587686768164229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6799127732233831381771277 2549672899587686768164229)
                  ·
                    refine ⟨478063668672691269030793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2549672899587686768164229 478063668672691269030793)
                    ·
                      rfl

theorem cell23_2793077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2793077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793077 prefixEnd_2793077 := by exact prefixLift 2793077
  have htrace : WordTrace (prefixWord ++ tailWord_2793077) baseStart_2793077 baseEnd_2793077 := by
    simpa [prefixWord, tailWord_2793077, baseEnd_2793077] using wordTrace_append hprefix tailTrace_2793077
  have hstable : (prefixWord ++ tailWord_2793077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793077).length < 2 ^ (prefixWord ++ tailWord_2793077).sum := by decide
  have hdescent : baseEnd_2793077 < baseStart_2793077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793117 : List Nat := [1, 4, 2, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_2793117 : Nat := 118140960795 + 2793117 * 2 ^ 59
def prefixEnd_2793117 : Nat := 4983230072969 + 3 ^ 40 * 2793117 * 2
def baseEnd_2793117 : Nat := 1434211545244253650592195

theorem tailTrace_2793117 : CollatzResearch.WordTrace tailWord_2793117 prefixEnd_2793117 1434211545244253650592195 := by
  unfold tailWord_2793117
  simp only [CollatzResearch.WordTrace]
  refine ⟨101873346222021610250697605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67915564148014406833798403 101873346222021610250697605)
  ·
    refine ⟨19101252416629051922005801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101873346222021610250697605 19101252416629051922005801)
    ·
      refine ⟨14325939312471788941504351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19101252416629051922005801 14325939312471788941504351)
      ·
        refine ⟨21488908968707683412256527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14325939312471788941504351 21488908968707683412256527)
        ·
          refine ⟨32233363453061525118384791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21488908968707683412256527 32233363453061525118384791)
          ·
            refine ⟨48350045179592287677577187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32233363453061525118384791 48350045179592287677577187)
            ·
              refine ⟨72525067769388431516365781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48350045179592287677577187 72525067769388431516365781)
              ·
                refine ⟨1699806275845041363664823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72525067769388431516365781 1699806275845041363664823)
                ·
                  refine ⟨2549709413767562045497235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699806275845041363664823 2549709413767562045497235)
                  ·
                    refine ⟨3824564120651343068245853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549709413767562045497235 3824564120651343068245853)
                    ·
                      refine ⟨1434211545244253650592195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3824564120651343068245853 1434211545244253650592195)
                      ·
                        rfl

theorem cell23_2793117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_2793117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793117 prefixEnd_2793117 := by exact prefixLift 2793117
  have htrace : WordTrace (prefixWord ++ tailWord_2793117) baseStart_2793117 baseEnd_2793117 := by
    simpa [prefixWord, tailWord_2793117, baseEnd_2793117] using wordTrace_append hprefix tailTrace_2793117
  have hstable : (prefixWord ++ tailWord_2793117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793117).length < 2 ^ (prefixWord ++ tailWord_2793117).sum := by decide
  have hdescent : baseEnd_2793117 < baseStart_2793117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793133 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2793133 : Nat := 118140960795 + 2793133 * 2 ^ 59
def prefixEnd_2793133 : Nat := 4983230072969 + 3 ^ 40 * 2793133 * 2
def baseEnd_2793133 : Nat := 478073253644908529330707

theorem tailTrace_2793133 : CollatzResearch.WordTrace tailWord_2793133 prefixEnd_2793133 478073253644908529330707 := by
  unfold tailWord_2793133
  simp only [CollatzResearch.WordTrace]
  refine ⟨101873929789963644983280053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67915953193309096655520035 101873929789963644983280053)
  ·
    refine ⟨9550680917809091717182505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101873929789963644983280053 9550680917809091717182505)
    ·
      refine ⟨7163010688356818787886879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9550680917809091717182505 7163010688356818787886879)
      ·
        refine ⟨10744516032535228181830319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7163010688356818787886879 10744516032535228181830319)
        ·
          refine ⟨16116774048802842272745479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10744516032535228181830319 16116774048802842272745479)
          ·
            refine ⟨24175161073204263409118219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16116774048802842272745479 24175161073204263409118219)
            ·
              refine ⟨36262741609806395113677329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24175161073204263409118219 36262741609806395113677329)
              ·
                refine ⟨27197056207354796335257997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36262741609806395113677329 27197056207354796335257997)
                ·
                  refine ⟨10198896077758048625721749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27197056207354796335257997 10198896077758048625721749)
                  ·
                    refine ⟨478073253644908529330707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10198896077758048625721749 478073253644908529330707)
                    ·
                      rfl

theorem cell23_2793133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2793133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793133 prefixEnd_2793133 := by exact prefixLift 2793133
  have htrace : WordTrace (prefixWord ++ tailWord_2793133) baseStart_2793133 baseEnd_2793133 := by
    simpa [prefixWord, tailWord_2793133, baseEnd_2793133] using wordTrace_append hprefix tailTrace_2793133
  have hstable : (prefixWord ++ tailWord_2793133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793133).length < 2 ^ (prefixWord ++ tailWord_2793133).sum := by decide
  have hdescent : baseEnd_2793133 < baseStart_2793133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793136 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_2793136 : Nat := 118140960795 + 2793136 * 2 ^ 59
def prefixEnd_2793136 : Nat := 4983230072969 + 3 ^ 40 * 2793136 * 2
def baseEnd_2793136 : Nat := 1434221301376689076254607

theorem tailTrace_2793136 : CollatzResearch.WordTrace tailWord_2793136 prefixEnd_2793136 1434221301376689076254607 := by
  unfold tailWord_2793136
  simp only [CollatzResearch.WordTrace]
  refine ⟨50937019604476388247819631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67916026139301850997092841 50937019604476388247819631)
  ·
    refine ⟨76405529406714582371729447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50937019604476388247819631 76405529406714582371729447)
    ·
      refine ⟨114608294110071873557594171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76405529406714582371729447 114608294110071873557594171)
      ·
        refine ⟨171912441165107810336391257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114608294110071873557594171 171912441165107810336391257)
        ·
          refine ⟨128934330873830857752293443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171912441165107810336391257 128934330873830857752293443)
          ·
            refine ⟨193401496310746286628440165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128934330873830857752293443 193401496310746286628440165)
            ·
              refine ⟨36262780558264928742832531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193401496310746286628440165 36262780558264928742832531)
              ·
                refine ⟨54394170837397393114248797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36262780558264928742832531 54394170837397393114248797)
                ·
                  refine ⟨20397814064024022417843299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54394170837397393114248797 20397814064024022417843299)
                  ·
                    refine ⟨30596721096036033626764949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20397814064024022417843299 30596721096036033626764949)
                    ·
                      refine ⟨1434221301376689076254607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30596721096036033626764949 1434221301376689076254607)
                      ·
                        rfl

theorem cell23_2793136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_2793136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793136 prefixEnd_2793136 := by exact prefixLift 2793136
  have htrace : WordTrace (prefixWord ++ tailWord_2793136) baseStart_2793136 baseEnd_2793136 := by
    simpa [prefixWord, tailWord_2793136, baseEnd_2793136] using wordTrace_append hprefix tailTrace_2793136
  have hstable : (prefixWord ++ tailWord_2793136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793136).length < 2 ^ (prefixWord ++ tailWord_2793136).sum := by decide
  have hdescent : baseEnd_2793136 < baseStart_2793136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793150 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2793150 : Nat := 118140960795 + 2793150 * 2 ^ 59
def prefixEnd_2793150 : Nat := 4983230072969 + 3 ^ 40 * 2793150 * 2
def baseEnd_2793150 : Nat := 478076163368617340493181

theorem tailTrace_2793150 : CollatzResearch.WordTrace tailWord_2793150 prefixEnd_2793150 478076163368617340493181 := by
  unfold tailWord_2793150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12734318728862757110831113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67916366553934704591099269 12734318728862757110831113)
  ·
    refine ⟨9550739046647067833123335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12734318728862757110831113 9550739046647067833123335)
    ·
      refine ⟨14326108569970601749685003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9550739046647067833123335 14326108569970601749685003)
      ·
        refine ⟨21489162854955902624527505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14326108569970601749685003 21489162854955902624527505)
        ·
          refine ⟨16116872141216926968395629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21489162854955902624527505 16116872141216926968395629)
          ·
            refine ⟨6043827052956347613148361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16116872141216926968395629 6043827052956347613148361)
            ·
              refine ⟨4532870289717260709861271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6043827052956347613148361 4532870289717260709861271)
              ·
                refine ⟨6799305434575891064791907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532870289717260709861271 6799305434575891064791907)
                ·
                  refine ⟨10198958151863836597187861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6799305434575891064791907 10198958151863836597187861)
                  ·
                    refine ⟨478076163368617340493181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10198958151863836597187861 478076163368617340493181)
                    ·
                      rfl

theorem cell23_2793150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2793150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793150 prefixEnd_2793150 := by exact prefixLift 2793150
  have htrace : WordTrace (prefixWord ++ tailWord_2793150) baseStart_2793150 baseEnd_2793150 := by
    simpa [prefixWord, tailWord_2793150, baseEnd_2793150] using wordTrace_append hprefix tailTrace_2793150
  have hstable : (prefixWord ++ tailWord_2793150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793150).length < 2 ^ (prefixWord ++ tailWord_2793150).sum := by decide
  have hdescent : baseEnd_2793150 < baseStart_2793150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793160 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_2793160 : Nat := 118140960795 + 2793160 * 2 ^ 59
def prefixEnd_2793160 : Nat := 4983230072969 + 3 ^ 40 * 2793160 * 2
def baseEnd_2793160 : Nat := 1434233624912396982354497

theorem tailTrace_2793160 : CollatzResearch.WordTrace tailWord_2793160 prefixEnd_2793160 1434233624912396982354497 := by
  unfold tailWord_2793160
  simp only [CollatzResearch.WordTrace]
  refine ⟨50937457280432914297256467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67916609707243885729675289 50937457280432914297256467)
  ·
    refine ⟨76406185920649371445884701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50937457280432914297256467 76406185920649371445884701)
    ·
      refine ⟨28652319720243514292206763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76406185920649371445884701 28652319720243514292206763)
      ·
        refine ⟨42978479580365271438310145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28652319720243514292206763 42978479580365271438310145)
        ·
          refine ⟨32233859685273953578732609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42978479580365271438310145 32233859685273953578732609)
          ·
            refine ⟨24175394763955465184049457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32233859685273953578732609 24175394763955465184049457)
            ·
              refine ⟨18131546072966598888037093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24175394763955465184049457 18131546072966598888037093)
              ·
                refine ⟨3399664888681237291506955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18131546072966598888037093 3399664888681237291506955)
                ·
                  refine ⟨5099497333021855937260433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399664888681237291506955 5099497333021855937260433)
                  ·
                    refine ⟨3824622999766391952945325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5099497333021855937260433 3824622999766391952945325)
                    ·
                      refine ⟨1434233624912396982354497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3824622999766391952945325 1434233624912396982354497)
                      ·
                        rfl

theorem cell23_2793160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_2793160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793160 prefixEnd_2793160 := by exact prefixLift 2793160
  have htrace : WordTrace (prefixWord ++ tailWord_2793160) baseStart_2793160 baseEnd_2793160 := by
    simpa [prefixWord, tailWord_2793160, baseEnd_2793160] using wordTrace_append hprefix tailTrace_2793160
  have hstable : (prefixWord ++ tailWord_2793160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793160).length < 2 ^ (prefixWord ++ tailWord_2793160).sum := by decide
  have hdescent : baseEnd_2793160 < baseStart_2793160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793170 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2793170 : Nat := 118140960795 + 2793170 * 2 ^ 59
def prefixEnd_2793170 : Nat := 4983230072969 + 3 ^ 40 * 2793170 * 2
def baseEnd_2793170 : Nat := 1434238759718941943229451

theorem tailTrace_2793170 : CollatzResearch.WordTrace tailWord_2793170 prefixEnd_2793170 1434238759718941943229451 := by
  unfold tailWord_2793170
  simp only [CollatzResearch.WordTrace]
  refine ⟨25468819822707400075594241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67916852860553066868251309 25468819822707400075594241)
  ·
    refine ⟨19101614867030550056695681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25468819822707400075594241 19101614867030550056695681)
    ·
      refine ⟨14326211150272912542521761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19101614867030550056695681 14326211150272912542521761)
      ·
        refine ⟨10744658362704684406891321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14326211150272912542521761 10744658362704684406891321)
        ·
          refine ⟨8058493772028513305168491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10744658362704684406891321 8058493772028513305168491)
          ·
            refine ⟨12087740658042769957752737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8058493772028513305168491 12087740658042769957752737)
            ·
              refine ⟨9065805493532077468314553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12087740658042769957752737 9065805493532077468314553)
              ·
                refine ⟨6799354120149058101235915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9065805493532077468314553 6799354120149058101235915)
                ·
                  refine ⟨10199031180223587151853873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6799354120149058101235915 10199031180223587151853873)
                  ·
                    refine ⟨7649273385167690363890405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10199031180223587151853873 7649273385167690363890405)
                    ·
                      refine ⟨1434238759718941943229451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7649273385167690363890405 1434238759718941943229451)
                      ·
                        rfl

theorem cell23_2793170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2793170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793170 prefixEnd_2793170 := by exact prefixLift 2793170
  have htrace : WordTrace (prefixWord ++ tailWord_2793170) baseStart_2793170 baseEnd_2793170 := by
    simpa [prefixWord, tailWord_2793170, baseEnd_2793170] using wordTrace_append hprefix tailTrace_2793170
  have hstable : (prefixWord ++ tailWord_2793170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793170).length < 2 ^ (prefixWord ++ tailWord_2793170).sum := by decide
  have hdescent : baseEnd_2793170 < baseStart_2793170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793177 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 1, 2, 3]
def baseStart_2793177 : Nat := 118140960795 + 2793177 * 2 ^ 59
def prefixEnd_2793177 : Nat := 4983230072969 + 3 ^ 40 * 2793177 * 2
def baseEnd_2793177 : Nat := 1434242354083523415841919

theorem tailTrace_2793177 : CollatzResearch.WordTrace tailWord_2793177 prefixEnd_2793177 1434242354083523415841919 := by
  unfold tailWord_2793177
  simp only [CollatzResearch.WordTrace]
  refine ⟨101875534601804240497881785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67917023067869493665254523 101875534601804240497881785)
  ·
    refine ⟨76406650951353180373411339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101875534601804240497881785 76406650951353180373411339)
    ·
      refine ⟨114609976427029770560117009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76406650951353180373411339 114609976427029770560117009)
      ·
        refine ⟨85957482320272327920087757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114609976427029770560117009 85957482320272327920087757)
        ·
          refine ⟨32234055870102122970032909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85957482320272327920087757 32234055870102122970032909)
          ·
            refine ⟨12087770951288296113762341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32234055870102122970032909 12087770951288296113762341)
            ·
              refine ⟨2266457053366555521330439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12087770951288296113762341 2266457053366555521330439)
              ·
                refine ⟨3399685580049833281995659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266457053366555521330439 3399685580049833281995659)
                ·
                  refine ⟨5099528370074749922993489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399685580049833281995659 5099528370074749922993489)
                  ·
                    refine ⟨3824646277556062442245117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5099528370074749922993489 3824646277556062442245117)
                    ·
                      refine ⟨1434242354083523415841919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3824646277556062442245117 1434242354083523415841919)
                      ·
                        rfl

theorem cell23_2793177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_2793177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793177 prefixEnd_2793177 := by exact prefixLift 2793177
  have htrace : WordTrace (prefixWord ++ tailWord_2793177) baseStart_2793177 baseEnd_2793177 := by
    simpa [prefixWord, tailWord_2793177, baseEnd_2793177] using wordTrace_append hprefix tailTrace_2793177
  have hstable : (prefixWord ++ tailWord_2793177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793177).length < 2 ^ (prefixWord ++ tailWord_2793177).sum := by decide
  have hdescent : baseEnd_2793177 < baseStart_2793177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793180 : List Nat := [2, 2, 5, 1, 2, 1, 10]
def baseStart_2793180 : Nat := 118140960795 + 2793180 * 2 ^ 59
def prefixEnd_2793180 : Nat := 4983230072969 + 3 ^ 40 * 2793180 * 2
def baseEnd_2793180 : Nat := 17706714747228233384005

theorem tailTrace_2793180 : CollatzResearch.WordTrace tailWord_2793180 prefixEnd_2793180 17706714747228233384005 := by
  unfold tailWord_2793180
  simp only [CollatzResearch.WordTrace]
  refine ⟨50937822010396686005120497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67917096013862248006827329 50937822010396686005120497)
  ·
    refine ⟨38203366507797514503840373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50937822010396686005120497 38203366507797514503840373)
    ·
      refine ⟨3581565610106016984735035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38203366507797514503840373 3581565610106016984735035)
      ·
        refine ⟨5372348415159025477102553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3581565610106016984735035 5372348415159025477102553)
        ·
          refine ⟨4029261311369269107826915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5372348415159025477102553 4029261311369269107826915)
          ·
            refine ⟨6043891967053903661740373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029261311369269107826915 6043891967053903661740373)
            ·
              refine ⟨17706714747228233384005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6043891967053903661740373 17706714747228233384005)
              ·
                rfl

theorem cell23_2793180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 10].length) (baseStart_2793180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793180 prefixEnd_2793180 := by exact prefixLift 2793180
  have htrace : WordTrace (prefixWord ++ tailWord_2793180) baseStart_2793180 baseEnd_2793180 := by
    simpa [prefixWord, tailWord_2793180, baseEnd_2793180] using wordTrace_append hprefix tailTrace_2793180
  have hstable : (prefixWord ++ tailWord_2793180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793180).length < 2 ^ (prefixWord ++ tailWord_2793180).sum := by decide
  have hdescent : baseEnd_2793180 < baseStart_2793180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793191 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2793191 : Nat := 118140960795 + 2793191 * 2 ^ 59
def prefixEnd_2793191 : Nat := 4983230072969 + 3 ^ 40 * 2793191 * 2
def baseEnd_2793191 : Nat := 1434249542812686361066855

theorem tailTrace_2793191 : CollatzResearch.WordTrace tailWord_2793191 prefixEnd_2793191 1434249542812686361066855 := by
  unfold tailWord_2793191
  simp only [CollatzResearch.WordTrace]
  refine ⟨101876045223753520888891427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67917363482502347259260951 101876045223753520888891427)
  ·
    refine ⟨152814067835630281333337141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101876045223753520888891427 152814067835630281333337141)
    ·
      refine ⟨14326318859590338875000357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152814067835630281333337141 14326318859590338875000357)
      ·
        refine ⟨2686184786173188539062567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14326318859590338875000357 2686184786173188539062567)
        ·
          refine ⟨4029277179259782808593851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686184786173188539062567 4029277179259782808593851)
          ·
            refine ⟨6043915768889674212890777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029277179259782808593851 6043915768889674212890777)
            ·
              refine ⟨4532936826667255659668083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6043915768889674212890777 4532936826667255659668083)
              ·
                refine ⟨6799405240000883489502125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532936826667255659668083 6799405240000883489502125)
                ·
                  refine ⟨2549776965000331308563297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6799405240000883489502125 2549776965000331308563297)
                  ·
                    refine ⟨1912332723750248481422473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2549776965000331308563297 1912332723750248481422473)
                    ·
                      refine ⟨1434249542812686361066855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912332723750248481422473 1434249542812686361066855)
                      ·
                        rfl

theorem cell23_2793191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2793191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793191 prefixEnd_2793191 := by exact prefixLift 2793191
  have htrace : WordTrace (prefixWord ++ tailWord_2793191) baseStart_2793191 baseEnd_2793191 := by
    simpa [prefixWord, tailWord_2793191, baseEnd_2793191] using wordTrace_append hprefix tailTrace_2793191
  have hstable : (prefixWord ++ tailWord_2793191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793191).length < 2 ^ (prefixWord ++ tailWord_2793191).sum := by decide
  have hdescent : baseEnd_2793191 < baseStart_2793191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793200 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 3, 3, 2]
def baseStart_2793200 : Nat := 118140960795 + 2793200 * 2 ^ 59
def prefixEnd_2793200 : Nat := 4983230072969 + 3 ^ 40 * 2793200 * 2
def baseEnd_2793200 : Nat := 1434254164138576825854313

theorem tailTrace_2793200 : CollatzResearch.WordTrace tailWord_2793200 prefixEnd_2793200 1434254164138576825854313 := by
  unfold tailWord_2793200
  simp only [CollatzResearch.WordTrace]
  refine ⟨50938186740360457712984527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67917582320480610283979369 50938186740360457712984527)
  ·
    refine ⟨76407280110540686569476791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50938186740360457712984527 76407280110540686569476791)
    ·
      refine ⟨114610920165811029854215187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76407280110540686569476791 114610920165811029854215187)
      ·
        refine ⟨171916380248716544781322781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114610920165811029854215187 171916380248716544781322781)
        ·
          refine ⟨64468642593268704292996043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171916380248716544781322781 64468642593268704292996043)
          ·
            refine ⟨96702963889903056439494065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64468642593268704292996043 96702963889903056439494065)
            ·
              refine ⟨72527222917427292329620549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96702963889903056439494065 72527222917427292329620549)
              ·
                refine ⟨13598854297017617311803853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72527222917427292329620549 13598854297017617311803853)
                ·
                  refine ⟨5099570361381606491926445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13598854297017617311803853 5099570361381606491926445)
                  ·
                    refine ⟨1912338885518102434472417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5099570361381606491926445 1912338885518102434472417)
                    ·
                      refine ⟨1434254164138576825854313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912338885518102434472417 1434254164138576825854313)
                      ·
                        rfl

theorem cell23_2793200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 3, 2].length) (baseStart_2793200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793200 prefixEnd_2793200 := by exact prefixLift 2793200
  have htrace : WordTrace (prefixWord ++ tailWord_2793200) baseStart_2793200 baseEnd_2793200 := by
    simpa [prefixWord, tailWord_2793200, baseEnd_2793200] using wordTrace_append hprefix tailTrace_2793200
  have hstable : (prefixWord ++ tailWord_2793200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793200).length < 2 ^ (prefixWord ++ tailWord_2793200).sum := by decide
  have hdescent : baseEnd_2793200 < baseStart_2793200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793204 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2793204 : Nat := 118140960795 + 2793204 * 2 ^ 59
def prefixEnd_2793204 : Nat := 4983230072969 + 3 ^ 40 * 2793204 * 2
def baseEnd_2793204 : Nat := 1434256218061194810204295

theorem tailTrace_2793204 : CollatzResearch.WordTrace tailWord_2793204 prefixEnd_2793204 1434256218061194810204295 := by
  unfold tailWord_2793204
  simp only [CollatzResearch.WordTrace]
  refine ⟨50938259686353212054557333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67917679581804282739409777 50938259686353212054557333)
  ·
    refine ⟨2387730922797806815057375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50938259686353212054557333 2387730922797806815057375)
    ·
      refine ⟨3581596384196710222586063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387730922797806815057375 3581596384196710222586063)
      ·
        refine ⟨5372394576295065333879095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3581596384196710222586063 5372394576295065333879095)
        ·
          refine ⟨8058591864442598000818643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5372394576295065333879095 8058591864442598000818643)
          ·
            refine ⟨12087887796663897001227965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8058591864442598000818643 12087887796663897001227965)
            ·
              refine ⟨4532957923748961375460487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12087887796663897001227965 4532957923748961375460487)
              ·
                refine ⟨6799436885623442063190731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532957923748961375460487 6799436885623442063190731)
                ·
                  refine ⟨10199155328435163094786097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6799436885623442063190731 10199155328435163094786097)
                  ·
                    refine ⟨7649366496326372321089573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10199155328435163094786097 7649366496326372321089573)
                    ·
                      refine ⟨1434256218061194810204295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7649366496326372321089573 1434256218061194810204295)
                      ·
                        rfl

theorem cell23_2793204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2793204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793204 prefixEnd_2793204 := by exact prefixLift 2793204
  have htrace : WordTrace (prefixWord ++ tailWord_2793204) baseStart_2793204 baseEnd_2793204 := by
    simpa [prefixWord, tailWord_2793204, baseEnd_2793204] using wordTrace_append hprefix tailTrace_2793204
  have hstable : (prefixWord ++ tailWord_2793204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793204).length < 2 ^ (prefixWord ++ tailWord_2793204).sum := by decide
  have hdescent : baseEnd_2793204 < baseStart_2793204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793214 : List Nat := [4, 2, 2, 1, 4, 1, 2, 7]
def baseStart_2793214 : Nat := 118140960795 + 2793214 * 2 ^ 59
def prefixEnd_2793214 : Nat := 4983230072969 + 3 ^ 40 * 2793214 * 2
def baseEnd_2793214 : Nat := 53120790846953324854787

theorem tailTrace_2793214 : CollatzResearch.WordTrace tailWord_2793214 prefixEnd_2793214 53120790846953324854787 := by
  unfold tailWord_2793214
  simp only [CollatzResearch.WordTrace]
  refine ⟨12734610512833774477122337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67917922735113463877985797 12734610512833774477122337)
  ·
    refine ⟨9550957884625330857841753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12734610512833774477122337 9550957884625330857841753)
    ·
      refine ⟨7163218413468998143381315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9550957884625330857841753 7163218413468998143381315)
      ·
        refine ⟨10744827620203497215071973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7163218413468998143381315 10744827620203497215071973)
        ·
          refine ⟨2014655178788155727825995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10744827620203497215071973 2014655178788155727825995)
          ·
            refine ⟨3021982768182233591738993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014655178788155727825995 3021982768182233591738993)
            ·
              refine ⟨2266487076136675193804245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3021982768182233591738993 2266487076136675193804245)
              ·
                refine ⟨53120790846953324854787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2266487076136675193804245 53120790846953324854787)
                ·
                  rfl

theorem cell23_2793214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_2793214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793214 prefixEnd_2793214 := by exact prefixLift 2793214
  have htrace : WordTrace (prefixWord ++ tailWord_2793214) baseStart_2793214 baseEnd_2793214 := by
    simpa [prefixWord, tailWord_2793214, baseEnd_2793214] using wordTrace_append hprefix tailTrace_2793214
  have hstable : (prefixWord ++ tailWord_2793214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793214).length < 2 ^ (prefixWord ++ tailWord_2793214).sum := by decide
  have hdescent : baseEnd_2793214 < baseStart_2793214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793217 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_2793217 : Nat := 118140960795 + 2793217 * 2 ^ 59
def prefixEnd_2793217 : Nat := 4983230072969 + 3 ^ 40 * 2793217 * 2
def baseEnd_2793217 : Nat := 1434262893309703259341735

theorem tailTrace_2793217 : CollatzResearch.WordTrace tailWord_2793217 prefixEnd_2793217 1434262893309703259341735 := by
  unfold tailWord_2793217
  simp only [CollatzResearch.WordTrace]
  refine ⟨101876993521659327329337905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67917995681106218219558603 101876993521659327329337905)
  ·
    refine ⟨76407745141244495497003429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101876993521659327329337905 76407745141244495497003429)
    ·
      refine ⟨14326452213983342905688143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76407745141244495497003429 14326452213983342905688143)
      ·
        refine ⟨21489678320975014358532215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14326452213983342905688143 21489678320975014358532215)
        ·
          refine ⟨32234517481462521537798323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21489678320975014358532215 32234517481462521537798323)
          ·
            refine ⟨48351776222193782306697485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32234517481462521537798323 48351776222193782306697485)
            ·
              refine ⟨18131916083322668365011557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48351776222193782306697485 18131916083322668365011557)
              ·
                refine ⟨3399734265623000318439667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18131916083322668365011557 3399734265623000318439667)
                ·
                  refine ⟨5099601398434500477659501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399734265623000318439667 5099601398434500477659501)
                  ·
                    refine ⟨1912350524412937679122313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5099601398434500477659501 1912350524412937679122313)
                    ·
                      refine ⟨1434262893309703259341735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912350524412937679122313 1434262893309703259341735)
                      ·
                        rfl

theorem cell23_2793217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_2793217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793217 prefixEnd_2793217 := by exact prefixLift 2793217
  have htrace : WordTrace (prefixWord ++ tailWord_2793217) baseStart_2793217 baseEnd_2793217 := by
    simpa [prefixWord, tailWord_2793217, baseEnd_2793217] using wordTrace_append hprefix tailTrace_2793217
  have hstable : (prefixWord ++ tailWord_2793217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793217).length < 2 ^ (prefixWord ++ tailWord_2793217).sum := by decide
  have hdescent : baseEnd_2793217 < baseStart_2793217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793233 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_2793233 : Nat := 118140960795 + 2793233 * 2 ^ 59
def prefixEnd_2793233 : Nat := 4983230072969 + 3 ^ 40 * 2793233 * 2
def baseEnd_2793233 : Nat := 1434271109000175196741661

theorem tailTrace_2793233 : CollatzResearch.WordTrace tailWord_2793233 prefixEnd_2793233 1434271109000175196741661 := by
  unfold tailWord_2793233
  simp only [CollatzResearch.WordTrace]
  refine ⟨101877577089601362061920353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67918384726400908041280235 101877577089601362061920353)
  ·
    refine ⟨76408182817201021546440265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101877577089601362061920353 76408182817201021546440265)
    ·
      refine ⟨57306137112900766159830199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76408182817201021546440265 57306137112900766159830199)
      ·
        refine ⟨85959205669351149239745299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57306137112900766159830199 85959205669351149239745299)
        ·
          refine ⟨128938808504026723859617949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85959205669351149239745299 128938808504026723859617949)
          ·
            refine ⟨48352053189010021447356731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128938808504026723859617949 48352053189010021447356731)
            ·
              refine ⟨72528079783515032171035097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48352053189010021447356731 72528079783515032171035097)
              ·
                refine ⟨54396059837636274128276323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72528079783515032171035097 54396059837636274128276323)
                ·
                  refine ⟨81594089756454411192414485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54396059837636274128276323 81594089756454411192414485)
                  ·
                    refine ⟨3824722957333800524644429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81594089756454411192414485 3824722957333800524644429)
                    ·
                      refine ⟨1434271109000175196741661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3824722957333800524644429 1434271109000175196741661)
                      ·
                        rfl

theorem cell23_2793233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_2793233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793233 prefixEnd_2793233 := by exact prefixLift 2793233
  have htrace : WordTrace (prefixWord ++ tailWord_2793233) baseStart_2793233 baseEnd_2793233 := by
    simpa [prefixWord, tailWord_2793233, baseEnd_2793233] using wordTrace_append hprefix tailTrace_2793233
  have hstable : (prefixWord ++ tailWord_2793233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793233).length < 2 ^ (prefixWord ++ tailWord_2793233).sum := by decide
  have hdescent : baseEnd_2793233 < baseStart_2793233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793247 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 4, 2, 2]
def baseStart_2793247 : Nat := 118140960795 + 2793247 * 2 ^ 59
def prefixEnd_2793247 : Nat := 4983230072969 + 3 ^ 40 * 2793247 * 2
def baseEnd_2793247 : Nat := 1434278297729338141966597

theorem tailTrace_2793247 : CollatzResearch.WordTrace tailWord_2793247 prefixEnd_2793247 1434278297729338141966597 := by
  unfold tailWord_2793247
  simp only [CollatzResearch.WordTrace]
  refine ⟨101878087711550642452929995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67918725141033761635286663 101878087711550642452929995)
  ·
    refine ⟨152817131567325963679394993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101878087711550642452929995 152817131567325963679394993)
    ·
      refine ⟨114612848675494472759546245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152817131567325963679394993 114612848675494472759546245)
      ·
        refine ⟨21489909126655213642414921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114612848675494472759546245 21489909126655213642414921)
        ·
          refine ⟨16117431844991410231811191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21489909126655213642414921 16117431844991410231811191)
          ·
            refine ⟨24176147767487115347716787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16117431844991410231811191 24176147767487115347716787)
            ·
              refine ⟨36264221651230673021575181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24176147767487115347716787 36264221651230673021575181)
              ·
                refine ⟨13599083119211502383090693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36264221651230673021575181 13599083119211502383090693)
                ·
                  refine ⟨2549828084852156696829505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13599083119211502383090693 2549828084852156696829505)
                  ·
                    refine ⟨1912371063639117522622129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2549828084852156696829505 1912371063639117522622129)
                    ·
                      refine ⟨1434278297729338141966597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912371063639117522622129 1434278297729338141966597)
                      ·
                        rfl

theorem cell23_2793247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_2793247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793247 prefixEnd_2793247 := by exact prefixLift 2793247
  have htrace : WordTrace (prefixWord ++ tailWord_2793247) baseStart_2793247 baseEnd_2793247 := by
    simpa [prefixWord, tailWord_2793247, baseEnd_2793247] using wordTrace_append hprefix tailTrace_2793247
  have hstable : (prefixWord ++ tailWord_2793247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793247).length < 2 ^ (prefixWord ++ tailWord_2793247).sum := by decide
  have hdescent : baseEnd_2793247 < baseStart_2793247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793250 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_2793250 : Nat := 118140960795 + 2793250 * 2 ^ 59
def prefixEnd_2793250 : Nat := 4983230072969 + 3 ^ 40 * 2793250 * 2
def baseEnd_2793250 : Nat := 1434279838171301630229083

theorem tailTrace_2793250 : CollatzResearch.WordTrace tailWord_2793250 prefixEnd_2793250 1434279838171301630229083 := by
  unfold tailWord_2793250
  simp only [CollatzResearch.WordTrace]
  refine ⟨25469549282634943491322301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67918798087026515976859469 25469549282634943491322301)
  ·
    refine ⟨9551080980988103809245863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25469549282634943491322301 9551080980988103809245863)
    ·
      refine ⟨14326621471482155713868795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9551080980988103809245863 14326621471482155713868795)
      ·
        refine ⟨21489932207223233570803193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14326621471482155713868795 21489932207223233570803193)
        ·
          refine ⟨16117449155417425178102395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21489932207223233570803193 16117449155417425178102395)
          ·
            refine ⟨24176173733126137767153593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16117449155417425178102395 24176173733126137767153593)
            ·
              refine ⟨18132130299844603325365195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24176173733126137767153593 18132130299844603325365195)
              ·
                refine ⟨27198195449766904988047793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18132130299844603325365195 27198195449766904988047793)
                ·
                  refine ⟨20398646587325178741035845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27198195449766904988047793 20398646587325178741035845)
                  ·
                    refine ⟨3824746235123471013944221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20398646587325178741035845 3824746235123471013944221)
                    ·
                      refine ⟨1434279838171301630229083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3824746235123471013944221 1434279838171301630229083)
                      ·
                        rfl

theorem cell23_2793250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_2793250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793250 prefixEnd_2793250 := by exact prefixLift 2793250
  have htrace : WordTrace (prefixWord ++ tailWord_2793250) baseStart_2793250 baseEnd_2793250 := by
    simpa [prefixWord, tailWord_2793250, baseEnd_2793250] using wordTrace_append hprefix tailTrace_2793250
  have hstable : (prefixWord ++ tailWord_2793250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793250).length < 2 ^ (prefixWord ++ tailWord_2793250).sum := by decide
  have hdescent : baseEnd_2793250 < baseStart_2793250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793320 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2793320 : Nat := 118140960795 + 2793320 * 2 ^ 59
def prefixEnd_2793320 : Nat := 4983230072969 + 3 ^ 40 * 2793320 * 2
def baseEnd_2793320 : Nat := 1434315781817116356353761

theorem tailTrace_2793320 : CollatzResearch.WordTrace tailWord_2793320 prefixEnd_2793320 1434315781817116356353761 := by
  unfold tailWord_2793320
  simp only [CollatzResearch.WordTrace]
  refine ⟨50940375120143087960168707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67920500160190783946891609 50940375120143087960168707)
  ·
    refine ⟨76410562680214631940253061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50940375120143087960168707 76410562680214631940253061)
    ·
      refine ⟨14326980502540243488797449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76410562680214631940253061 14326980502540243488797449)
      ·
        refine ⟨10745235376905182616598087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14326980502540243488797449 10745235376905182616598087)
        ·
          refine ⟨16117853065357773924897131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10745235376905182616598087 16117853065357773924897131)
          ·
            refine ⟨24176779598036660887345697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16117853065357773924897131 24176779598036660887345697)
            ·
              refine ⟨18132584698527495665509273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24176779598036660887345697 18132584698527495665509273)
              ·
                refine ⟨13599438523895621749131955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18132584698527495665509273 13599438523895621749131955)
                ·
                  refine ⟨20399157785843432623697933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13599438523895621749131955 20399157785843432623697933)
                  ·
                    refine ⟨7649684169691287233886725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20399157785843432623697933 7649684169691287233886725)
                    ·
                      refine ⟨1434315781817116356353761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7649684169691287233886725 1434315781817116356353761)
                      ·
                        rfl

theorem cell23_2793320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2793320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793320 prefixEnd_2793320 := by exact prefixLift 2793320
  have htrace : WordTrace (prefixWord ++ tailWord_2793320) baseStart_2793320 baseEnd_2793320 := by
    simpa [prefixWord, tailWord_2793320, baseEnd_2793320] using wordTrace_append hprefix tailTrace_2793320
  have hstable : (prefixWord ++ tailWord_2793320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793320).length < 2 ^ (prefixWord ++ tailWord_2793320).sum := by decide
  have hdescent : baseEnd_2793320 < baseStart_2793320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793343 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 8]
def baseStart_2793343 : Nat := 118140960795 + 2793343 * 2 ^ 59
def prefixEnd_2793343 : Nat := 4983230072969 + 3 ^ 40 * 2793343 * 2
def baseEnd_2793343 : Nat := 159369732430241085151795

theorem tailTrace_2793343 : CollatzResearch.WordTrace tailWord_2793343 prefixEnd_2793343 159369732430241085151795 := by
  unfold tailWord_2793343
  simp only [CollatzResearch.WordTrace]
  refine ⟨101881589119202850848424683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67921059412801900565616455 101881589119202850848424683)
  ·
    refine ⟨152822383678804276272637025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101881589119202850848424683 152822383678804276272637025)
    ·
      refine ⟨114616787759103207204477769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152822383678804276272637025 114616787759103207204477769)
      ·
        refine ⟨85962590819327405403358327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114616787759103207204477769 85962590819327405403358327)
        ·
          refine ⟨128943886228991108105037491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85962590819327405403358327 128943886228991108105037491)
          ·
            refine ⟨193415829343486662157556237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128943886228991108105037491 193415829343486662157556237)
            ·
              refine ⟨72530936003807498309083589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193415829343486662157556237 72530936003807498309083589)
              ·
                refine ⟨13599550500713905932953173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72530936003807498309083589 13599550500713905932953173)
                ·
                  refine ⟨159369732430241085151795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13599550500713905932953173 159369732430241085151795)
                  ·
                    rfl

theorem cell23_2793343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 8].length) (baseStart_2793343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793343 prefixEnd_2793343 := by exact prefixLift 2793343
  have htrace : WordTrace (prefixWord ++ tailWord_2793343) baseStart_2793343 baseEnd_2793343 := by
    simpa [prefixWord, tailWord_2793343, baseEnd_2793343] using wordTrace_append hprefix tailTrace_2793343
  have hstable : (prefixWord ++ tailWord_2793343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793343).length < 2 ^ (prefixWord ++ tailWord_2793343).sum := by decide
  have hdescent : baseEnd_2793343 < baseStart_2793343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793364 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_2793364 : Nat := 118140960795 + 2793364 * 2 ^ 59
def prefixEnd_2793364 : Nat := 4983230072969 + 3 ^ 40 * 2793364 * 2
def baseEnd_2793364 : Nat := 478112791655304728067853

theorem tailTrace_2793364 : CollatzResearch.WordTrace tailWord_2793364 prefixEnd_2793364 478112791655304728067853 := by
  unfold tailWord_2793364
  simp only [CollatzResearch.WordTrace]
  refine ⟨50941177526063385717469573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67921570034751180956626097 50941177526063385717469573)
  ·
    refine ⟨9551470786136884822025545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50941177526063385717469573 9551470786136884822025545)
    ·
      refine ⟨7163603089602663616519159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9551470786136884822025545 7163603089602663616519159)
      ·
        refine ⟨10745404634403995424778739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7163603089602663616519159 10745404634403995424778739)
        ·
          refine ⟨16118106951605993137168109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10745404634403995424778739 16118106951605993137168109)
          ·
            refine ⟨6044290106852247426438041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16118106951605993137168109 6044290106852247426438041)
            ·
              refine ⟨4533217580139185569828531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6044290106852247426438041 4533217580139185569828531)
              ·
                refine ⟨6799826370208778354742797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4533217580139185569828531 6799826370208778354742797)
                ·
                  refine ⟨2549934888828291883028549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6799826370208778354742797 2549934888828291883028549)
                  ·
                    refine ⟨478112791655304728067853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2549934888828291883028549 478112791655304728067853)
                    ·
                      rfl

theorem cell23_2793364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_2793364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793364 prefixEnd_2793364 := by exact prefixLift 2793364
  have htrace : WordTrace (prefixWord ++ tailWord_2793364) baseStart_2793364 baseEnd_2793364 := by
    simpa [prefixWord, tailWord_2793364, baseEnd_2793364] using wordTrace_append hprefix tailTrace_2793364
  have hstable : (prefixWord ++ tailWord_2793364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793364).length < 2 ^ (prefixWord ++ tailWord_2793364).sum := by decide
  have hdescent : baseEnd_2793364 < baseStart_2793364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793440 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_2793440 : Nat := 118140960795 + 2793440 * 2 ^ 59
def prefixEnd_2793440 : Nat := 4983230072969 + 3 ^ 40 * 2793440 * 2
def baseEnd_2793440 : Nat := 1434377399495655886853209

theorem tailTrace_2793440 : CollatzResearch.WordTrace tailWord_2793440 prefixEnd_2793440 1434377399495655886853209 := by
  unfold tailWord_2793440
  simp only [CollatzResearch.WordTrace]
  refine ⟨50942563499925718207352887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67923417999900957609803849 50942563499925718207352887)
  ·
    refine ⟨76413845249888577311029331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50942563499925718207352887 76413845249888577311029331)
    ·
      refine ⟨114620767874832865966543997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76413845249888577311029331 114620767874832865966543997)
      ·
        refine ⟨42982787953062324737453999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114620767874832865966543997 42982787953062324737453999)
        ·
          refine ⟨64474181929593487106180999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42982787953062324737453999 64474181929593487106180999)
          ·
            refine ⟨96711272894390230659271499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64474181929593487106180999 96711272894390230659271499)
            ·
              refine ⟨145066909341585345988907249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96711272894390230659271499 145066909341585345988907249)
              ·
                refine ⟨108800182006189009491680437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145066909341585345988907249 108800182006189009491680437)
                ·
                  refine ⟨10200017063080219639845041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108800182006189009491680437 10200017063080219639845041)
                  ·
                    refine ⟨7650012797310164729883781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10200017063080219639845041 7650012797310164729883781)
                    ·
                      refine ⟨1434377399495655886853209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7650012797310164729883781 1434377399495655886853209)
                      ·
                        rfl

theorem cell23_2793440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_2793440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793440 prefixEnd_2793440 := by exact prefixLift 2793440
  have htrace : WordTrace (prefixWord ++ tailWord_2793440) baseStart_2793440 baseEnd_2793440 := by
    simpa [prefixWord, tailWord_2793440, baseEnd_2793440] using wordTrace_append hprefix tailTrace_2793440
  have hstable : (prefixWord ++ tailWord_2793440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793440).length < 2 ^ (prefixWord ++ tailWord_2793440).sum := by decide
  have hdescent : baseEnd_2793440 < baseStart_2793440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793444 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_2793444 : Nat := 118140960795 + 2793444 * 2 ^ 59
def prefixEnd_2793444 : Nat := 4983230072969 + 3 ^ 40 * 2793444 * 2
def baseEnd_2793444 : Nat := 1434379453418273871203191

theorem tailTrace_2793444 : CollatzResearch.WordTrace tailWord_2793444 prefixEnd_2793444 1434379453418273871203191 := by
  unfold tailWord_2793444
  simp only [CollatzResearch.WordTrace]
  refine ⟨50942636445918472548925693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67923515261224630065234257 50942636445918472548925693)
  ·
    refine ⟨19103488667219427205847135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50942636445918472548925693 19103488667219427205847135)
    ·
      refine ⟨28655233000829140808770703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19103488667219427205847135 28655233000829140808770703)
      ·
        refine ⟨42982849501243711213156055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28655233000829140808770703 42982849501243711213156055)
        ·
          refine ⟨64474274251865566819734083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42982849501243711213156055 64474274251865566819734083)
          ·
            refine ⟨96711411377798350229601125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64474274251865566819734083 96711411377798350229601125)
            ·
              refine ⟨18133389633337190668050211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96711411377798350229601125 18133389633337190668050211)
              ·
                refine ⟨27200084450005786002075317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18133389633337190668050211 27200084450005786002075317)
                ·
                  refine ⟨2550007917188042437694561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27200084450005786002075317 2550007917188042437694561)
                  ·
                    refine ⟨1912505937891031828270921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2550007917188042437694561 1912505937891031828270921)
                    ·
                      refine ⟨1434379453418273871203191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912505937891031828270921 1434379453418273871203191)
                      ·
                        rfl

theorem cell23_2793444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_2793444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793444 prefixEnd_2793444 := by exact prefixLift 2793444
  have htrace : WordTrace (prefixWord ++ tailWord_2793444) baseStart_2793444 baseEnd_2793444 := by
    simpa [prefixWord, tailWord_2793444, baseEnd_2793444] using wordTrace_append hprefix tailTrace_2793444
  have hstable : (prefixWord ++ tailWord_2793444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793444).length < 2 ^ (prefixWord ++ tailWord_2793444).sum := by decide
  have hdescent : baseEnd_2793444 < baseStart_2793444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793450 : List Nat := [3, 1, 3, 1, 2, 1, 1, 11]
def baseStart_2793450 : Nat := 118140960795 + 2793450 * 2 ^ 59
def prefixEnd_2793450 : Nat := 4983230072969 + 3 ^ 40 * 2793450 * 2
def baseEnd_2793450 : Nat := 53125279048229661026969

theorem tailTrace_2793450 : CollatzResearch.WordTrace tailWord_2793450 prefixEnd_2793450 53125279048229661026969 := by
  unfold tailWord_2793450
  simp only [CollatzResearch.WordTrace]
  refine ⟨25471372932453802030642451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67923661153210138748379869 25471372932453802030642451)
  ·
    refine ⟨38207059398680703045963677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25471372932453802030642451 38207059398680703045963677)
    ·
      refine ⟨14327647274505263642236379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38207059398680703045963677 14327647274505263642236379)
      ·
        refine ⟨21491470911757895463354569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14327647274505263642236379 21491470911757895463354569)
        ·
          refine ⟨16118603183818421597515927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21491470911757895463354569 16118603183818421597515927)
          ·
            refine ⟨24177904775727632396273891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16118603183818421597515927 24177904775727632396273891)
            ·
              refine ⟨36266857163591448594410837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24177904775727632396273891 36266857163591448594410837)
              ·
                refine ⟨53125279048229661026969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 36266857163591448594410837 53125279048229661026969)
                ·
                  rfl

theorem cell23_2793450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 11].length) (baseStart_2793450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793450 prefixEnd_2793450 := by exact prefixLift 2793450
  have htrace : WordTrace (prefixWord ++ tailWord_2793450) baseStart_2793450 baseEnd_2793450 := by
    simpa [prefixWord, tailWord_2793450, baseEnd_2793450] using wordTrace_append hprefix tailTrace_2793450
  have hstable : (prefixWord ++ tailWord_2793450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793450).length < 2 ^ (prefixWord ++ tailWord_2793450).sum := by decide
  have hdescent : baseEnd_2793450 < baseStart_2793450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793480 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 1, 9]
def baseStart_2793480 : Nat := 118140960795 + 2793480 * 2 ^ 59
def prefixEnd_2793480 : Nat := 4983230072969 + 3 ^ 40 * 2793480 * 2
def baseEnd_2793480 : Nat := 478132646240611910117675

theorem tailTrace_2793480 : CollatzResearch.WordTrace tailWord_2793480 prefixEnd_2793480 478132646240611910117675 := by
  unfold tailWord_2793480
  simp only [CollatzResearch.WordTrace]
  refine ⟨50943292959853261623080947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67924390613137682164107929 50943292959853261623080947)
  ·
    refine ⟨76414939439779892434621421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50943292959853261623080947 76414939439779892434621421)
    ·
      refine ⟨28655602289917459662983033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76414939439779892434621421 28655602289917459662983033)
      ·
        refine ⟨21491701717438094747237275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28655602289917459662983033 21491701717438094747237275)
        ·
          refine ⟨32237552576157142120855913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21491701717438094747237275 32237552576157142120855913)
          ·
            refine ⟨24178164432117856590641935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32237552576157142120855913 24178164432117856590641935)
            ·
              refine ⟨36267246648176784885962903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24178164432117856590641935 36267246648176784885962903)
              ·
                refine ⟨54400869972265177328944355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36267246648176784885962903 54400869972265177328944355)
                ·
                  refine ⟨81601304958397765993416533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54400869972265177328944355 81601304958397765993416533)
                  ·
                    refine ⟨478132646240611910117675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 81601304958397765993416533 478132646240611910117675)
                    ·
                      rfl

theorem cell23_2793480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_2793480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793480 prefixEnd_2793480 := by exact prefixLift 2793480
  have htrace : WordTrace (prefixWord ++ tailWord_2793480) baseStart_2793480 baseEnd_2793480 := by
    simpa [prefixWord, tailWord_2793480, baseEnd_2793480] using wordTrace_append hprefix tailTrace_2793480
  have hstable : (prefixWord ++ tailWord_2793480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793480).length < 2 ^ (prefixWord ++ tailWord_2793480).sum := by decide
  have hdescent : baseEnd_2793480 < baseStart_2793480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793512 : List Nat := [2, 1, 5, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2793512 : Nat := 118140960795 + 2793512 * 2 ^ 59
def prefixEnd_2793512 : Nat := 4983230072969 + 3 ^ 40 * 2793512 * 2
def baseEnd_2793512 : Nat := 1434414370102779605152879

theorem tailTrace_2793512 : CollatzResearch.WordTrace tailWord_2793512 prefixEnd_2793512 1434414370102779605152879 := by
  unfold tailWord_2793512
  simp only [CollatzResearch.WordTrace]
  refine ⟨50943876527795296355663395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67925168703727061807551193 50943876527795296355663395)
  ·
    refine ⟨76415814791692944533495093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50943876527795296355663395 76415814791692944533495093)
    ·
      refine ⟨7163982636721213550015165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76415814791692944533495093 7163982636721213550015165)
      ·
        refine ⟨2686493488770455081255687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7163982636721213550015165 2686493488770455081255687)
        ·
          refine ⟨4029740233155682621883531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686493488770455081255687 4029740233155682621883531)
          ·
            refine ⟨6044610349733523932825297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029740233155682621883531 6044610349733523932825297)
            ·
              refine ⟨4533457762300142949618973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6044610349733523932825297 4533457762300142949618973)
              ·
                refine ⟨1700046660862553606107115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4533457762300142949618973 1700046660862553606107115)
                ·
                  refine ⟨2550069991293830409160673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700046660862553606107115 2550069991293830409160673)
                  ·
                    refine ⟨1912552493470372806870505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2550069991293830409160673 1912552493470372806870505)
                    ·
                      refine ⟨1434414370102779605152879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912552493470372806870505 1434414370102779605152879)
                      ·
                        rfl

theorem cell23_2793512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2793512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793512 prefixEnd_2793512 := by exact prefixLift 2793512
  have htrace : WordTrace (prefixWord ++ tailWord_2793512) baseStart_2793512 baseEnd_2793512 := by
    simpa [prefixWord, tailWord_2793512, baseEnd_2793512] using wordTrace_append hprefix tailTrace_2793512
  have hstable : (prefixWord ++ tailWord_2793512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793512).length < 2 ^ (prefixWord ++ tailWord_2793512).sum := by decide
  have hdescent : baseEnd_2793512 < baseStart_2793512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793521 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 1, 3, 2]
def baseStart_2793521 : Nat := 118140960795 + 2793521 * 2 ^ 59
def prefixEnd_2793521 : Nat := 4983230072969 + 3 ^ 40 * 2793521 * 2
def baseEnd_2793521 : Nat := 1434418991428670069940337

theorem tailTrace_2793521 : CollatzResearch.WordTrace tailWord_2793521 prefixEnd_2793521 1434418991428670069940337 := by
  unfold tailWord_2793521
  simp only [CollatzResearch.WordTrace]
  refine ⟨101888081312557987248404417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67925387541705324832269611 101888081312557987248404417)
  ·
    refine ⟨76416060984418490436303313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101888081312557987248404417 76416060984418490436303313)
    ·
      refine ⟨57312045738313867827227485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76416060984418490436303313 57312045738313867827227485)
      ·
        refine ⟨21492017151867700435210307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57312045738313867827227485 21492017151867700435210307)
        ·
          refine ⟨32238025727801550652815461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21492017151867700435210307 32238025727801550652815461)
          ·
            refine ⟨6044629823962790747402899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32238025727801550652815461 6044629823962790747402899)
            ·
              refine ⟨9066944735944186121104349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6044629823962790747402899 9066944735944186121104349)
              ·
                refine ⟨3400104275979069795414131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9066944735944186121104349 3400104275979069795414131)
                ·
                  refine ⟨5100156413968604693121197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400104275979069795414131 5100156413968604693121197)
                  ·
                    refine ⟨1912558655238226759920449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5100156413968604693121197 1912558655238226759920449)
                    ·
                      refine ⟨1434418991428670069940337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912558655238226759920449 1434418991428670069940337)
                      ·
                        rfl

theorem cell23_2793521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_2793521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793521 prefixEnd_2793521 := by exact prefixLift 2793521
  have htrace : WordTrace (prefixWord ++ tailWord_2793521) baseStart_2793521 baseEnd_2793521 := by
    simpa [prefixWord, tailWord_2793521, baseEnd_2793521] using wordTrace_append hprefix tailTrace_2793521
  have hstable : (prefixWord ++ tailWord_2793521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793521).length < 2 ^ (prefixWord ++ tailWord_2793521).sum := by decide
  have hdescent : baseEnd_2793521 < baseStart_2793521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793528 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 2, 1, 3]
def baseStart_2793528 : Nat := 118140960795 + 2793528 * 2 ^ 59
def prefixEnd_2793528 : Nat := 4983230072969 + 3 ^ 40 * 2793528 * 2
def baseEnd_2793528 : Nat := 1434422585793251542552805

theorem tailTrace_2793528 : CollatzResearch.WordTrace tailWord_2793528 prefixEnd_2793528 1434422585793251542552805 := by
  unfold tailWord_2793528
  simp only [CollatzResearch.WordTrace]
  refine ⟨50944168311766313721954619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67925557749021751629272825 50944168311766313721954619)
  ·
    refine ⟨76416252467649470582931929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50944168311766313721954619 76416252467649470582931929)
    ·
      refine ⟨57312189350737102937198947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76416252467649470582931929 57312189350737102937198947)
      ·
        refine ⟨85968284026105654405798421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57312189350737102937198947 85968284026105654405798421)
        ·
          refine ⟨4029763313723702550271801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85968284026105654405798421 4029763313723702550271801)
          ·
            refine ⟨3022322485292776912703851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4029763313723702550271801 3022322485292776912703851)
            ·
              refine ⟨4533483727939165369055777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022322485292776912703851 4533483727939165369055777)
              ·
                refine ⟨3400112795954374026791833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4533483727939165369055777 3400112795954374026791833)
                ·
                  refine ⟨2550084596965780520093875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3400112795954374026791833 2550084596965780520093875)
                  ·
                    refine ⟨3825126895448670780140813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2550084596965780520093875 3825126895448670780140813)
                    ·
                      refine ⟨1434422585793251542552805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3825126895448670780140813 1434422585793251542552805)
                      ·
                        rfl

theorem cell23_2793528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_2793528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793528 prefixEnd_2793528 := by exact prefixLift 2793528
  have htrace : WordTrace (prefixWord ++ tailWord_2793528) baseStart_2793528 baseEnd_2793528 := by
    simpa [prefixWord, tailWord_2793528, baseEnd_2793528] using wordTrace_append hprefix tailTrace_2793528
  have hstable : (prefixWord ++ tailWord_2793528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793528).length < 2 ^ (prefixWord ++ tailWord_2793528).sum := by decide
  have hdescent : baseEnd_2793528 < baseStart_2793528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793557 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 7]
def baseStart_2793557 : Nat := 118140960795 + 2793557 * 2 ^ 59
def prefixEnd_2793557 : Nat := 4983230072969 + 3 ^ 40 * 2793557 * 2
def baseEnd_2793557 : Nat := 159381941859136881010019

theorem tailTrace_2793557 : CollatzResearch.WordTrace tailWord_2793557 prefixEnd_2793557 159381941859136881010019 := by
  unfold tailWord_2793557
  simp only [CollatzResearch.WordTrace]
  refine ⟨101889394340427565396714925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67926262893618376931143283 101889394340427565396714925)
  ·
    refine ⟨38208522877660337023768097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101889394340427565396714925 38208522877660337023768097)
    ·
      refine ⟨28656392158245252767826073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38208522877660337023768097 28656392158245252767826073)
      ·
        refine ⟨21492294118683939575869555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28656392158245252767826073 21492294118683939575869555)
        ·
          refine ⟨32238441178025909363804333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21492294118683939575869555 32238441178025909363804333)
          ·
            refine ⟨12089415441759716011426625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32238441178025909363804333 12089415441759716011426625)
            ·
              refine ⟨9067061581319787008569969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12089415441759716011426625 9067061581319787008569969)
              ·
                refine ⟨6800296185989840256427477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9067061581319787008569969 6800296185989840256427477)
                ·
                  refine ⟨159381941859136881010019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6800296185989840256427477 159381941859136881010019)
                  ·
                    rfl

theorem cell23_2793557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_2793557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793557 prefixEnd_2793557 := by exact prefixLift 2793557
  have htrace : WordTrace (prefixWord ++ tailWord_2793557) baseStart_2793557 baseEnd_2793557 := by
    simpa [prefixWord, tailWord_2793557, baseEnd_2793557] using wordTrace_append hprefix tailTrace_2793557
  have hstable : (prefixWord ++ tailWord_2793557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793557).length < 2 ^ (prefixWord ++ tailWord_2793557).sum := by decide
  have hdescent : baseEnd_2793557 < baseStart_2793557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793567 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 3]
def baseStart_2793567 : Nat := 118140960795 + 2793567 * 2 ^ 59
def prefixEnd_2793567 : Nat := 4983230072969 + 3 ^ 40 * 2793567 * 2
def baseEnd_2793567 : Nat := 1434442611538776889965125

theorem tailTrace_2793567 : CollatzResearch.WordTrace tailWord_2793567 prefixEnd_2793567 1434442611538776889965125 := by
  unfold tailWord_2793567
  simp only [CollatzResearch.WordTrace]
  refine ⟨101889759070391337104578955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67926506046927558069719303 101889759070391337104578955)
  ·
    refine ⟨152834638605587005656868433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101889759070391337104578955 152834638605587005656868433)
    ·
      refine ⟨114625978954190254242651325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152834638605587005656868433 114625978954190254242651325)
      ·
        refine ⟨42984742107821345340994247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114625978954190254242651325 42984742107821345340994247)
        ·
          refine ⟨64477113161732018011491371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42984742107821345340994247 64477113161732018011491371)
          ·
            refine ⟨96715669742598027017237057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64477113161732018011491371 96715669742598027017237057)
            ·
              refine ⟨72536752306948520262927793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96715669742598027017237057 72536752306948520262927793)
              ·
                refine ⟨54402564230211390197195845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72536752306948520262927793 54402564230211390197195845)
                ·
                  refine ⟨10200480793164635661974221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54402564230211390197195845 10200480793164635661974221)
                  ·
                    refine ⟨3825180297436738373240333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10200480793164635661974221 3825180297436738373240333)
                    ·
                      refine ⟨1434442611538776889965125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3825180297436738373240333 1434442611538776889965125)
                      ·
                        rfl

theorem cell23_2793567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_2793567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793567 prefixEnd_2793567 := by exact prefixLift 2793567
  have htrace : WordTrace (prefixWord ++ tailWord_2793567) baseStart_2793567 baseEnd_2793567 := by
    simpa [prefixWord, tailWord_2793567, baseEnd_2793567] using wordTrace_append hprefix tailTrace_2793567
  have hstable : (prefixWord ++ tailWord_2793567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793567).length < 2 ^ (prefixWord ++ tailWord_2793567).sum := by decide
  have hdescent : baseEnd_2793567 < baseStart_2793567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793591 : List Nat := [1, 1, 3, 1, 1, 6, 3, 2, 5]
def baseStart_2793591 : Nat := 118140960795 + 2793591 * 2 ^ 59
def prefixEnd_2793591 : Nat := 4983230072969 + 3 ^ 40 * 2793591 * 2
def baseEnd_2793591 : Nat := 159383881674942755118335

theorem tailTrace_2793591 : CollatzResearch.WordTrace tailWord_2793591 prefixEnd_2793591 159383881674942755118335 := by
  unfold tailWord_2793591
  simp only [CollatzResearch.WordTrace]
  refine ⟨101890634422304389203452627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67927089614869592802301751 101890634422304389203452627)
  ·
    refine ⟨152835951633456583805178941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101890634422304389203452627 152835951633456583805178941)
    ·
      refine ⟨57313481862546218926942103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152835951633456583805178941 57313481862546218926942103)
      ·
        refine ⟨85970222793819328390413155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57313481862546218926942103 85970222793819328390413155)
        ·
          refine ⟨128955334190728992585619733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85970222793819328390413155 128955334190728992585619733)
          ·
            refine ⟨6044781290190421527450925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128955334190728992585619733 6044781290190421527450925)
            ·
              refine ⟨2266792983821408072794097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6044781290190421527450925 2266792983821408072794097)
              ·
                refine ⟨1700094737866056054595573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2266792983821408072794097 1700094737866056054595573)
                ·
                  refine ⟨159383881674942755118335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1700094737866056054595573 159383881674942755118335)
                  ·
                    rfl

theorem cell23_2793591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 5].length) (baseStart_2793591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793591 prefixEnd_2793591 := by exact prefixLift 2793591
  have htrace : WordTrace (prefixWord ++ tailWord_2793591) baseStart_2793591 baseEnd_2793591 := by
    simpa [prefixWord, tailWord_2793591, baseEnd_2793591] using wordTrace_append hprefix tailTrace_2793591
  have hstable : (prefixWord ++ tailWord_2793591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793591).length < 2 ^ (prefixWord ++ tailWord_2793591).sum := by decide
  have hdescent : baseEnd_2793591 < baseStart_2793591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793597 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_2793597 : Nat := 118140960795 + 2793597 * 2 ^ 59
def prefixEnd_2793597 : Nat := 4983230072969 + 3 ^ 40 * 2793597 * 2
def baseEnd_2793597 : Nat := 1434458015958411772589987

theorem tailTrace_2793597 : CollatzResearch.WordTrace tailWord_2793597 prefixEnd_2793597 1434458015958411772589987 := by
  unfold tailWord_2793597
  simp only [CollatzResearch.WordTrace]
  refine ⟨101890853260282652228171045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67927235506855101485447363 101890853260282652228171045)
  ·
    refine ⟨19104534986302997292782071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101890853260282652228171045 19104534986302997292782071)
    ·
      refine ⟨28656802479454495939173107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19104534986302997292782071 28656802479454495939173107)
      ·
        refine ⟨42985203719181743908759661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28656802479454495939173107 42985203719181743908759661)
        ·
          refine ⟨16119451394693153965784873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42985203719181743908759661 16119451394693153965784873)
          ·
            refine ⟨12089588546019865474338655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16119451394693153965784873 12089588546019865474338655)
            ·
              refine ⟨18134382819029798211507983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12089588546019865474338655 18134382819029798211507983)
              ·
                refine ⟨27201574228544697317261975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18134382819029798211507983 27201574228544697317261975)
                ·
                  refine ⟨40802361342817045975892963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27201574228544697317261975 40802361342817045975892963)
                  ·
                    refine ⟨61203542014225568963839445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40802361342817045975892963 61203542014225568963839445)
                    ·
                      refine ⟨1434458015958411772589987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61203542014225568963839445 1434458015958411772589987)
                      ·
                        rfl

theorem cell23_2793597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_2793597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793597 prefixEnd_2793597 := by exact prefixLift 2793597
  have htrace : WordTrace (prefixWord ++ tailWord_2793597) baseStart_2793597 baseEnd_2793597 := by
    simpa [prefixWord, tailWord_2793597, baseEnd_2793597] using wordTrace_append hprefix tailTrace_2793597
  have hstable : (prefixWord ++ tailWord_2793597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793597).length < 2 ^ (prefixWord ++ tailWord_2793597).sum := by decide
  have hdescent : baseEnd_2793597 < baseStart_2793597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793607 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_2793607 : Nat := 118140960795 + 2793607 * 2 ^ 59
def prefixEnd_2793607 : Nat := 4983230072969 + 3 ^ 40 * 2793607 * 2
def baseEnd_2793607 : Nat := 1434463150764956733464941

theorem tailTrace_2793607 : CollatzResearch.WordTrace tailWord_2793607 prefixEnd_2793607 1434463150764956733464941 := by
  unfold tailWord_2793607
  simp only [CollatzResearch.WordTrace]
  refine ⟨101891217990246423936035075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67927478660164282624023383 101891217990246423936035075)
  ·
    refine ⟨152836826985369635904052613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101891217990246423936035075 152836826985369635904052613)
    ·
      refine ⟨28656905059756806732009865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152836826985369635904052613 28656905059756806732009865)
      ·
        refine ⟨21492678794817605049007399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28656905059756806732009865 21492678794817605049007399)
        ·
          refine ⟨32239018192226407573511099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21492678794817605049007399 32239018192226407573511099)
          ·
            refine ⟨48358527288339611360266649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32239018192226407573511099 48358527288339611360266649)
            ·
              refine ⟨36268895466254708520199987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48358527288339611360266649 36268895466254708520199987)
              ·
                refine ⟨54403343199382062780299981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36268895466254708520199987 54403343199382062780299981)
                ·
                  refine ⟨20401253699768273542612493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54403343199382062780299981 20401253699768273542612493)
                  ·
                    refine ⟨7650470137413102578479685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20401253699768273542612493 7650470137413102578479685)
                    ·
                      refine ⟨1434463150764956733464941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7650470137413102578479685 1434463150764956733464941)
                      ·
                        rfl

theorem cell23_2793607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_2793607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793607 prefixEnd_2793607 := by exact prefixLift 2793607
  have htrace : WordTrace (prefixWord ++ tailWord_2793607) baseStart_2793607 baseEnd_2793607 := by
    simpa [prefixWord, tailWord_2793607, baseEnd_2793607] using wordTrace_append hprefix tailTrace_2793607
  have hstable : (prefixWord ++ tailWord_2793607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793607).length < 2 ^ (prefixWord ++ tailWord_2793607).sum := by decide
  have hdescent : baseEnd_2793607 < baseStart_2793607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793637 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_2793637 : Nat := 118140960795 + 2793637 * 2 ^ 59
def prefixEnd_2793637 : Nat := 4983230072969 + 3 ^ 40 * 2793637 * 2
def baseEnd_2793637 : Nat := 1434478555184591616089803

theorem tailTrace_2793637 : CollatzResearch.WordTrace tailWord_2793637 prefixEnd_2793637 1434478555184591616089803 := by
  unfold tailWord_2793637
  simp only [CollatzResearch.WordTrace]
  refine ⟨101892312180137739059627165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67928208120091826039751443 101892312180137739059627165)
  ·
    refine ⟨38209617067551652147360187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101892312180137739059627165 38209617067551652147360187)
    ·
      refine ⟨57314425601327478221040281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38209617067551652147360187 57314425601327478221040281)
      ·
        refine ⟨42985819200995608665780211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57314425601327478221040281 42985819200995608665780211)
        ·
          refine ⟨64478728801493412998670317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42985819200995608665780211 64478728801493412998670317)
          ·
            refine ⟨24179523300560029874501369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64478728801493412998670317 24179523300560029874501369)
            ·
              refine ⟨18134642475420022405876027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24179523300560029874501369 18134642475420022405876027)
              ·
                refine ⟨27201963713130033608814041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18134642475420022405876027 27201963713130033608814041)
                ·
                  refine ⟨20401472784847525206610531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27201963713130033608814041 20401472784847525206610531)
                  ·
                    refine ⟨30602209177271287809915797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20401472784847525206610531 30602209177271287809915797)
                    ·
                      refine ⟨1434478555184591616089803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30602209177271287809915797 1434478555184591616089803)
                      ·
                        rfl

theorem cell23_2793637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_2793637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793637 prefixEnd_2793637 := by exact prefixLift 2793637
  have htrace : WordTrace (prefixWord ++ tailWord_2793637) baseStart_2793637 baseEnd_2793637 := by
    simpa [prefixWord, tailWord_2793637, baseEnd_2793637] using wordTrace_append hprefix tailTrace_2793637
  have hstable : (prefixWord ++ tailWord_2793637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793637).length < 2 ^ (prefixWord ++ tailWord_2793637).sum := by decide
  have hdescent : baseEnd_2793637 < baseStart_2793637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793642 : List Nat := [3, 1, 5, 1, 3, 1, 2, 2, 5]
def baseStart_2793642 : Nat := 118140960795 + 2793642 * 2 ^ 59
def prefixEnd_2793642 : Nat := 4983230072969 + 3 ^ 40 * 2793642 * 2
def baseEnd_2793642 : Nat := 159386791398651566280809

theorem tailTrace_2793642 : CollatzResearch.WordTrace tailWord_2793642 prefixEnd_2793642 159386791398651566280809 := by
  unfold tailWord_2793642
  simp only [CollatzResearch.WordTrace]
  refine ⟨25473123636279906228389795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67928329696746416609039453 25473123636279906228389795)
  ·
    refine ⟨38209685454419859342584693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25473123636279906228389795 38209685454419859342584693)
    ·
      refine ⟨3582158011351861813367315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38209685454419859342584693 3582158011351861813367315)
      ·
        refine ⟨5373237017027792720050973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582158011351861813367315 5373237017027792720050973)
        ·
          refine ⟨2014963881385422270019115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5373237017027792720050973 2014963881385422270019115)
          ·
            refine ⟨3022445822078133405028673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014963881385422270019115 3022445822078133405028673)
            ·
              refine ⟨2266834366558600053771505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022445822078133405028673 2266834366558600053771505)
              ·
                refine ⟨1700125774918950040328629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2266834366558600053771505 1700125774918950040328629)
                ·
                  refine ⟨159386791398651566280809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1700125774918950040328629 159386791398651566280809)
                  ·
                    rfl

theorem cell23_2793642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_2793642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793642 prefixEnd_2793642 := by exact prefixLift 2793642
  have htrace : WordTrace (prefixWord ++ tailWord_2793642) baseStart_2793642 baseEnd_2793642 := by
    simpa [prefixWord, tailWord_2793642, baseEnd_2793642] using wordTrace_append hprefix tailTrace_2793642
  have hstable : (prefixWord ++ tailWord_2793642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793642).length < 2 ^ (prefixWord ++ tailWord_2793642).sum := by decide
  have hdescent : baseEnd_2793642 < baseStart_2793642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793664 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 6]
def baseStart_2793664 : Nat := 118140960795 + 2793664 * 2 ^ 59
def prefixEnd_2793664 : Nat := 4983230072969 + 3 ^ 40 * 2793664 * 2
def baseEnd_2793664 : Nat := 159388046573584778939131

theorem tailTrace_2793664 : CollatzResearch.WordTrace tailWord_2793664 prefixEnd_2793664 159388046573584778939131 := by
  unfold tailWord_2793664
  simp only [CollatzResearch.WordTrace]
  refine ⟨50946648475519961335430023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67928864634026615113906697 50946648475519961335430023)
  ·
    refine ⟨76419972713279942003145035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50946648475519961335430023 76419972713279942003145035)
    ·
      refine ⟨114629959069919913004717553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76419972713279942003145035 114629959069919913004717553)
      ·
        refine ⟨85972469302439934753538165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114629959069919913004717553 85972469302439934753538165)
        ·
          refine ⟨8059918997103743883144203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85972469302439934753538165 8059918997103743883144203)
          ·
            refine ⟨12089878495655615824716305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8059918997103743883144203 12089878495655615824716305)
            ·
              refine ⟨9067408871741711868537229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12089878495655615824716305 9067408871741711868537229)
              ·
                refine ⟨3400278326903141950701461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9067408871741711868537229 3400278326903141950701461)
                ·
                  refine ⟨159388046573584778939131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3400278326903141950701461 159388046573584778939131)
                  ·
                    rfl

theorem cell23_2793664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 6].length) (baseStart_2793664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793664 prefixEnd_2793664 := by exact prefixLift 2793664
  have htrace : WordTrace (prefixWord ++ tailWord_2793664) baseStart_2793664 baseEnd_2793664 := by
    simpa [prefixWord, tailWord_2793664, baseEnd_2793664] using wordTrace_append hprefix tailTrace_2793664
  have hstable : (prefixWord ++ tailWord_2793664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793664).length < 2 ^ (prefixWord ++ tailWord_2793664).sum := by decide
  have hdescent : baseEnd_2793664 < baseStart_2793664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793678 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_2793678 : Nat := 118140960795 + 2793678 * 2 ^ 59
def prefixEnd_2793678 : Nat := 4983230072969 + 3 ^ 40 * 2793678 * 2
def baseEnd_2793678 : Nat := 1434499607891425955677115

theorem tailTrace_2793678 : CollatzResearch.WordTrace tailWord_2793678 prefixEnd_2793678 1434499607891425955677115 := by
  unfold tailWord_2793678
  simp only [CollatzResearch.WordTrace]
  refine ⟨12736725946623650382733711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67929205048659468707913125 12736725946623650382733711)
  ·
    refine ⟨19105088919935475574100567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12736725946623650382733711 19105088919935475574100567)
    ·
      refine ⟨28657633379903213361150851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19105088919935475574100567 28657633379903213361150851)
      ·
        refine ⟨42986450069854820041726277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28657633379903213361150851 42986450069854820041726277)
        ·
          refine ⟨8059959388097778757823677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42986450069854820041726277 8059959388097778757823677)
          ·
            refine ⟨3022484770536667034183879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8059959388097778757823677 3022484770536667034183879)
            ·
              refine ⟨4533727155805000551275819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022484770536667034183879 4533727155805000551275819)
              ·
                refine ⟨6800590733707500826913729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4533727155805000551275819 6800590733707500826913729)
                ·
                  refine ⟨5100443050280625620185297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6800590733707500826913729 5100443050280625620185297)
                  ·
                    refine ⟨3825332287710469215138973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5100443050280625620185297 3825332287710469215138973)
                    ·
                      refine ⟨1434499607891425955677115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3825332287710469215138973 1434499607891425955677115)
                      ·
                        rfl

theorem cell23_2793678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_2793678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793678 prefixEnd_2793678 := by exact prefixLift 2793678
  have htrace : WordTrace (prefixWord ++ tailWord_2793678) baseStart_2793678 baseEnd_2793678 := by
    simpa [prefixWord, tailWord_2793678, baseEnd_2793678] using wordTrace_append hprefix tailTrace_2793678
  have hstable : (prefixWord ++ tailWord_2793678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793678).length < 2 ^ (prefixWord ++ tailWord_2793678).sum := by decide
  have hdescent : baseEnd_2793678 < baseStart_2793678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793685 : List Nat := [1, 3, 2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_2793685 : Nat := 118140960795 + 2793685 * 2 ^ 59
def prefixEnd_2793685 : Nat := 4983230072969 + 3 ^ 40 * 2793685 * 2
def baseEnd_2793685 : Nat := 478167734085335809429861

theorem tailTrace_2793685 : CollatzResearch.WordTrace tailWord_2793685 prefixEnd_2793685 478167734085335809429861 := by
  unfold tailWord_2793685
  simp only [CollatzResearch.WordTrace]
  refine ⟨101894062883963843257374509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67929375255975895504916339 101894062883963843257374509)
  ·
    refine ⟨38210273581486441221515441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101894062883963843257374509 38210273581486441221515441)
    ·
      refine ⟨28657705186114830916136581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38210273581486441221515441 28657705186114830916136581)
      ·
        refine ⟨5373319722396530796775609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28657705186114830916136581 5373319722396530796775609)
        ·
          refine ⟨4029989791797398097581707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5373319722396530796775609 4029989791797398097581707)
          ·
            refine ⟨6044984687696097146372561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029989791797398097581707 6044984687696097146372561)
            ·
              refine ⟨4533738515772072859779421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6044984687696097146372561 4533738515772072859779421)
              ·
                refine ⟨1700151943414527322417283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4533738515772072859779421 1700151943414527322417283)
                ·
                  refine ⟨2550227915121790983625925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700151943414527322417283 2550227915121790983625925)
                  ·
                    refine ⟨478167734085335809429861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2550227915121790983625925 478167734085335809429861)
                    ·
                      rfl

theorem cell23_2793685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_2793685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793685 prefixEnd_2793685 := by exact prefixLift 2793685
  have htrace : WordTrace (prefixWord ++ tailWord_2793685) baseStart_2793685 baseEnd_2793685 := by
    simpa [prefixWord, tailWord_2793685, baseEnd_2793685] using wordTrace_append hprefix tailTrace_2793685
  have hstable : (prefixWord ++ tailWord_2793685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793685).length < 2 ^ (prefixWord ++ tailWord_2793685).sum := by decide
  have hdescent : baseEnd_2793685 < baseStart_2793685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793687 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_2793687 : Nat := 118140960795 + 2793687 * 2 ^ 59
def prefixEnd_2793687 : Nat := 4983230072969 + 3 ^ 40 * 2793687 * 2
def baseEnd_2793687 : Nat := 1434504229217316420464573

theorem tailTrace_2793687 : CollatzResearch.WordTrace tailWord_2793687 prefixEnd_2793687 1434504229217316420464573 := by
  unfold tailWord_2793687
  simp only [CollatzResearch.WordTrace]
  refine ⟨101894135829956597598947315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67929423886637731732631543 101894135829956597598947315)
  ·
    refine ⟨152841203744934896398420973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101894135829956597598947315 152841203744934896398420973)
    ·
      refine ⟨57315451404350586149407865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152841203744934896398420973 57315451404350586149407865)
      ·
        refine ⟨42986588553262939612055899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57315451404350586149407865 42986588553262939612055899)
        ·
          refine ⟨64479882829894409418083849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42986588553262939612055899 64479882829894409418083849)
          ·
            refine ⟨48359912122420807063562887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64479882829894409418083849 48359912122420807063562887)
            ·
              refine ⟨72539868183631210595344331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48359912122420807063562887 72539868183631210595344331)
              ·
                refine ⟨108809802275446815893016497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72539868183631210595344331 108809802275446815893016497)
                ·
                  refine ⟨81607351706585111919762373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108809802275446815893016497 81607351706585111919762373)
                  ·
                    refine ⟨15301378444984708484955445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81607351706585111919762373 15301378444984708484955445)
                    ·
                      refine ⟨1434504229217316420464573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15301378444984708484955445 1434504229217316420464573)
                      ·
                        rfl

theorem cell23_2793687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_2793687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793687 prefixEnd_2793687 := by exact prefixLift 2793687
  have htrace : WordTrace (prefixWord ++ tailWord_2793687) baseStart_2793687 baseEnd_2793687 := by
    simpa [prefixWord, tailWord_2793687, baseEnd_2793687] using wordTrace_append hprefix tailTrace_2793687
  have hstable : (prefixWord ++ tailWord_2793687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793687).length < 2 ^ (prefixWord ++ tailWord_2793687).sum := by decide
  have hdescent : baseEnd_2793687 < baseStart_2793687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793708 : List Nat := [2, 2, 1, 1, 2, 3, 1, 6, 1, 1, 3]
def baseStart_2793708 : Nat := 118140960795 + 2793708 * 2 ^ 59
def prefixEnd_2793708 : Nat := 4983230072969 + 3 ^ 40 * 2793708 * 2
def baseEnd_2793708 : Nat := 1434515012311060838301977

theorem tailTrace_2793708 : CollatzResearch.WordTrace tailWord_2793708 prefixEnd_2793708 1434515012311060838301977 := by
  unfold tailWord_2793708
  simp only [CollatzResearch.WordTrace]
  refine ⟨50947450881440259092730889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67929934508587012123641185 50947450881440259092730889)
  ·
    refine ⟨38210588161080194319548167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50947450881440259092730889 38210588161080194319548167)
    ·
      refine ⟨57315882241620291479322251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38210588161080194319548167 57315882241620291479322251)
      ·
        refine ⟨85973823362430437218983377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57315882241620291479322251 85973823362430437218983377)
        ·
          refine ⟨64480367521822827914237533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85973823362430437218983377 64480367521822827914237533)
          ·
            refine ⟨24180137820683560467839075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64480367521822827914237533 24180137820683560467839075)
            ·
              refine ⟨36270206731025340701758613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24180137820683560467839075 36270206731025340701758613)
              ·
                refine ⟨1700165940516812845394935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36270206731025340701758613 1700165940516812845394935)
                ·
                  refine ⟨2550248910775219268092403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700165940516812845394935 2550248910775219268092403)
                  ·
                    refine ⟨3825373366162828902138605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2550248910775219268092403 3825373366162828902138605)
                    ·
                      refine ⟨1434515012311060838301977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3825373366162828902138605 1434515012311060838301977)
                      ·
                        rfl

theorem cell23_2793708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 1, 3].length) (baseStart_2793708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793708 prefixEnd_2793708 := by exact prefixLift 2793708
  have htrace : WordTrace (prefixWord ++ tailWord_2793708) baseStart_2793708 baseEnd_2793708 := by
    simpa [prefixWord, tailWord_2793708, baseEnd_2793708] using wordTrace_append hprefix tailTrace_2793708
  have hstable : (prefixWord ++ tailWord_2793708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793708).length < 2 ^ (prefixWord ++ tailWord_2793708).sum := by decide
  have hdescent : baseEnd_2793708 < baseStart_2793708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793731 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 4]
def baseStart_2793731 : Nat := 118140960795 + 2793731 * 2 ^ 59
def prefixEnd_2793731 : Nat := 4983230072969 + 3 ^ 40 * 2793731 * 2
def baseEnd_2793731 : Nat := 1434526822366114248314371

theorem tailTrace_2793731 : CollatzResearch.WordTrace tailWord_2793731 prefixEnd_2793731 1434526822366114248314371 := by
  unfold tailWord_2793731
  simp only [CollatzResearch.WordTrace]
  refine ⟨101895740641797193113549047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67930493761198128742366031 101895740641797193113549047)
  ·
    refine ⟨152843610962695789670323571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101895740641797193113549047 152843610962695789670323571)
    ·
      refine ⟨229265416444043684505485357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152843610962695789670323571 229265416444043684505485357)
      ·
        refine ⟨85974531166516381689557009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229265416444043684505485357 85974531166516381689557009)
        ·
          refine ⟨64480898374887286267167757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85974531166516381689557009 64480898374887286267167757)
          ·
            refine ⟨24180336890582732350187909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64480898374887286267167757 24180336890582732350187909)
            ·
              refine ⟨4533813166984262315660233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24180336890582732350187909 4533813166984262315660233)
              ·
                refine ⟨3400359875238196736745175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4533813166984262315660233 3400359875238196736745175)
                ·
                  refine ⟨5100539812857295105117763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400359875238196736745175 5100539812857295105117763)
                  ·
                    refine ⟨7650809719285942657676645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5100539812857295105117763 7650809719285942657676645)
                    ·
                      refine ⟨1434526822366114248314371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7650809719285942657676645 1434526822366114248314371)
                      ·
                        rfl

theorem cell23_2793731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_2793731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793731 prefixEnd_2793731 := by exact prefixLift 2793731
  have htrace : WordTrace (prefixWord ++ tailWord_2793731) baseStart_2793731 baseEnd_2793731 := by
    simpa [prefixWord, tailWord_2793731, baseEnd_2793731] using wordTrace_append hprefix tailTrace_2793731
  have hstable : (prefixWord ++ tailWord_2793731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793731).length < 2 ^ (prefixWord ++ tailWord_2793731).sum := by decide
  have hdescent : baseEnd_2793731 < baseStart_2793731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793751 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2793751 : Nat := 118140960795 + 2793751 * 2 ^ 59
def prefixEnd_2793751 : Nat := 4983230072969 + 3 ^ 40 * 2793751 * 2
def baseEnd_2793751 : Nat := 1434537091979204170064279

theorem tailTrace_2793751 : CollatzResearch.WordTrace tailWord_2793751 prefixEnd_2793751 1434537091979204170064279 := by
  unfold tailWord_2793751
  simp only [CollatzResearch.WordTrace]
  refine ⟨101896470101724736529277107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67930980067816491019518071 101896470101724736529277107)
  ·
    refine ⟨152844705152587104793915661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101896470101724736529277107 152844705152587104793915661)
    ·
      refine ⟨57316764432220164297718373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152844705152587104793915661 57316764432220164297718373)
      ·
        refine ⟨10746893331041280805822195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57316764432220164297718373 10746893331041280805822195)
        ·
          refine ⟨16120339996561921208733293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10746893331041280805822195 16120339996561921208733293)
          ·
            refine ⟨6045127498710720453274985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16120339996561921208733293 6045127498710720453274985)
            ·
              refine ⟨4533845624033040339956239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6045127498710720453274985 4533845624033040339956239)
              ·
                refine ⟨6800768436049560509934359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4533845624033040339956239 6800768436049560509934359)
                ·
                  refine ⟨10201152654074340764901539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6800768436049560509934359 10201152654074340764901539)
                  ·
                    refine ⟨15301728981111511147352309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10201152654074340764901539 15301728981111511147352309)
                    ·
                      refine ⟨1434537091979204170064279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15301728981111511147352309 1434537091979204170064279)
                      ·
                        rfl

theorem cell23_2793751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2793751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793751 prefixEnd_2793751 := by exact prefixLift 2793751
  have htrace : WordTrace (prefixWord ++ tailWord_2793751) baseStart_2793751 baseEnd_2793751 := by
    simpa [prefixWord, tailWord_2793751, baseEnd_2793751] using wordTrace_append hprefix tailTrace_2793751
  have hstable : (prefixWord ++ tailWord_2793751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793751).length < 2 ^ (prefixWord ++ tailWord_2793751).sum := by decide
  have hdescent : baseEnd_2793751 < baseStart_2793751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793781 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_2793781 : Nat := 118140960795 + 2793781 * 2 ^ 59
def prefixEnd_2793781 : Nat := 4983230072969 + 3 ^ 40 * 2793781 * 2
def baseEnd_2793781 : Nat := 1434552496398839052689141

theorem tailTrace_2793781 : CollatzResearch.WordTrace tailWord_2793781 prefixEnd_2793781 1434552496398839052689141 := by
  unfold tailWord_2793781
  simp only [CollatzResearch.WordTrace]
  refine ⟨101897564291616051652869197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67931709527744034435246131 101897564291616051652869197)
  ·
    refine ⟨38211586609356019369825949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101897564291616051652869197 38211586609356019369825949)
    ·
      refine ⟨14329344978508507263684731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38211586609356019369825949 14329344978508507263684731)
      ·
        refine ⟨21494017467762760895527097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14329344978508507263684731 21494017467762760895527097)
        ·
          refine ⟨16120513100822070671645323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21494017467762760895527097 16120513100822070671645323)
          ·
            refine ⟨24180769651233106007467985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16120513100822070671645323 24180769651233106007467985)
            ·
              refine ⟨18135577238424829505600989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24180769651233106007467985 18135577238424829505600989)
              ·
                refine ⟨6800841464409311064600371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18135577238424829505600989 6800841464409311064600371)
                ·
                  refine ⟨10201262196613966596900557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6800841464409311064600371 10201262196613966596900557)
                  ·
                    refine ⟨3825473323730237473837709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10201262196613966596900557 3825473323730237473837709)
                    ·
                      refine ⟨1434552496398839052689141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3825473323730237473837709 1434552496398839052689141)
                      ·
                        rfl

theorem cell23_2793781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_2793781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793781 prefixEnd_2793781 := by exact prefixLift 2793781
  have htrace : WordTrace (prefixWord ++ tailWord_2793781) baseStart_2793781 baseEnd_2793781 := by
    simpa [prefixWord, tailWord_2793781, baseEnd_2793781] using wordTrace_append hprefix tailTrace_2793781
  have hstable : (prefixWord ++ tailWord_2793781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793781).length < 2 ^ (prefixWord ++ tailWord_2793781).sum := by decide
  have hdescent : baseEnd_2793781 < baseStart_2793781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793785 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2793785 : Nat := 118140960795 + 2793785 * 2 ^ 59
def prefixEnd_2793785 : Nat := 4983230072969 + 3 ^ 40 * 2793785 * 2
def baseEnd_2793785 : Nat := 1434554550321457037039123

theorem tailTrace_2793785 : CollatzResearch.WordTrace tailWord_2793785 prefixEnd_2793785 1434554550321457037039123 := by
  unfold tailWord_2793785
  simp only [CollatzResearch.WordTrace]
  refine ⟨101897710183601560336014809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67931806789067706890676539 101897710183601560336014809)
  ·
    refine ⟨76423282637701170252011107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101897710183601560336014809 76423282637701170252011107)
    ·
      refine ⟨114634923956551755378016661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76423282637701170252011107 114634923956551755378016661)
      ·
        refine ⟨5373512060463363533344531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114634923956551755378016661 5373512060463363533344531)
        ·
          refine ⟨8060268090695045300016797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5373512060463363533344531 8060268090695045300016797)
          ·
            refine ⟨3022600534010641987506299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8060268090695045300016797 3022600534010641987506299)
            ·
              refine ⟨4533900801015962981259449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022600534010641987506299 4533900801015962981259449)
              ·
                refine ⟨3400425600761972235944587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4533900801015962981259449 3400425600761972235944587)
                ·
                  refine ⟨5100638401142958353916881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400425600761972235944587 5100638401142958353916881)
                  ·
                    refine ⟨3825478800857218765437661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5100638401142958353916881 3825478800857218765437661)
                    ·
                      refine ⟨1434554550321457037039123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3825478800857218765437661 1434554550321457037039123)
                      ·
                        rfl

theorem cell23_2793785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2793785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793785 prefixEnd_2793785 := by exact prefixLift 2793785
  have htrace : WordTrace (prefixWord ++ tailWord_2793785) baseStart_2793785 baseEnd_2793785 := by
    simpa [prefixWord, tailWord_2793785, baseEnd_2793785] using wordTrace_append hprefix tailTrace_2793785
  have hstable : (prefixWord ++ tailWord_2793785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793785).length < 2 ^ (prefixWord ++ tailWord_2793785).sum := by decide
  have hdescent : baseEnd_2793785 < baseStart_2793785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793831 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 2, 6]
def baseStart_2793831 : Nat := 118140960795 + 2793831 * 2 ^ 59
def prefixEnd_2793831 : Nat := 4983230072969 + 3 ^ 40 * 2793831 * 2
def baseEnd_2793831 : Nat := 478192723477187952354637

theorem tailTrace_2793831 : CollatzResearch.WordTrace tailWord_2793831 prefixEnd_2793831 478192723477187952354637 := by
  unfold tailWord_2793831
  simp only [CollatzResearch.WordTrace]
  refine ⟨101899387941434910192189347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67932925294289940128126231 101899387941434910192189347)
  ·
    refine ⟨152849081912152365288284021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101899387941434910192189347 152849081912152365288284021)
    ·
      refine ⟨14329601429264284245776627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152849081912152365288284021 14329601429264284245776627)
      ·
        refine ⟨21494402143896426368664941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14329601429264284245776627 21494402143896426368664941)
        ·
          refine ⟨8060400803961159888249353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21494402143896426368664941 8060400803961159888249353)
          ·
            refine ⟨6045300602970869916187015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8060400803961159888249353 6045300602970869916187015)
            ·
              refine ⟨9067950904456304874280523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045300602970869916187015 9067950904456304874280523)
              ·
                refine ⟨13601926356684457311420785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9067950904456304874280523 13601926356684457311420785)
                ·
                  refine ⟨10201444767513342983565589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13601926356684457311420785 10201444767513342983565589)
                  ·
                    refine ⟨478192723477187952354637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10201444767513342983565589 478192723477187952354637)
                    ·
                      rfl

theorem cell23_2793831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_2793831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793831 prefixEnd_2793831 := by exact prefixLift 2793831
  have htrace : WordTrace (prefixWord ++ tailWord_2793831) baseStart_2793831 baseEnd_2793831 := by
    simpa [prefixWord, tailWord_2793831, baseEnd_2793831] using wordTrace_append hprefix tailTrace_2793831
  have hstable : (prefixWord ++ tailWord_2793831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793831).length < 2 ^ (prefixWord ++ tailWord_2793831).sum := by decide
  have hdescent : baseEnd_2793831 < baseStart_2793831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793859 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 1, 3, 2]
def baseStart_2793859 : Nat := 118140960795 + 2793859 * 2 ^ 59
def prefixEnd_2793859 : Nat := 4983230072969 + 3 ^ 40 * 2793859 * 2
def baseEnd_2793859 : Nat := 1434592547889889747513783

theorem tailTrace_2793859 : CollatzResearch.WordTrace tailWord_2793859 prefixEnd_2793859 1434592547889889747513783 := by
  unfold tailWord_2793859
  simp only [CollatzResearch.WordTrace]
  refine ⟨101900409185333470974208631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67933606123555647316139087 101900409185333470974208631)
  ·
    refine ⟨152850613778000206461312947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101900409185333470974208631 152850613778000206461312947)
    ·
      refine ⟨229275920667000309691969421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152850613778000206461312947 229275920667000309691969421)
      ·
        refine ⟨85978470250125116134488533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229275920667000309691969421 85978470250125116134488533)
        ·
          refine ⟨2015120396487307409402075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 85978470250125116134488533 2015120396487307409402075)
          ·
            refine ⟨3022680594730961114103113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015120396487307409402075 3022680594730961114103113)
            ·
              refine ⟨2267010446048220835577335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022680594730961114103113 2267010446048220835577335)
              ·
                refine ⟨3400515669072331253366003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267010446048220835577335 3400515669072331253366003)
                ·
                  refine ⟨5100773503608496880049005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400515669072331253366003 5100773503608496880049005)
                  ·
                    refine ⟨1912790063853186330018377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5100773503608496880049005 1912790063853186330018377)
                    ·
                      refine ⟨1434592547889889747513783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912790063853186330018377 1434592547889889747513783)
                      ·
                        rfl

theorem cell23_2793859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_2793859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793859 prefixEnd_2793859 := by exact prefixLift 2793859
  have htrace : WordTrace (prefixWord ++ tailWord_2793859) baseStart_2793859 baseEnd_2793859 := by
    simpa [prefixWord, tailWord_2793859, baseEnd_2793859] using wordTrace_append hprefix tailTrace_2793859
  have hstable : (prefixWord ++ tailWord_2793859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793859).length < 2 ^ (prefixWord ++ tailWord_2793859).sum := by decide
  have hdescent : baseEnd_2793859 < baseStart_2793859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793889 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2793889 : Nat := 118140960795 + 2793889 * 2 ^ 59
def prefixEnd_2793889 : Nat := 4983230072969 + 3 ^ 40 * 2793889 * 2
def baseEnd_2793889 : Nat := 1434607952309524630138645

theorem tailTrace_2793889 : CollatzResearch.WordTrace tailWord_2793889 prefixEnd_2793889 1434607952309524630138645 := by
  unfold tailWord_2793889
  simp only [CollatzResearch.WordTrace]
  refine ⟨101901503375224786097800721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67934335583483190731867147 101901503375224786097800721)
  ·
    refine ⟨76426127531418589573350541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101901503375224786097800721 76426127531418589573350541)
    ·
      refine ⟨28659797824281971090006453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76426127531418589573350541 28659797824281971090006453)
      ·
        refine ⟨2686856046026434789688105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28659797824281971090006453 2686856046026434789688105)
        ·
          refine ⟨2015142034519826092266079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2686856046026434789688105 2015142034519826092266079)
          ·
            refine ⟨3022713051779739138399119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015142034519826092266079 3022713051779739138399119)
            ·
              refine ⟨4534069577669608707598679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022713051779739138399119 4534069577669608707598679)
              ·
                refine ⟨6801104366504413061398019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4534069577669608707598679 6801104366504413061398019)
                ·
                  refine ⟨10201656549756619592097029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6801104366504413061398019 10201656549756619592097029)
                  ·
                    refine ⟨1912810603079366173518193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10201656549756619592097029 1912810603079366173518193)
                    ·
                      refine ⟨1434607952309524630138645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912810603079366173518193 1434607952309524630138645)
                      ·
                        rfl

theorem cell23_2793889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2793889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793889 prefixEnd_2793889 := by exact prefixLift 2793889
  have htrace : WordTrace (prefixWord ++ tailWord_2793889) baseStart_2793889 baseEnd_2793889 := by
    simpa [prefixWord, tailWord_2793889, baseEnd_2793889] using wordTrace_append hprefix tailTrace_2793889
  have hstable : (prefixWord ++ tailWord_2793889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793889).length < 2 ^ (prefixWord ++ tailWord_2793889).sum := by decide
  have hdescent : baseEnd_2793889 < baseStart_2793889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793911 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_2793911 : Nat := 118140960795 + 2793911 * 2 ^ 59
def prefixEnd_2793911 : Nat := 4983230072969 + 3 ^ 40 * 2793911 * 2
def baseEnd_2793911 : Nat := 1434619248883923544063543

theorem tailTrace_2793911 : CollatzResearch.WordTrace tailWord_2793911 prefixEnd_2793911 1434619248883923544063543 := by
  unfold tailWord_2793911
  simp only [CollatzResearch.WordTrace]
  refine ⟨101902305781145083855101587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67934870520763389236734391 101902305781145083855101587)
  ·
    refine ⟨152853458671717625782652381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101902305781145083855101587 152853458671717625782652381)
    ·
      refine ⟨57320047001894109668494643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152853458671717625782652381 57320047001894109668494643)
      ·
        refine ⟨85980070502841164502741965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57320047001894109668494643 85980070502841164502741965)
        ·
          refine ⟨32242526438565436688528237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85980070502841164502741965 32242526438565436688528237)
          ·
            refine ⟨12090947414462038758198089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32242526438565436688528237 12090947414462038758198089)
            ·
              refine ⟨9068210560846529068648567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12090947414462038758198089 9068210560846529068648567)
              ·
                refine ⟨13602315841269793602972851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9068210560846529068648567 13602315841269793602972851)
                ·
                  refine ⟨20403473761904690404459277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13602315841269793602972851 20403473761904690404459277)
                  ·
                    refine ⟨7651302660714258901672229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20403473761904690404459277 7651302660714258901672229)
                    ·
                      refine ⟨1434619248883923544063543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7651302660714258901672229 1434619248883923544063543)
                      ·
                        rfl

theorem cell23_2793911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_2793911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793911 prefixEnd_2793911 := by exact prefixLift 2793911
  have htrace : WordTrace (prefixWord ++ tailWord_2793911) baseStart_2793911 baseEnd_2793911 := by
    simpa [prefixWord, tailWord_2793911, baseEnd_2793911] using wordTrace_append hprefix tailTrace_2793911
  have hstable : (prefixWord ++ tailWord_2793911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793911).length < 2 ^ (prefixWord ++ tailWord_2793911).sum := by decide
  have hdescent : baseEnd_2793911 < baseStart_2793911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793928 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_2793928 : Nat := 118140960795 + 2793928 * 2 ^ 59
def prefixEnd_2793928 : Nat := 4983230072969 + 3 ^ 40 * 2793928 * 2
def baseEnd_2793928 : Nat := 1434627978055049977550965

theorem tailTrace_2793928 : CollatzResearch.WordTrace tailWord_2793928 prefixEnd_2793928 1434627978055049977550965 := by
  unfold tailWord_2793928
  simp only [CollatzResearch.WordTrace]
  refine ⟨50951462911041747879235219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67935283881388997172313625 50951462911041747879235219)
  ·
    refine ⟨76427194366562621818852829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50951462911041747879235219 76427194366562621818852829)
    ·
      refine ⟨28660197887460983182069811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76427194366562621818852829 28660197887460983182069811)
      ·
        refine ⟨42990296831191474773104717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28660197887460983182069811 42990296831191474773104717)
        ·
          refine ⟨16121361311696803039914269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42990296831191474773104717 16121361311696803039914269)
          ·
            refine ⟨6045510491886301139967851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16121361311696803039914269 6045510491886301139967851)
            ·
              refine ⟨9068265737829451709951777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045510491886301139967851 9068265737829451709951777)
              ·
                refine ⟨6801199303372088782463833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9068265737829451709951777 6801199303372088782463833)
                ·
                  refine ⟨5100899477529066586847875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6801199303372088782463833 5100899477529066586847875)
                  ·
                    refine ⟨7651349216293599880271813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5100899477529066586847875 7651349216293599880271813)
                    ·
                      refine ⟨1434627978055049977550965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7651349216293599880271813 1434627978055049977550965)
                      ·
                        rfl

theorem cell23_2793928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_2793928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793928 prefixEnd_2793928 := by exact prefixLift 2793928
  have htrace : WordTrace (prefixWord ++ tailWord_2793928) baseStart_2793928 baseEnd_2793928 := by
    simpa [prefixWord, tailWord_2793928, baseEnd_2793928] using wordTrace_append hprefix tailTrace_2793928
  have hstable : (prefixWord ++ tailWord_2793928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793928).length < 2 ^ (prefixWord ++ tailWord_2793928).sum := by decide
  have hdescent : baseEnd_2793928 < baseStart_2793928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793965 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2793965 : Nat := 118140960795 + 2793965 * 2 ^ 59
def prefixEnd_2793965 : Nat := 4983230072969 + 3 ^ 40 * 2793965 * 2
def baseEnd_2793965 : Nat := 1434646976839266332788295

theorem tailTrace_2793965 : CollatzResearch.WordTrace tailWord_2793965 prefixEnd_2793965 1434646976839266332788295 := by
  unfold tailWord_2793965
  simp only [CollatzResearch.WordTrace]
  refine ⟨101904275322949451077567349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67936183548632967385044899 101904275322949451077567349)
  ·
    refine ⟨9553525811526511038521939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101904275322949451077567349 9553525811526511038521939)
    ·
      refine ⟨14330288717289766557782909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9553525811526511038521939 14330288717289766557782909)
      ·
        refine ⟨5373858268983662459168591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14330288717289766557782909 5373858268983662459168591)
        ·
          refine ⟨8060787403475493688752887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5373858268983662459168591 8060787403475493688752887)
          ·
            refine ⟨12091181105213240533129331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8060787403475493688752887 12091181105213240533129331)
            ·
              refine ⟨18136771657819860799693997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12091181105213240533129331 18136771657819860799693997)
              ·
                refine ⟨6801289371682447799885249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18136771657819860799693997 6801289371682447799885249)
                ·
                  refine ⟨5100967028761835849913937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6801289371682447799885249 5100967028761835849913937)
                  ·
                    refine ⟨3825725271571376887435453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5100967028761835849913937 3825725271571376887435453)
                    ·
                      refine ⟨1434646976839266332788295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3825725271571376887435453 1434646976839266332788295)
                      ·
                        rfl

theorem cell23_2793965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2793965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793965 prefixEnd_2793965 := by exact prefixLift 2793965
  have htrace : WordTrace (prefixWord ++ tailWord_2793965) baseStart_2793965 baseEnd_2793965 := by
    simpa [prefixWord, tailWord_2793965, baseEnd_2793965] using wordTrace_append hprefix tailTrace_2793965
  have hstable : (prefixWord ++ tailWord_2793965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793965).length < 2 ^ (prefixWord ++ tailWord_2793965).sum := by decide
  have hdescent : baseEnd_2793965 < baseStart_2793965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793978 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3]
def baseStart_2793978 : Nat := 118140960795 + 2793978 * 2 ^ 59
def prefixEnd_2793978 : Nat := 4983230072969 + 3 ^ 40 * 2793978 * 2
def baseEnd_2793978 : Nat := 1434653652087774781925735

theorem tailTrace_2793978 : CollatzResearch.WordTrace tailWord_2793978 prefixEnd_2793978 1434653652087774781925735 := by
  unfold tailWord_2793978
  simp only [CollatzResearch.WordTrace]
  refine ⟨25476187367975588574447647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67936499647934902865193725 25476187367975588574447647)
  ·
    refine ⟨38214281051963382861671471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25476187367975588574447647 38214281051963382861671471)
    ·
      refine ⟨57321421577945074292507207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38214281051963382861671471 57321421577945074292507207)
      ·
        refine ⟨85982132366917611438760811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57321421577945074292507207 85982132366917611438760811)
        ·
          refine ⟨128973198550376417158141217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85982132366917611438760811 128973198550376417158141217)
          ·
            refine ⟨96729898912782312868605913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128973198550376417158141217 96729898912782312868605913)
            ·
              refine ⟨72547424184586734651454435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96729898912782312868605913 72547424184586734651454435)
              ·
                refine ⟨108821136276880101977181653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72547424184586734651454435 108821136276880101977181653)
                ·
                  refine ⟨2550495381489377390090195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108821136276880101977181653 2550495381489377390090195)
                  ·
                    refine ⟨3825743072234066085135293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2550495381489377390090195 3825743072234066085135293)
                    ·
                      refine ⟨1434653652087774781925735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3825743072234066085135293 1434653652087774781925735)
                      ·
                        rfl

theorem cell23_2793978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_2793978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793978 prefixEnd_2793978 := by exact prefixLift 2793978
  have htrace : WordTrace (prefixWord ++ tailWord_2793978) baseStart_2793978 baseEnd_2793978 := by
    simpa [prefixWord, tailWord_2793978, baseEnd_2793978] using wordTrace_append hprefix tailTrace_2793978
  have hstable : (prefixWord ++ tailWord_2793978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793978).length < 2 ^ (prefixWord ++ tailWord_2793978).sum := by decide
  have hdescent : baseEnd_2793978 < baseStart_2793978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793998 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_2793998 : Nat := 118140960795 + 2793998 * 2 ^ 59
def prefixEnd_2793998 : Nat := 4983230072969 + 3 ^ 40 * 2793998 * 2
def baseEnd_2793998 : Nat := 478221307233621567891881

theorem tailTrace_2793998 : CollatzResearch.WordTrace tailWord_2793998 prefixEnd_2793998 478221307233621567891881 := by
  unfold tailWord_2793998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12738184866478737214189831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67936985954553265142345765 12738184866478737214189831)
  ·
    refine ⟨19107277299718105821284747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12738184866478737214189831 19107277299718105821284747)
    ·
      refine ⟨28660915949577158731927121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19107277299718105821284747 28660915949577158731927121)
      ·
        refine ⟨21495686962182869048945341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28660915949577158731927121 21495686962182869048945341)
        ·
          refine ⟨8060882610818575893354503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21495686962182869048945341 8060882610818575893354503)
          ·
            refine ⟨12091323916227863840031755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8060882610818575893354503 12091323916227863840031755)
            ·
              refine ⟨18136985874341795760047633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12091323916227863840031755 18136985874341795760047633)
              ·
                refine ⟨13602739405756346820035725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18136985874341795760047633 13602739405756346820035725)
                ·
                  refine ⟨5101027277158630057513397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13602739405756346820035725 5101027277158630057513397)
                  ·
                    refine ⟨478221307233621567891881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5101027277158630057513397 478221307233621567891881)
                    ·
                      rfl

theorem cell23_2793998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_2793998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2793998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2793998 prefixEnd_2793998 := by exact prefixLift 2793998
  have htrace : WordTrace (prefixWord ++ tailWord_2793998) baseStart_2793998 baseEnd_2793998 := by
    simpa [prefixWord, tailWord_2793998, baseEnd_2793998] using wordTrace_append hprefix tailTrace_2793998
  have hstable : (prefixWord ++ tailWord_2793998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793998).length < 2 ^ (prefixWord ++ tailWord_2793998).sum := by decide
  have hdescent : baseEnd_2793998 < baseStart_2793998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794035 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 5, 2, 2]
def baseStart_2794035 : Nat := 118140960795 + 2794035 * 2 ^ 59
def prefixEnd_2794035 : Nat := 4983230072969 + 3 ^ 40 * 2794035 * 2
def baseEnd_2794035 : Nat := 1434682920485081058912973

theorem tailTrace_2794035 : CollatzResearch.WordTrace tailWord_2794035 prefixEnd_2794035 1434682920485081058912973 := by
  unfold tailWord_2794035
  simp only [CollatzResearch.WordTrace]
  refine ⟨101906828432695853032615559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67937885621797235355077039 101906828432695853032615559)
  ·
    refine ⟨152860242649043779548923339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101906828432695853032615559 152860242649043779548923339)
    ·
      refine ⟨229290363973565669323385009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152860242649043779548923339 229290363973565669323385009)
      ·
        refine ⟨171967772980174251992538757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229290363973565669323385009 171967772980174251992538757)
        ·
          refine ⟨32243957433782672248601017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171967772980174251992538757 32243957433782672248601017)
          ·
            refine ⟨24182968075337004186450763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32243957433782672248601017 24182968075337004186450763)
            ·
              refine ⟨36274452113005506279676145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24182968075337004186450763 36274452113005506279676145)
              ·
                refine ⟨27205839084754129709757109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36274452113005506279676145 27205839084754129709757109)
                ·
                  refine ⟨2550547414195699660289729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27205839084754129709757109 2550547414195699660289729)
                  ·
                    refine ⟨1912910560646774745217297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2550547414195699660289729 1912910560646774745217297)
                    ·
                      refine ⟨1434682920485081058912973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912910560646774745217297 1434682920485081058912973)
                      ·
                        rfl

theorem cell23_2794035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 2, 2].length) (baseStart_2794035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794035 prefixEnd_2794035 := by exact prefixLift 2794035
  have htrace : WordTrace (prefixWord ++ tailWord_2794035) baseStart_2794035 baseEnd_2794035 := by
    simpa [prefixWord, tailWord_2794035, baseEnd_2794035] using wordTrace_append hprefix tailTrace_2794035
  have hstable : (prefixWord ++ tailWord_2794035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794035).length < 2 ^ (prefixWord ++ tailWord_2794035).sum := by decide
  have hdescent : baseEnd_2794035 < baseStart_2794035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794041 : List Nat := [1, 2, 1, 5, 1, 1, 12]
def baseStart_2794041 : Nat := 118140960795 + 2794041 * 2 ^ 59
def prefixEnd_2794041 : Nat := 4983230072969 + 3 ^ 40 * 2794041 * 2
def baseEnd_2794041 : Nat := 17712172856407506610345

theorem tailTrace_2794041 : CollatzResearch.WordTrace tailWord_2794041 prefixEnd_2794041 17712172856407506610345 := by
  unfold tailWord_2794041
  simp only [CollatzResearch.WordTrace]
  refine ⟨101907047270674116057333977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67938031513782744038222651 101907047270674116057333977)
  ·
    refine ⟨76430285453005587043000483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101907047270674116057333977 76430285453005587043000483)
    ·
      refine ⟨114645428179508380564500725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76430285453005587043000483 114645428179508380564500725)
      ·
        refine ⟨10748008891828910677921943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114645428179508380564500725 10748008891828910677921943)
        ·
          refine ⟨16122013337743366016882915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10748008891828910677921943 16122013337743366016882915)
          ·
            refine ⟨24183020006615049025324373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16122013337743366016882915 24183020006615049025324373)
            ·
              refine ⟨17712172856407506610345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 24183020006615049025324373 17712172856407506610345)
              ·
                rfl

theorem cell23_2794041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 12].length) (baseStart_2794041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794041 prefixEnd_2794041 := by exact prefixLift 2794041
  have htrace : WordTrace (prefixWord ++ tailWord_2794041) baseStart_2794041 baseEnd_2794041 := by
    simpa [prefixWord, tailWord_2794041, baseEnd_2794041] using wordTrace_append hprefix tailTrace_2794041
  have hstable : (prefixWord ++ tailWord_2794041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794041).length < 2 ^ (prefixWord ++ tailWord_2794041).sum := by decide
  have hdescent : baseEnd_2794041 < baseStart_2794041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794045 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_2794045 : Nat := 118140960795 + 2794045 * 2 ^ 59
def prefixEnd_2794045 : Nat := 4983230072969 + 3 ^ 40 * 2794045 * 2
def baseEnd_2794045 : Nat := 478229351763875339929309

theorem tailTrace_2794045 : CollatzResearch.WordTrace tailWord_2794045 prefixEnd_2794045 478229351763875339929309 := by
  unfold tailWord_2794045
  simp only [CollatzResearch.WordTrace]
  refine ⟨101907193162659624740479589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67938128775106416493653059 101907193162659624740479589)
  ·
    refine ⟨19107598717998679638839923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101907193162659624740479589 19107598717998679638839923)
    ·
      refine ⟨28661398076998019458259885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19107598717998679638839923 28661398076998019458259885)
      ·
        refine ⟨10748024278874257296847457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28661398076998019458259885 10748024278874257296847457)
        ·
          refine ⟨8061018209155692972635593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10748024278874257296847457 8061018209155692972635593)
          ·
            refine ⟨6045763656866769729476695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8061018209155692972635593 6045763656866769729476695)
            ·
              refine ⟨9068645485300154594215043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045763656866769729476695 9068645485300154594215043)
              ·
                refine ⟨13602968227950231891322565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9068645485300154594215043 13602968227950231891322565)
                ·
                  refine ⟨2550556542740668479622981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13602968227950231891322565 2550556542740668479622981)
                  ·
                    refine ⟨478229351763875339929309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2550556542740668479622981 478229351763875339929309)
                    ·
                      rfl

theorem cell23_2794045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_2794045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794045 prefixEnd_2794045 := by exact prefixLift 2794045
  have htrace : WordTrace (prefixWord ++ tailWord_2794045) baseStart_2794045 baseEnd_2794045 := by
    simpa [prefixWord, tailWord_2794045, baseEnd_2794045] using wordTrace_append hprefix tailTrace_2794045
  have hstable : (prefixWord ++ tailWord_2794045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794045).length < 2 ^ (prefixWord ++ tailWord_2794045).sum := by decide
  have hdescent : baseEnd_2794045 < baseStart_2794045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794065 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 4]
def baseStart_2794065 : Nat := 118140960795 + 2794065 * 2 ^ 59
def prefixEnd_2794065 : Nat := 4983230072969 + 3 ^ 40 * 2794065 * 2
def baseEnd_2794065 : Nat := 1434698324904715941537835

theorem tailTrace_2794065 : CollatzResearch.WordTrace tailWord_2794065 prefixEnd_2794065 1434698324904715941537835 := by
  unfold tailWord_2794065
  simp only [CollatzResearch.WordTrace]
  refine ⟨101907922622587168156207649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67938615081724778770805099 101907922622587168156207649)
  ·
    refine ⟨76430941966940376117155737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101907922622587168156207649 76430941966940376117155737)
    ·
      refine ⟨57323206475205282087866803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76430941966940376117155737 57323206475205282087866803)
      ·
        refine ⟨85984809712807923131800205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57323206475205282087866803 85984809712807923131800205)
        ·
          refine ⟨32244303642302971174425077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85984809712807923131800205 32244303642302971174425077)
          ·
            refine ⟨3022903466465903547602351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32244303642302971174425077 3022903466465903547602351)
            ·
              refine ⟨4534355199698855321403527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022903466465903547602351 4534355199698855321403527)
              ·
                refine ⟨6801532799548282982105291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4534355199698855321403527 6801532799548282982105291)
                ·
                  refine ⟨10202299199322424473157937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6801532799548282982105291 10202299199322424473157937)
                  ·
                    refine ⟨7651724399491818354868453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10202299199322424473157937 7651724399491818354868453)
                    ·
                      refine ⟨1434698324904715941537835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7651724399491818354868453 1434698324904715941537835)
                      ·
                        rfl

theorem cell23_2794065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_2794065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794065 prefixEnd_2794065 := by exact prefixLift 2794065
  have htrace : WordTrace (prefixWord ++ tailWord_2794065) baseStart_2794065 baseEnd_2794065 := by
    simpa [prefixWord, tailWord_2794065, baseEnd_2794065] using wordTrace_append hprefix tailTrace_2794065
  have hstable : (prefixWord ++ tailWord_2794065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794065).length < 2 ^ (prefixWord ++ tailWord_2794065).sum := by decide
  have hdescent : baseEnd_2794065 < baseStart_2794065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794159 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 2, 2, 2]
def baseStart_2794159 : Nat := 118140960795 + 2794159 * 2 ^ 59
def prefixEnd_2794159 : Nat := 4983230072969 + 3 ^ 40 * 2794159 * 2
def baseEnd_2794159 : Nat := 1434746592086238573762403

theorem tailTrace_2794159 : CollatzResearch.WordTrace tailWord_2794159 prefixEnd_2794159 1434746592086238573762403 := by
  unfold tailWord_2794159
  simp only [CollatzResearch.WordTrace]
  refine ⟨101911351084246622210129531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67940900722831081473419687 101911351084246622210129531)
  ·
    refine ⟨152867026626369933315194297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101911351084246622210129531 152867026626369933315194297)
    ·
      refine ⟨114650269969777449986395723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152867026626369933315194297 114650269969777449986395723)
      ·
        refine ⟨171975404954666174979593585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114650269969777449986395723 171975404954666174979593585)
        ·
          refine ⟨128981553715999631234695189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171975404954666174979593585 128981553715999631234695189)
          ·
            refine ⟨6046010330437482714126337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128981553715999631234695189 6046010330437482714126337)
            ·
              refine ⟨4534507747828112035594753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6046010330437482714126337 4534507747828112035594753)
              ·
                refine ⟨3400880810871084026696065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4534507747828112035594753 3400880810871084026696065)
                ·
                  refine ⟨2550660608153313020022049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3400880810871084026696065 2550660608153313020022049)
                  ·
                    refine ⟨1912995456114984765016537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2550660608153313020022049 1912995456114984765016537)
                    ·
                      refine ⟨1434746592086238573762403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1912995456114984765016537 1434746592086238573762403)
                      ·
                        rfl

theorem cell23_2794159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 2, 2].length) (baseStart_2794159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794159 prefixEnd_2794159 := by exact prefixLift 2794159
  have htrace : WordTrace (prefixWord ++ tailWord_2794159) baseStart_2794159 baseEnd_2794159 := by
    simpa [prefixWord, tailWord_2794159, baseEnd_2794159] using wordTrace_append hprefix tailTrace_2794159
  have hstable : (prefixWord ++ tailWord_2794159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794159).length < 2 ^ (prefixWord ++ tailWord_2794159).sum := by decide
  have hdescent : baseEnd_2794159 < baseStart_2794159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794175 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 3]
def baseStart_2794175 : Nat := 118140960795 + 2794175 * 2 ^ 59
def prefixEnd_2794175 : Nat := 4983230072969 + 3 ^ 40 * 2794175 * 2
def baseEnd_2794175 : Nat := 1434754807776710511162329

theorem tailTrace_2794175 : CollatzResearch.WordTrace tailWord_2794175 prefixEnd_2794175 1434754807776710511162329 := by
  unfold tailWord_2794175
  simp only [CollatzResearch.WordTrace]
  refine ⟨101911934652188656942711979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67941289768125771295141319 101911934652188656942711979)
  ·
    refine ⟨152867901978282985414067969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101911934652188656942711979 152867901978282985414067969)
    ·
      refine ⟨114650926483712239060550977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152867901978282985414067969 114650926483712239060550977)
      ·
        refine ⟨85988194862784179295413233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114650926483712239060550977 85988194862784179295413233)
        ·
          refine ⟨64491146147088134471559925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85988194862784179295413233 64491146147088134471559925)
          ·
            refine ⟨6046044951289512606708743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64491146147088134471559925 6046044951289512606708743)
            ·
              refine ⟨9069067426934268910063115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046044951289512606708743 9069067426934268910063115)
              ·
                refine ⟨13603601140401403365094673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9069067426934268910063115 13603601140401403365094673)
                ·
                  refine ⟨10202700855301052523821005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13603601140401403365094673 10202700855301052523821005)
                  ·
                    refine ⟨3826012820737894696432877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10202700855301052523821005 3826012820737894696432877)
                    ·
                      refine ⟨1434754807776710511162329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3826012820737894696432877 1434754807776710511162329)
                      ·
                        rfl

theorem cell23_2794175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_2794175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794175 prefixEnd_2794175 := by exact prefixLift 2794175
  have htrace : WordTrace (prefixWord ++ tailWord_2794175) baseStart_2794175 baseEnd_2794175 := by
    simpa [prefixWord, tailWord_2794175, baseEnd_2794175] using wordTrace_append hprefix tailTrace_2794175
  have hstable : (prefixWord ++ tailWord_2794175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794175).length < 2 ^ (prefixWord ++ tailWord_2794175).sum := by decide
  have hdescent : baseEnd_2794175 < baseStart_2794175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794276 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_2794276 : Nat := 118140960795 + 2794276 * 2 ^ 59
def prefixEnd_2794276 : Nat := 4983230072969 + 3 ^ 40 * 2794276 * 2
def baseEnd_2794276 : Nat := 478268889774271538666455

theorem tailTrace_2794276 : CollatzResearch.WordTrace tailWord_2794276 prefixEnd_2794276 478268889774271538666455 := by
  unfold tailWord_2794276
  simp only [CollatzResearch.WordTrace]
  refine ⟨50957809212411375596069341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67943745616548500794759121 50957809212411375596069341)
  ·
    refine ⟨19109178454654265848526003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50957809212411375596069341 19109178454654265848526003)
    ·
      refine ⟨28663767681981398772789005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19109178454654265848526003 28663767681981398772789005)
      ·
        refine ⟨10748912880743024539795877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28663767681981398772789005 10748912880743024539795877)
        ·
          refine ⟨2015421165139317101211727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10748912880743024539795877 2015421165139317101211727)
          ·
            refine ⟨3023131747708975651817591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015421165139317101211727 3023131747708975651817591)
            ·
              refine ⟨4534697621563463477726387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023131747708975651817591 4534697621563463477726387)
              ·
                refine ⟨6802046432345195216589581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4534697621563463477726387 6802046432345195216589581)
                ·
                  refine ⟨2550767412129448206221093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6802046432345195216589581 2550767412129448206221093)
                  ·
                    refine ⟨478268889774271538666455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2550767412129448206221093 478268889774271538666455)
                    ·
                      rfl

theorem cell23_2794276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_2794276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794276 prefixEnd_2794276 := by exact prefixLift 2794276
  have htrace : WordTrace (prefixWord ++ tailWord_2794276) baseStart_2794276 baseEnd_2794276 := by
    simpa [prefixWord, tailWord_2794276, baseEnd_2794276] using wordTrace_append hprefix tailTrace_2794276
  have hstable : (prefixWord ++ tailWord_2794276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794276).length < 2 ^ (prefixWord ++ tailWord_2794276).sum := by decide
  have hdescent : baseEnd_2794276 < baseStart_2794276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794335 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_2794335 : Nat := 118140960795 + 2794335 * 2 ^ 59
def prefixEnd_2794335 : Nat := 4983230072969 + 3 ^ 40 * 2794335 * 2
def baseEnd_2794335 : Nat := 1434836964681429885161593

theorem tailTrace_2794335 : CollatzResearch.WordTrace tailWord_2794335 prefixEnd_2794335 1434836964681429885161593 := by
  unfold tailWord_2794335
  simp only [CollatzResearch.WordTrace]
  refine ⟨101917770331609004268536459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67945180221072669512357639 101917770331609004268536459)
  ·
    refine ⟨152876655497413506402804689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101917770331609004268536459 152876655497413506402804689)
    ·
      refine ⟨114657491623060129802103517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152876655497413506402804689 114657491623060129802103517)
      ·
        refine ⟨42996559358647548675788819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114657491623060129802103517 42996559358647548675788819)
        ·
          refine ⟨64494839037971323013683229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42996559358647548675788819 64494839037971323013683229)
          ·
            refine ⟨24185564639239246130131211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64494839037971323013683229 24185564639239246130131211)
            ·
              refine ⟨36278346958858869195196817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24185564639239246130131211 36278346958858869195196817)
              ·
                refine ⟨27208760219144151896397613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36278346958858869195196817 27208760219144151896397613)
                ·
                  refine ⟨10203285082179056961149105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27208760219144151896397613 10203285082179056961149105)
                  ·
                    refine ⟨7652463811634292720861829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10203285082179056961149105 7652463811634292720861829)
                    ·
                      refine ⟨1434836964681429885161593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7652463811634292720861829 1434836964681429885161593)
                      ·
                        rfl

theorem cell23_2794335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_2794335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794335 prefixEnd_2794335 := by exact prefixLift 2794335
  have htrace : WordTrace (prefixWord ++ tailWord_2794335) baseStart_2794335 baseEnd_2794335 := by
    simpa [prefixWord, tailWord_2794335, baseEnd_2794335] using wordTrace_append hprefix tailTrace_2794335
  have hstable : (prefixWord ++ tailWord_2794335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794335).length < 2 ^ (prefixWord ++ tailWord_2794335).sum := by decide
  have hdescent : baseEnd_2794335 < baseStart_2794335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794370 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2794370 : Nat := 118140960795 + 2794370 * 2 ^ 59
def prefixEnd_2794370 : Nat := 4983230072969 + 3 ^ 40 * 2794370 * 2
def baseEnd_2794370 : Nat := 478284978834779082741311

theorem tailTrace_2794370 : CollatzResearch.WordTrace tailWord_2794370 prefixEnd_2794370 478284978834779082741311 := by
  unfold tailWord_2794370
  simp only [CollatzResearch.WordTrace]
  refine ⟨25479761721620551311515141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67946031257654803497373709 25479761721620551311515141)
  ·
    refine ⟨4777455322803853370909089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25479761721620551311515141 4777455322803853370909089)
    ·
      refine ⟨3583091492102890028181817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4777455322803853370909089 3583091492102890028181817)
      ·
        refine ⟨2687318619077167521136363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3583091492102890028181817 2687318619077167521136363)
        ·
          refine ⟨4030977928615751281704545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687318619077167521136363 4030977928615751281704545)
          ·
            refine ⟨3023233446461813461278409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4030977928615751281704545 3023233446461813461278409)
            ·
              refine ⟨2267425084846360095958807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3023233446461813461278409 2267425084846360095958807)
              ·
                refine ⟨3401137627269540143938211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267425084846360095958807 3401137627269540143938211)
                ·
                  refine ⟨5101706440904310215907317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3401137627269540143938211 5101706440904310215907317)
                  ·
                    refine ⟨478284978834779082741311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5101706440904310215907317 478284978834779082741311)
                    ·
                      rfl

theorem cell23_2794370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2794370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794370 prefixEnd_2794370 := by exact prefixLift 2794370
  have htrace : WordTrace (prefixWord ++ tailWord_2794370) baseStart_2794370 baseEnd_2794370 := by
    simpa [prefixWord, tailWord_2794370, baseEnd_2794370] using wordTrace_append hprefix tailTrace_2794370
  have hstable : (prefixWord ++ tailWord_2794370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794370).length < 2 ^ (prefixWord ++ tailWord_2794370).sum := by decide
  have hdescent : baseEnd_2794370 < baseStart_2794370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794373 : List Nat := [1, 3, 1, 1, 3, 4, 2, 3, 1, 2, 2]
def baseStart_2794373 : Nat := 118140960795 + 2794373 * 2 ^ 59
def prefixEnd_2794373 : Nat := 4983230072969 + 3 ^ 40 * 2794373 * 2
def baseEnd_2794373 : Nat := 1434856476946300736486419

theorem tailTrace_2794373 : CollatzResearch.WordTrace tailWord_2794373 prefixEnd_2794373 1434856476946300736486419 := by
  unfold tailWord_2794373
  simp only [CollatzResearch.WordTrace]
  refine ⟨101919156305471336758419773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67946104203647557838946515 101919156305471336758419773)
  ·
    refine ⟨38219683614551751284407415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101919156305471336758419773 38219683614551751284407415)
    ·
      refine ⟨57329525421827626926611123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38219683614551751284407415 57329525421827626926611123)
      ·
        refine ⟨85994288132741440389916685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57329525421827626926611123 85994288132741440389916685)
        ·
          refine ⟨32247858049778040146218757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85994288132741440389916685 32247858049778040146218757)
          ·
            refine ⟨6046473384333382527416017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32247858049778040146218757 6046473384333382527416017)
            ·
              refine ⟨4534855038250036895562013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6046473384333382527416017 4534855038250036895562013)
              ·
                refine ⟨1700570639343763835835755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4534855038250036895562013 1700570639343763835835755)
                ·
                  refine ⟨2550855959015645753753633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700570639343763835835755 2550855959015645753753633)
                  ·
                    refine ⟨1913141969261734315315225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2550855959015645753753633 1913141969261734315315225)
                    ·
                      refine ⟨1434856476946300736486419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913141969261734315315225 1434856476946300736486419)
                      ·
                        rfl

theorem cell23_2794373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 2, 2].length) (baseStart_2794373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794373 prefixEnd_2794373 := by exact prefixLift 2794373
  have htrace : WordTrace (prefixWord ++ tailWord_2794373) baseStart_2794373 baseEnd_2794373 := by
    simpa [prefixWord, tailWord_2794373, baseEnd_2794373] using wordTrace_append hprefix tailTrace_2794373
  have hstable : (prefixWord ++ tailWord_2794373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794373).length < 2 ^ (prefixWord ++ tailWord_2794373).sum := by decide
  have hdescent : baseEnd_2794373 < baseStart_2794373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794376 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_2794376 : Nat := 118140960795 + 2794376 * 2 ^ 59
def prefixEnd_2794376 : Nat := 4983230072969 + 3 ^ 40 * 2794376 * 2
def baseEnd_2794376 : Nat := 1434858017388264224748905

theorem tailTrace_2794376 : CollatzResearch.WordTrace tailWord_2794376 prefixEnd_2794376 1434858017388264224748905 := by
  unfold tailWord_2794376
  simp only [CollatzResearch.WordTrace]
  refine ⟨50959632862230234135389491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67946177149640312180519321 50959632862230234135389491)
  ·
    refine ⟨76439449293345351203084237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50959632862230234135389491 76439449293345351203084237)
    ·
      refine ⟨28664793485004506701156589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76439449293345351203084237 28664793485004506701156589)
      ·
        refine ⟨10749297556876690012933721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28664793485004506701156589 10749297556876690012933721)
        ·
          refine ⟨8061973167657517509700291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10749297556876690012933721 8061973167657517509700291)
          ·
            refine ⟨12092959751486276264550437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8061973167657517509700291 12092959751486276264550437)
            ·
              refine ⟨2267429953403676799603207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12092959751486276264550437 2267429953403676799603207)
              ·
                refine ⟨3401144930105515199404811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267429953403676799603207 3401144930105515199404811)
                ·
                  refine ⟨5101717395158272799107217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3401144930105515199404811 5101717395158272799107217)
                  ·
                    refine ⟨3826288046368704599330413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5101717395158272799107217 3826288046368704599330413)
                    ·
                      refine ⟨1434858017388264224748905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3826288046368704599330413 1434858017388264224748905)
                      ·
                        rfl

theorem cell23_2794376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_2794376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794376 prefixEnd_2794376 := by exact prefixLift 2794376
  have htrace : WordTrace (prefixWord ++ tailWord_2794376) baseStart_2794376 baseEnd_2794376 := by
    simpa [prefixWord, tailWord_2794376, baseEnd_2794376] using wordTrace_append hprefix tailTrace_2794376
  have hstable : (prefixWord ++ tailWord_2794376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794376).length < 2 ^ (prefixWord ++ tailWord_2794376).sum := by decide
  have hdescent : baseEnd_2794376 < baseStart_2794376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794389 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_2794389 : Nat := 118140960795 + 2794389 * 2 ^ 59
def prefixEnd_2794389 : Nat := 4983230072969 + 3 ^ 40 * 2794389 * 2
def baseEnd_2794389 : Nat := 1434864692636772673886345

theorem tailTrace_2794389 : CollatzResearch.WordTrace tailWord_2794389 prefixEnd_2794389 1434864692636772673886345 := by
  unfold tailWord_2794389
  simp only [CollatzResearch.WordTrace]
  refine ⟨101919739873413371491002221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67946493248942247660668147 101919739873413371491002221)
  ·
    refine ⟨38219902452530014309125833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101919739873413371491002221 38219902452530014309125833)
    ·
      refine ⟨28664926839397510731844375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38219902452530014309125833 28664926839397510731844375)
      ·
        refine ⟨42997390259096266097766563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28664926839397510731844375 42997390259096266097766563)
        ·
          refine ⟨64496085388644399146649845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42997390259096266097766563 64496085388644399146649845)
          ·
            refine ⟨6046508005185412419998423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64496085388644399146649845 6046508005185412419998423)
            ·
              refine ⟨9069762007778118629997635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046508005185412419998423 9069762007778118629997635)
              ·
                refine ⟨13604643011667177944996453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9069762007778118629997635 13604643011667177944996453)
                ·
                  refine ⟨2550870564687595864686835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13604643011667177944996453 2550870564687595864686835)
                  ·
                    refine ⟨3826305847031393797030253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2550870564687595864686835 3826305847031393797030253)
                    ·
                      refine ⟨1434864692636772673886345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3826305847031393797030253 1434864692636772673886345)
                      ·
                        rfl

theorem cell23_2794389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_2794389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794389 prefixEnd_2794389 := by exact prefixLift 2794389
  have htrace : WordTrace (prefixWord ++ tailWord_2794389) baseStart_2794389 baseEnd_2794389 := by
    simpa [prefixWord, tailWord_2794389, baseEnd_2794389] using wordTrace_append hprefix tailTrace_2794389
  have hstable : (prefixWord ++ tailWord_2794389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794389).length < 2 ^ (prefixWord ++ tailWord_2794389).sum := by decide
  have hdescent : baseEnd_2794389 < baseStart_2794389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794390 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2794390 : Nat := 118140960795 + 2794390 * 2 ^ 59
def prefixEnd_2794390 : Nat := 4983230072969 + 3 ^ 40 * 2794390 * 2
def baseEnd_2794390 : Nat := 1434865206117427169973841

theorem tailTrace_2794390 : CollatzResearch.WordTrace tailWord_2794390 prefixEnd_2794390 1434865206117427169973841 := by
  unfold tailWord_2794390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6369986021650609291361789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67946517564273165774525749 6369986021650609291361789)
  ·
    refine ⟨2388744758118978484260671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6369986021650609291361789 2388744758118978484260671)
    ·
      refine ⟨3583117137178467726391007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388744758118978484260671 3583117137178467726391007)
      ·
        refine ⟨5374675705767701589586511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583117137178467726391007 5374675705767701589586511)
        ·
          refine ⟨8062013558651552384379767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374675705767701589586511 8062013558651552384379767)
          ·
            refine ⟨12093020337977328576569651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062013558651552384379767 12093020337977328576569651)
            ·
              refine ⟨18139530506965992864854477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12093020337977328576569651 18139530506965992864854477)
              ·
                refine ⟨6802323940112247324320429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18139530506965992864854477 6802323940112247324320429)
                ·
                  refine ⟨2550871477542092746620161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6802323940112247324320429 2550871477542092746620161)
                  ·
                    refine ⟨1913153608156569559965121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2550871477542092746620161 1913153608156569559965121)
                    ·
                      refine ⟨1434865206117427169973841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913153608156569559965121 1434865206117427169973841)
                      ·
                        rfl

theorem cell23_2794390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2794390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794390 prefixEnd_2794390 := by exact prefixLift 2794390
  have htrace : WordTrace (prefixWord ++ tailWord_2794390) baseStart_2794390 baseEnd_2794390 := by
    simpa [prefixWord, tailWord_2794390, baseEnd_2794390] using wordTrace_append hprefix tailTrace_2794390
  have hstable : (prefixWord ++ tailWord_2794390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794390).length < 2 ^ (prefixWord ++ tailWord_2794390).sum := by decide
  have hdescent : baseEnd_2794390 < baseStart_2794390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794413 : List Nat := [1, 5, 2, 3, 2, 1, 2, 7]
def baseStart_2794413 : Nat := 118140960795 + 2794413 * 2 ^ 59
def prefixEnd_2794413 : Nat := 4983230072969 + 3 ^ 40 * 2794413 * 2
def baseEnd_2794413 : Nat := 53143593191573354814305

theorem tailTrace_2794413 : CollatzResearch.WordTrace tailWord_2794413 prefixEnd_2794413 53143593191573354814305 := by
  unfold tailWord_2794413
  simp only [CollatzResearch.WordTrace]
  refine ⟨101920615225326423589875893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67947076816884282393250595 101920615225326423589875893)
  ·
    refine ⟨9555057677374352211550865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101920615225326423589875893 9555057677374352211550865)
    ·
      refine ⟨7166293258030764158663149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9555057677374352211550865 7166293258030764158663149)
      ·
        refine ⟨2687359971761536559498681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7166293258030764158663149 2687359971761536559498681)
        ·
          refine ⟨2015519978821152419624011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2687359971761536559498681 2015519978821152419624011)
          ·
            refine ⟨3023279968231728629436017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015519978821152419624011 3023279968231728629436017)
            ·
              refine ⟨2267459976173796472077013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3023279968231728629436017 2267459976173796472077013)
              ·
                refine ⟨53143593191573354814305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2267459976173796472077013 53143593191573354814305)
                ·
                  rfl

theorem cell23_2794413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 7].length) (baseStart_2794413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794413 prefixEnd_2794413 := by exact prefixLift 2794413
  have htrace : WordTrace (prefixWord ++ tailWord_2794413) baseStart_2794413 baseEnd_2794413 := by
    simpa [prefixWord, tailWord_2794413, baseEnd_2794413] using wordTrace_append hprefix tailTrace_2794413
  have hstable : (prefixWord ++ tailWord_2794413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794413).length < 2 ^ (prefixWord ++ tailWord_2794413).sum := by decide
  have hdescent : baseEnd_2794413 < baseStart_2794413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794432 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_2794432 : Nat := 118140960795 + 2794432 * 2 ^ 59
def prefixEnd_2794432 : Nat := 4983230072969 + 3 ^ 40 * 2794432 * 2
def baseEnd_2794432 : Nat := 1434886772304916005648647

theorem tailTrace_2794432 : CollatzResearch.WordTrace tailWord_2794432 prefixEnd_2794432 1434886772304916005648647 := by
  unfold tailWord_2794432
  simp only [CollatzResearch.WordTrace]
  refine ⟨50960654106128794917408775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67947538808171726556545033 50960654106128794917408775)
  ·
    refine ⟨76440981159193192376113163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50960654106128794917408775 76440981159193192376113163)
    ·
      refine ⟨114661471738789788564169745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76440981159193192376113163 114661471738789788564169745)
      ·
        refine ⟨85996103804092341423127309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114661471738789788564169745 85996103804092341423127309)
        ·
          refine ⟨32248538926534628033672741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85996103804092341423127309 32248538926534628033672741)
          ·
            refine ⟨6046601048725242756313639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32248538926534628033672741 6046601048725242756313639)
            ·
              refine ⟨9069901573087864134470459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046601048725242756313639 9069901573087864134470459)
              ·
                refine ⟨13604852359631796201705689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9069901573087864134470459 13604852359631796201705689)
                ·
                  refine ⟨10203639269723847151279267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13604852359631796201705689 10203639269723847151279267)
                  ·
                    refine ⟨15305458904585770726918901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10203639269723847151279267 15305458904585770726918901)
                    ·
                      refine ⟨1434886772304916005648647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15305458904585770726918901 1434886772304916005648647)
                      ·
                        rfl

theorem cell23_2794432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_2794432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794432 prefixEnd_2794432 := by exact prefixLift 2794432
  have htrace : WordTrace (prefixWord ++ tailWord_2794432) baseStart_2794432 baseEnd_2794432 := by
    simpa [prefixWord, tailWord_2794432, baseEnd_2794432] using wordTrace_append hprefix tailTrace_2794432
  have hstable : (prefixWord ++ tailWord_2794432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794432).length < 2 ^ (prefixWord ++ tailWord_2794432).sum := by decide
  have hdescent : baseEnd_2794432 < baseStart_2794432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794446 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_2794446 : Nat := 118140960795 + 2794446 * 2 ^ 59
def prefixEnd_2794446 : Nat := 4983230072969 + 3 ^ 40 * 2794446 * 2
def baseEnd_2794446 : Nat := 1434893961034078950873583

theorem tailTrace_2794446 : CollatzResearch.WordTrace tailWord_2794446 prefixEnd_2794446 1434893961034078950873583 := by
  unfold tailWord_2794446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12740227354275858778228399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67947879222804580150551461 12740227354275858778228399)
  ·
    refine ⟨19110341031413788167342599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12740227354275858778228399 19110341031413788167342599)
    ·
      refine ⟨28665511547120682251013899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19110341031413788167342599 28665511547120682251013899)
      ·
        refine ⟨42998267320681023376520849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28665511547120682251013899 42998267320681023376520849)
        ·
          refine ⟨32248700490510767532390637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42998267320681023376520849 32248700490510767532390637)
          ·
            refine ⟨12093262683941537824646489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32248700490510767532390637 12093262683941537824646489)
            ·
              refine ⟨9069947012956153368484867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12093262683941537824646489 9069947012956153368484867)
              ·
                refine ⟨13604920519434230052727301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9069947012956153368484867 13604920519434230052727301)
                ·
                  refine ⟨2550922597393918134886369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13604920519434230052727301 2550922597393918134886369)
                  ·
                    refine ⟨1913191948045438601164777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2550922597393918134886369 1913191948045438601164777)
                    ·
                      refine ⟨1434893961034078950873583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913191948045438601164777 1434893961034078950873583)
                      ·
                        rfl

theorem cell23_2794446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_2794446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794446 prefixEnd_2794446 := by exact prefixLift 2794446
  have htrace : WordTrace (prefixWord ++ tailWord_2794446) baseStart_2794446 baseEnd_2794446 := by
    simpa [prefixWord, tailWord_2794446, baseEnd_2794446] using wordTrace_append hprefix tailTrace_2794446
  have hstable : (prefixWord ++ tailWord_2794446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794446).length < 2 ^ (prefixWord ++ tailWord_2794446).sum := by decide
  have hdescent : baseEnd_2794446 < baseStart_2794446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794455 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_2794455 : Nat := 118140960795 + 2794455 * 2 ^ 59
def prefixEnd_2794455 : Nat := 4983230072969 + 3 ^ 40 * 2794455 * 2
def baseEnd_2794455 : Nat := 1434898582359969415661041

theorem tailTrace_2794455 : CollatzResearch.WordTrace tailWord_2794455 prefixEnd_2794455 1434898582359969415661041 := by
  unfold tailWord_2794455
  simp only [CollatzResearch.WordTrace]
  refine ⟨101922147091174264762904819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67948098060782843175269879 101922147091174264762904819)
  ·
    refine ⟨152883220636761397144357229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101922147091174264762904819 152883220636761397144357229)
    ·
      refine ⟨57331207738785523929133961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152883220636761397144357229 57331207738785523929133961)
      ·
        refine ⟨42998405804089142946850471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57331207738785523929133961 42998405804089142946850471)
        ·
          refine ⟨64497608706133714420275707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42998405804089142946850471 64497608706133714420275707)
          ·
            refine ⟨96746413059200571630413561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64497608706133714420275707 96746413059200571630413561)
            ·
              refine ⟨72559809794400428722810171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96746413059200571630413561 72559809794400428722810171)
              ·
                refine ⟨108839714691600643084215257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72559809794400428722810171 108839714691600643084215257)
                ·
                  refine ⟨81629786018700482313161443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108839714691600643084215257 81629786018700482313161443)
                  ·
                    refine ⟨122444679028050723469742165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81629786018700482313161443 122444679028050723469742165)
                    ·
                      refine ⟨1434898582359969415661041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 122444679028050723469742165 1434898582359969415661041)
                      ·
                        rfl

theorem cell23_2794455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_2794455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794455 prefixEnd_2794455 := by exact prefixLift 2794455
  have htrace : WordTrace (prefixWord ++ tailWord_2794455) baseStart_2794455 baseEnd_2794455 := by
    simpa [prefixWord, tailWord_2794455, baseEnd_2794455] using wordTrace_append hprefix tailTrace_2794455
  have hstable : (prefixWord ++ tailWord_2794455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794455).length < 2 ^ (prefixWord ++ tailWord_2794455).sum := by decide
  have hdescent : baseEnd_2794455 < baseStart_2794455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794463 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 2, 2, 2]
def baseStart_2794463 : Nat := 118140960795 + 2794463 * 2 ^ 59
def prefixEnd_2794463 : Nat := 4983230072969 + 3 ^ 40 * 2794463 * 2
def baseEnd_2794463 : Nat := 1434902690205205384361005

theorem tailTrace_2794463 : CollatzResearch.WordTrace tailWord_2794463 prefixEnd_2794463 1434902690205205384361005 := by
  unfold tailWord_2794463
  simp only [CollatzResearch.WordTrace]
  refine ⟨101922438875145282129196043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67948292583430188086130695 101922438875145282129196043)
  ·
    refine ⟨152883658312717923193794065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101922438875145282129196043 152883658312717923193794065)
    ·
      refine ⟨114662743734538442395345549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152883658312717923193794065 114662743734538442395345549)
      ·
        refine ⟨42998528900451915898254581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114662743734538442395345549 42998528900451915898254581)
        ·
          refine ⟨4031112084417367115461367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42998528900451915898254581 4031112084417367115461367)
          ·
            refine ⟨6046668126626050673192051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031112084417367115461367 6046668126626050673192051)
            ·
              refine ⟨9070002189939076009788077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046668126626050673192051 9070002189939076009788077)
              ·
                refine ⟨3401250821227153503670529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9070002189939076009788077 3401250821227153503670529)
                ·
                  refine ⟨2550938115920365127752897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3401250821227153503670529 2550938115920365127752897)
                  ·
                    refine ⟨1913203586940273845814673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2550938115920365127752897 1913203586940273845814673)
                    ·
                      refine ⟨1434902690205205384361005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913203586940273845814673 1434902690205205384361005)
                      ·
                        rfl

theorem cell23_2794463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_2794463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794463 prefixEnd_2794463 := by exact prefixLift 2794463
  have htrace : WordTrace (prefixWord ++ tailWord_2794463) baseStart_2794463 baseEnd_2794463 := by
    simpa [prefixWord, tailWord_2794463, baseEnd_2794463] using wordTrace_append hprefix tailTrace_2794463
  have hstable : (prefixWord ++ tailWord_2794463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794463).length < 2 ^ (prefixWord ++ tailWord_2794463).sum := by decide
  have hdescent : baseEnd_2794463 < baseStart_2794463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794492 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2794492 : Nat := 118140960795 + 2794492 * 2 ^ 59
def prefixEnd_2794492 : Nat := 4983230072969 + 3 ^ 40 * 2794492 * 2
def baseEnd_2794492 : Nat := 1434917581144185770898371

theorem tailTrace_2794492 : CollatzResearch.WordTrace tailWord_2794492 prefixEnd_2794492 1434917581144185770898371 := by
  unfold tailWord_2794492
  simp only [CollatzResearch.WordTrace]
  refine ⟨50961748296020110041000865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67948997728026813388001153 50961748296020110041000865)
  ·
    refine ⟨38221311222015082530750649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50961748296020110041000865 38221311222015082530750649)
    ·
      refine ⟨28665983416511311898062987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38221311222015082530750649 28665983416511311898062987)
      ·
        refine ⟨42998975124766967847094481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28665983416511311898062987 42998975124766967847094481)
        ·
          refine ⟨32249231343575225885320861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42998975124766967847094481 32249231343575225885320861)
          ·
            refine ⟨12093461753840709706995323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32249231343575225885320861 12093461753840709706995323)
            ·
              refine ⟨18140192630761064560492985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12093461753840709706995323 18140192630761064560492985)
              ·
                refine ⟨13605144473070798420369739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18140192630761064560492985 13605144473070798420369739)
                ·
                  refine ⟨20407716709606197630554609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13605144473070798420369739 20407716709606197630554609)
                  ·
                    refine ⟨15305787532204648222915957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20407716709606197630554609 15305787532204648222915957)
                    ·
                      refine ⟨1434917581144185770898371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15305787532204648222915957 1434917581144185770898371)
                      ·
                        rfl

theorem cell23_2794492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2794492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794492 prefixEnd_2794492 := by exact prefixLift 2794492
  have htrace : WordTrace (prefixWord ++ tailWord_2794492) baseStart_2794492 baseEnd_2794492 := by
    simpa [prefixWord, tailWord_2794492, baseEnd_2794492] using wordTrace_append hprefix tailTrace_2794492
  have hstable : (prefixWord ++ tailWord_2794492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794492).length < 2 ^ (prefixWord ++ tailWord_2794492).sum := by decide
  have hdescent : baseEnd_2794492 < baseStart_2794492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794529 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 5, 4]
def baseStart_2794529 : Nat := 118140960795 + 2794529 * 2 ^ 59
def prefixEnd_2794529 : Nat := 4983230072969 + 3 ^ 40 * 2794529 * 2
def baseEnd_2794529 : Nat := 478312193309467375378567

theorem tailTrace_2794529 : CollatzResearch.WordTrace tailWord_2794529 prefixEnd_2794529 478312193309467375378567 := by
  unfold tailWord_2794529
  simp only [CollatzResearch.WordTrace]
  refine ⟨101924846092906175401098641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67949897395270783600732427 101924846092906175401098641)
  ·
    refine ⟨76443634569679631550823981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101924846092906175401098641 76443634569679631550823981)
    ·
      refine ⟨28666362963629861831558993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76443634569679631550823981 28666362963629861831558993)
      ·
        refine ⟨21499772222722396373669245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28666362963629861831558993 21499772222722396373669245)
        ·
          refine ⟨8062414583520898640125967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21499772222722396373669245 8062414583520898640125967)
          ·
            refine ⟨12093621875281347960188951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062414583520898640125967 12093621875281347960188951)
            ·
              refine ⟨18140432812922021940283427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12093621875281347960188951 18140432812922021940283427)
              ·
                refine ⟨27210649219383032910425141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18140432812922021940283427 27210649219383032910425141)
                ·
                  refine ⟨2550998364317159335352357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27210649219383032910425141 2550998364317159335352357)
                  ·
                    refine ⟨478312193309467375378567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2550998364317159335352357 478312193309467375378567)
                    ·
                      rfl

theorem cell23_2794529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_2794529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794529 prefixEnd_2794529 := by exact prefixLift 2794529
  have htrace : WordTrace (prefixWord ++ tailWord_2794529) baseStart_2794529 baseEnd_2794529 := by
    simpa [prefixWord, tailWord_2794529, baseEnd_2794529] using wordTrace_append hprefix tailTrace_2794529
  have hstable : (prefixWord ++ tailWord_2794529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794529).length < 2 ^ (prefixWord ++ tailWord_2794529).sum := by decide
  have hdescent : baseEnd_2794529 < baseStart_2794529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794579 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 1, 5, 2]
def baseStart_2794579 : Nat := 118140960795 + 2794579 * 2 ^ 59
def prefixEnd_2794579 : Nat := 4983230072969 + 3 ^ 40 * 2794579 * 2
def baseEnd_2794579 : Nat := 1434962253961126930510471

theorem tailTrace_2794579 : CollatzResearch.WordTrace tailWord_2794579 prefixEnd_2794579 1434962253961126930510471 := by
  unfold tailWord_2794579
  simp only [CollatzResearch.WordTrace]
  refine ⟨101926669742725033940418791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67951113161816689293612527 101926669742725033940418791)
  ·
    refine ⟨152890004614087550910628187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101926669742725033940418791 152890004614087550910628187)
    ·
      refine ⟨229335006921131326365942281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152890004614087550910628187 229335006921131326365942281)
      ·
        refine ⟨172001255190848494774456711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229335006921131326365942281 172001255190848494774456711)
        ·
          refine ⟨258001882786272742161685067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172001255190848494774456711 258001882786272742161685067)
          ·
            refine ⟨387002824179409113242527601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258001882786272742161685067 387002824179409113242527601)
            ·
              refine ⟨290252118134556834931895701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387002824179409113242527601 290252118134556834931895701)
              ·
                refine ⟨13605568037557351637432611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 290252118134556834931895701 13605568037557351637432611)
                ·
                  refine ⟨20408352056336027456148917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13605568037557351637432611 20408352056336027456148917)
                  ·
                    refine ⟨1913283005281502574013961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20408352056336027456148917 1913283005281502574013961)
                    ·
                      refine ⟨1434962253961126930510471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913283005281502574013961 1434962253961126930510471)
                      ·
                        rfl

theorem cell23_2794579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 5, 2].length) (baseStart_2794579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794579 prefixEnd_2794579 := by exact prefixLift 2794579
  have htrace : WordTrace (prefixWord ++ tailWord_2794579) baseStart_2794579 baseEnd_2794579 := by
    simpa [prefixWord, tailWord_2794579, baseEnd_2794579] using wordTrace_append hprefix tailTrace_2794579
  have hstable : (prefixWord ++ tailWord_2794579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794579).length < 2 ^ (prefixWord ++ tailWord_2794579).sum := by decide
  have hdescent : baseEnd_2794579 < baseStart_2794579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794596 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_2794596 : Nat := 118140960795 + 2794596 * 2 ^ 59
def prefixEnd_2794596 : Nat := 4983230072969 + 3 ^ 40 * 2794596 * 2
def baseEnd_2794596 : Nat := 1434970983132253363997893

theorem tailTrace_2794596 : CollatzResearch.WordTrace tailWord_2794596 prefixEnd_2794596 1434970983132253363997893 := by
  unfold tailWord_2794596
  simp only [CollatzResearch.WordTrace]
  refine ⟨50963644891831722921893821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67951526522442297229191761 50963644891831722921893821)
  ·
    refine ⟨19111366834436896095710183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50963644891831722921893821 19111366834436896095710183)
    ·
      refine ⟨28667050251655344143565275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19111366834436896095710183 28667050251655344143565275)
      ·
        refine ⟨43000575377483016215347913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28667050251655344143565275 43000575377483016215347913)
        ·
          refine ⟨32250431533112262161510935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43000575377483016215347913 32250431533112262161510935)
          ·
            refine ⟨48375647299668393242266403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32250431533112262161510935 48375647299668393242266403)
            ·
              refine ⟨72563470949502589863399605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48375647299668393242266403 72563470949502589863399605)
              ·
                refine ⟨6802825401515867799693713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72563470949502589863399605 6802825401515867799693713)
                ·
                  refine ⟨5102119051136900849770285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6802825401515867799693713 5102119051136900849770285)
                  ·
                    refine ⟨1913294644176337818663857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5102119051136900849770285 1913294644176337818663857)
                    ·
                      refine ⟨1434970983132253363997893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913294644176337818663857 1434970983132253363997893)
                      ·
                        rfl

theorem cell23_2794596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_2794596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794596 prefixEnd_2794596 := by exact prefixLift 2794596
  have htrace : WordTrace (prefixWord ++ tailWord_2794596) baseStart_2794596 baseEnd_2794596 := by
    simpa [prefixWord, tailWord_2794596, baseEnd_2794596] using wordTrace_append hprefix tailTrace_2794596
  have hstable : (prefixWord ++ tailWord_2794596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794596).length < 2 ^ (prefixWord ++ tailWord_2794596).sum := by decide
  have hdescent : baseEnd_2794596 < baseStart_2794596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794606 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_2794606 : Nat := 118140960795 + 2794606 * 2 ^ 59
def prefixEnd_2794606 : Nat := 4983230072969 + 3 ^ 40 * 2794606 * 2
def baseEnd_2794606 : Nat := 478325372646266108290949

theorem tailTrace_2794606 : CollatzResearch.WordTrace tailWord_2794606 prefixEnd_2794606 478325372646266108290949 := by
  unfold tailWord_2794606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12740956814203402193956459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67951769675751478367767781 12740956814203402193956459)
  ·
    refine ⟨19111435221305103290934689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12740956814203402193956459 19111435221305103290934689)
    ·
      refine ⟨14333576415978827468201017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19111435221305103290934689 14333576415978827468201017)
      ·
        refine ⟨10750182311984120601150763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14333576415978827468201017 10750182311984120601150763)
        ·
          refine ⟨16125273467976180901726145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10750182311984120601150763 16125273467976180901726145)
          ·
            refine ⟨12093955100982135676294609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16125273467976180901726145 12093955100982135676294609)
            ·
              refine ⟨9070466325736601757220957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12093955100982135676294609 9070466325736601757220957)
              ·
                refine ⟨3401424872151225658957859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9070466325736601757220957 3401424872151225658957859)
                ·
                  refine ⟨5102137308226838488436789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3401424872151225658957859 5102137308226838488436789)
                  ·
                    refine ⟨478325372646266108290949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5102137308226838488436789 478325372646266108290949)
                    ·
                      rfl

theorem cell23_2794606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_2794606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794606 prefixEnd_2794606 := by exact prefixLift 2794606
  have htrace : WordTrace (prefixWord ++ tailWord_2794606) baseStart_2794606 baseEnd_2794606 := by
    simpa [prefixWord, tailWord_2794606, baseEnd_2794606] using wordTrace_append hprefix tailTrace_2794606
  have hstable : (prefixWord ++ tailWord_2794606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794606).length < 2 ^ (prefixWord ++ tailWord_2794606).sum := by decide
  have hdescent : baseEnd_2794606 < baseStart_2794606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794620 : List Nat := [2, 2, 2, 1, 1, 3, 5, 2, 1, 1, 3]
def baseStart_2794620 : Nat := 118140960795 + 2794620 * 2 ^ 59
def prefixEnd_2794620 : Nat := 4983230072969 + 3 ^ 40 * 2794620 * 2
def baseEnd_2794620 : Nat := 1434983306667961270097783

theorem tailTrace_2794620 : CollatzResearch.WordTrace tailWord_2794620 prefixEnd_2794620 1434983306667961270097783 := by
  unfold tailWord_2794620
  simp only [CollatzResearch.WordTrace]
  refine ⟨50964082567788248971330657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67952110090384331961774209 50964082567788248971330657)
  ·
    refine ⟨38223061925841186728497993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50964082567788248971330657 38223061925841186728497993)
    ·
      refine ⟨28667296444380890046373495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38223061925841186728497993 28667296444380890046373495)
      ·
        refine ⟨43000944666571335069560243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28667296444380890046373495 43000944666571335069560243)
        ·
          refine ⟨64501416999857002604340365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43000944666571335069560243 64501416999857002604340365)
          ·
            refine ⟨24188031374946375976627637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64501416999857002604340365 24188031374946375976627637)
            ·
              refine ⟨2267627941401222747808841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24188031374946375976627637 2267627941401222747808841)
              ·
                refine ⟨1700720956050917060856631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2267627941401222747808841 1700720956050917060856631)
                ·
                  refine ⟨2551081434076375591284947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700720956050917060856631 2551081434076375591284947)
                  ·
                    refine ⟨3826622151114563386927421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2551081434076375591284947 3826622151114563386927421)
                    ·
                      refine ⟨1434983306667961270097783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3826622151114563386927421 1434983306667961270097783)
                      ·
                        rfl

theorem cell23_2794620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_2794620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794620 prefixEnd_2794620 := by exact prefixLift 2794620
  have htrace : WordTrace (prefixWord ++ tailWord_2794620) baseStart_2794620 baseEnd_2794620 := by
    simpa [prefixWord, tailWord_2794620, baseEnd_2794620] using wordTrace_append hprefix tailTrace_2794620
  have hstable : (prefixWord ++ tailWord_2794620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794620).length < 2 ^ (prefixWord ++ tailWord_2794620).sum := by decide
  have hdescent : baseEnd_2794620 < baseStart_2794620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794663 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2794663 : Nat := 118140960795 + 2794663 * 2 ^ 59
def prefixEnd_2794663 : Nat := 4983230072969 + 3 ^ 40 * 2794663 * 2
def baseEnd_2794663 : Nat := 1435005386336104601860085

theorem tailTrace_2794663 : CollatzResearch.WordTrace tailWord_2794663 prefixEnd_2794663 1435005386336104601860085 := by
  unfold tailWord_2794663
  simp only [CollatzResearch.WordTrace]
  refine ⟨101929733474420716286476643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67953155649613810857651095 101929733474420716286476643)
  ·
    refine ⟨152894600211631074429714965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101929733474420716286476643 152894600211631074429714965)
    ·
      refine ⟨7166934384920206613892889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152894600211631074429714965 7166934384920206613892889)
      ·
        refine ⟨5375200788690154960419667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7166934384920206613892889 5375200788690154960419667)
        ·
          refine ⟨8062801183035232440629501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5375200788690154960419667 8062801183035232440629501)
          ·
            refine ⟨3023550443638212165236063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8062801183035232440629501 3023550443638212165236063)
            ·
              refine ⟨4535325665457318247854095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023550443638212165236063 4535325665457318247854095)
              ·
                refine ⟨6802988498185977371781143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535325665457318247854095 6802988498185977371781143)
                ·
                  refine ⟨10204482747278966057671715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6802988498185977371781143 10204482747278966057671715)
                  ·
                    refine ⟨15306724120918449086507573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10204482747278966057671715 15306724120918449086507573)
                    ·
                      refine ⟨1435005386336104601860085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15306724120918449086507573 1435005386336104601860085)
                      ·
                        rfl

theorem cell23_2794663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2794663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794663 prefixEnd_2794663 := by exact prefixLift 2794663
  have htrace : WordTrace (prefixWord ++ tailWord_2794663) baseStart_2794663 baseEnd_2794663 := by
    simpa [prefixWord, tailWord_2794663, baseEnd_2794663] using wordTrace_append hprefix tailTrace_2794663
  have hstable : (prefixWord ++ tailWord_2794663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794663).length < 2 ^ (prefixWord ++ tailWord_2794663).sum := by decide
  have hdescent : baseEnd_2794663 < baseStart_2794663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794719 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_2794719 : Nat := 118140960795 + 2794719 * 2 ^ 59
def prefixEnd_2794719 : Nat := 4983230072969 + 3 ^ 40 * 2794719 * 2
def baseEnd_2794719 : Nat := 1435034141252756382759827

theorem tailTrace_2794719 : CollatzResearch.WordTrace tailWord_2794719 prefixEnd_2794719 1435034141252756382759827 := by
  unfold tailWord_2794719
  simp only [CollatzResearch.WordTrace]
  refine ⟨101931775962217837850515211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67954517308145225233676807 101931775962217837850515211)
  ·
    refine ⟨152897663943326756775772817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101931775962217837850515211 152897663943326756775772817)
    ·
      refine ⟨114673247957495067581829613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152897663943326756775772817 114673247957495067581829613)
      ·
        refine ⟨43002467984060650343186105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114673247957495067581829613 43002467984060650343186105)
        ·
          refine ⟨32251850988045487757389579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43002467984060650343186105 32251850988045487757389579)
          ·
            refine ⟨48377776482068231636084369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32251850988045487757389579 48377776482068231636084369)
            ·
              refine ⟨36283332361551173727063277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48377776482068231636084369 36283332361551173727063277)
              ·
                refine ⟨13606249635581690147648729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36283332361551173727063277 13606249635581690147648729)
                ·
                  refine ⟨10204687226686267610736547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13606249635581690147648729 10204687226686267610736547)
                  ·
                    refine ⟨15307030840029401416104821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10204687226686267610736547 15307030840029401416104821)
                    ·
                      refine ⟨1435034141252756382759827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15307030840029401416104821 1435034141252756382759827)
                      ·
                        rfl

theorem cell23_2794719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_2794719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794719 prefixEnd_2794719 := by exact prefixLift 2794719
  have htrace : WordTrace (prefixWord ++ tailWord_2794719) baseStart_2794719 baseEnd_2794719 := by
    simpa [prefixWord, tailWord_2794719, baseEnd_2794719] using wordTrace_append hprefix tailTrace_2794719
  have hstable : (prefixWord ++ tailWord_2794719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794719).length < 2 ^ (prefixWord ++ tailWord_2794719).sum := by decide
  have hdescent : baseEnd_2794719 < baseStart_2794719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794720 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 1, 3, 2]
def baseStart_2794720 : Nat := 118140960795 + 2794720 * 2 ^ 59
def prefixEnd_2794720 : Nat := 4983230072969 + 3 ^ 40 * 2794720 * 2
def baseEnd_2794720 : Nat := 1435034654733410878847323

theorem tailTrace_2794720 : CollatzResearch.WordTrace tailWord_2794720 prefixEnd_2794720 1435034654733410878847323 := by
  unfold tailWord_2794720
  simp only [CollatzResearch.WordTrace]
  refine ⟨50965906217607107510650807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67954541623476143347534409 50965906217607107510650807)
  ·
    refine ⟨76448859326410661265976211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50965906217607107510650807 76448859326410661265976211)
    ·
      refine ⟨114673288989615991898964317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76448859326410661265976211 114673288989615991898964317)
      ·
        refine ⟨43002483371105996962111619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114673288989615991898964317 43002483371105996962111619)
        ·
          refine ⟨64503725056658995443167429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43002483371105996962111619 64503725056658995443167429)
          ·
            refine ⟨12094448448123561645593893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64503725056658995443167429 12094448448123561645593893)
            ·
              refine ⟨2267709084023167808548855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12094448448123561645593893 2267709084023167808548855)
              ·
                refine ⟨3401563626034751712823283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267709084023167808548855 3401563626034751712823283)
                ·
                  refine ⟨5102345439052127569234925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3401563626034751712823283 5102345439052127569234925)
                  ·
                    refine ⟨1913379539644547838463097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5102345439052127569234925 1913379539644547838463097)
                    ·
                      refine ⟨1435034654733410878847323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913379539644547838463097 1435034654733410878847323)
                      ·
                        rfl

theorem cell23_2794720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_2794720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794720 prefixEnd_2794720 := by exact prefixLift 2794720
  have htrace : WordTrace (prefixWord ++ tailWord_2794720) baseStart_2794720 baseEnd_2794720 := by
    simpa [prefixWord, tailWord_2794720, baseEnd_2794720] using wordTrace_append hprefix tailTrace_2794720
  have hstable : (prefixWord ++ tailWord_2794720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794720).length < 2 ^ (prefixWord ++ tailWord_2794720).sum := by decide
  have hdescent : baseEnd_2794720 < baseStart_2794720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794727 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2794727 : Nat := 118140960795 + 2794727 * 2 ^ 59
def prefixEnd_2794727 : Nat := 4983230072969 + 3 ^ 40 * 2794727 * 2
def baseEnd_2794727 : Nat := 1435038249097992351459791

theorem tailTrace_2794727 : CollatzResearch.WordTrace tailWord_2794727 prefixEnd_2794727 1435038249097992351459791 := by
  unfold tailWord_2794727
  simp only [CollatzResearch.WordTrace]
  refine ⟨101932067746188855216806435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67954711830792570144537623 101932067746188855216806435)
  ·
    refine ⟨152898101619283282825209653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101932067746188855216806435 152898101619283282825209653)
    ·
      refine ⟨14334197026807807764863405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152898101619283282825209653 14334197026807807764863405)
      ·
        refine ⟨5375323885052927911823777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14334197026807807764863405 5375323885052927911823777)
        ·
          refine ⟨4031492913789695933867833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5375323885052927911823777 4031492913789695933867833)
          ·
            refine ⟨3023619685342271950400875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4031492913789695933867833 3023619685342271950400875)
            ·
              refine ⟨4535429528013407925601313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023619685342271950400875 4535429528013407925601313)
              ·
                refine ⟨3401572146010055944200985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4535429528013407925601313 3401572146010055944200985)
                ·
                  refine ⟨2551179109507541958150739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3401572146010055944200985 2551179109507541958150739)
                  ·
                    refine ⟨3826768664261312937226109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2551179109507541958150739 3826768664261312937226109)
                    ·
                      refine ⟨1435038249097992351459791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3826768664261312937226109 1435038249097992351459791)
                      ·
                        rfl

theorem cell23_2794727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2794727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794727 prefixEnd_2794727 := by exact prefixLift 2794727
  have htrace : WordTrace (prefixWord ++ tailWord_2794727) baseStart_2794727 baseEnd_2794727 := by
    simpa [prefixWord, tailWord_2794727, baseEnd_2794727] using wordTrace_append hprefix tailTrace_2794727
  have hstable : (prefixWord ++ tailWord_2794727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794727).length < 2 ^ (prefixWord ++ tailWord_2794727).sum := by decide
  have hdescent : baseEnd_2794727 < baseStart_2794727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794739 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 7]
def baseStart_2794739 : Nat := 118140960795 + 2794739 * 2 ^ 59
def prefixEnd_2794739 : Nat := 4983230072969 + 3 ^ 40 * 2794739 * 2
def baseEnd_2794739 : Nat := 159449378985094033834415

theorem tailTrace_2794739 : CollatzResearch.WordTrace tailWord_2794739 prefixEnd_2794739 159449378985094033834415 := by
  unfold tailWord_2794739
  simp only [CollatzResearch.WordTrace]
  refine ⟨101932505422145381266243271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67955003614763587510828847 101932505422145381266243271)
  ·
    refine ⟨152898758133218071899364907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101932505422145381266243271 152898758133218071899364907)
    ·
      refine ⟨229348137199827107849047361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152898758133218071899364907 229348137199827107849047361)
      ·
        refine ⟨172011102899870330886785521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229348137199827107849047361 172011102899870330886785521)
        ·
          refine ⟨129008327174902748165089141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172011102899870330886785521 129008327174902748165089141)
          ·
            refine ⟨12094530672647132640477107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129008327174902748165089141 12094530672647132640477107)
            ·
              refine ⟨18141796008970698960715661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12094530672647132640477107 18141796008970698960715661)
              ·
                refine ⟨6803173503364012110268373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18141796008970698960715661 6803173503364012110268373)
                ·
                  refine ⟨159449378985094033834415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6803173503364012110268373 159449378985094033834415)
                  ·
                    rfl

theorem cell23_2794739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 7].length) (baseStart_2794739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794739 prefixEnd_2794739 := by exact prefixLift 2794739
  have htrace : WordTrace (prefixWord ++ tailWord_2794739) baseStart_2794739 baseEnd_2794739 := by
    simpa [prefixWord, tailWord_2794739, baseEnd_2794739] using wordTrace_append hprefix tailTrace_2794739
  have hstable : (prefixWord ++ tailWord_2794739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794739).length < 2 ^ (prefixWord ++ tailWord_2794739).sum := by decide
  have hdescent : baseEnd_2794739 < baseStart_2794739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794750 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_2794750 : Nat := 118140960795 + 2794750 * 2 ^ 59
def prefixEnd_2794750 : Nat := 4983230072969 + 3 ^ 40 * 2794750 * 2
def baseEnd_2794750 : Nat := 1435050059153045761472185

theorem tailTrace_2794750 : CollatzResearch.WordTrace tailWord_2794750 prefixEnd_2794750 1435050059153045761472185 := by
  unfold tailWord_2794750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12741613328138191268111713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67955271083403686763262469 12741613328138191268111713)
  ·
    refine ⟨9556209996103643451083785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12741613328138191268111713 9556209996103643451083785)
    ·
      refine ⟨7167157497077732588312839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9556209996103643451083785 7167157497077732588312839)
      ·
        refine ⟨10750736245616598882469259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7167157497077732588312839 10750736245616598882469259)
        ·
          refine ⟨16126104368424898323703889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10750736245616598882469259 16126104368424898323703889)
          ·
            refine ⟨12094578276318673742777917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16126104368424898323703889 12094578276318673742777917)
            ·
              refine ⟨4535466853619502653541719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12094578276318673742777917 4535466853619502653541719)
              ·
                refine ⟨6803200280429253980312579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535466853619502653541719 6803200280429253980312579)
                ·
                  refine ⟨10204800420643880970468869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6803200280429253980312579 10204800420643880970468869)
                  ·
                    refine ⟨1913400078870727681962913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10204800420643880970468869 1913400078870727681962913)
                    ·
                      refine ⟨1435050059153045761472185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913400078870727681962913 1435050059153045761472185)
                      ·
                        rfl

theorem cell23_2794750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_2794750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794750 prefixEnd_2794750 := by exact prefixLift 2794750
  have htrace : WordTrace (prefixWord ++ tailWord_2794750) baseStart_2794750 baseEnd_2794750 := by
    simpa [prefixWord, tailWord_2794750, baseEnd_2794750] using wordTrace_append hprefix tailTrace_2794750
  have hstable : (prefixWord ++ tailWord_2794750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794750).length < 2 ^ (prefixWord ++ tailWord_2794750).sum := by decide
  have hdescent : baseEnd_2794750 < baseStart_2794750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794756 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 7]
def baseStart_2794756 : Nat := 118140960795 + 2794756 * 2 ^ 59
def prefixEnd_2794756 : Nat := 4983230072969 + 3 ^ 40 * 2794756 * 2
def baseEnd_2794756 : Nat := 159450348892996970888573

theorem tailTrace_2794756 : CollatzResearch.WordTrace tailWord_2794756 prefixEnd_2794756 159450348892996970888573 := by
  unfold tailWord_2794756
  simp only [CollatzResearch.WordTrace]
  refine ⟨50966562731541896584806061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67955416975389195446408081 50966562731541896584806061)
  ·
    refine ⟨19112461024328211219302273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50966562731541896584806061 19112461024328211219302273)
    ·
      refine ⟨14334345768246158414476705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19112461024328211219302273 14334345768246158414476705)
      ·
        refine ⟨10750759326184618810857529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14334345768246158414476705 10750759326184618810857529)
        ·
          refine ⟨8063069494638464108143147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10750759326184618810857529 8063069494638464108143147)
          ·
            refine ⟨12094604241957696162214721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8063069494638464108143147 12094604241957696162214721)
            ·
              refine ⟨9070953181468272121661041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12094604241957696162214721 9070953181468272121661041)
              ·
                refine ⟨6803214886101204091245781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9070953181468272121661041 6803214886101204091245781)
                ·
                  refine ⟨159450348892996970888573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6803214886101204091245781 159450348892996970888573)
                  ·
                    rfl

theorem cell23_2794756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_2794756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794756 prefixEnd_2794756 := by exact prefixLift 2794756
  have htrace : WordTrace (prefixWord ++ tailWord_2794756) baseStart_2794756 baseEnd_2794756 := by
    simpa [prefixWord, tailWord_2794756, baseEnd_2794756] using wordTrace_append hprefix tailTrace_2794756
  have hstable : (prefixWord ++ tailWord_2794756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794756).length < 2 ^ (prefixWord ++ tailWord_2794756).sum := by decide
  have hdescent : baseEnd_2794756 < baseStart_2794756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794769 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 1, 7]
def baseStart_2794769 : Nat := 118140960795 + 2794769 * 2 ^ 59
def prefixEnd_2794769 : Nat := 4983230072969 + 3 ^ 40 * 2794769 * 2
def baseEnd_2794769 : Nat := 478353271761827062378199

theorem tailTrace_2794769 : CollatzResearch.WordTrace tailWord_2794769 prefixEnd_2794769 478353271761827062378199 := by
  unfold tailWord_2794769
  simp only [CollatzResearch.WordTrace]
  refine ⟨101933599612036696389835361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67955733074691130926556907 101933599612036696389835361)
  ·
    refine ⟨76450199709027522292376521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101933599612036696389835361 76450199709027522292376521)
    ·
      refine ⟨57337649781770641719282391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76450199709027522292376521 57337649781770641719282391)
      ·
        refine ⟨86006474672655962578923587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57337649781770641719282391 86006474672655962578923587)
        ·
          refine ⟨129009712008983943868385381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86006474672655962578923587 129009712008983943868385381)
          ·
            refine ⟨24189321001684489475322259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129009712008983943868385381 24189321001684489475322259)
            ·
              refine ⟨36283981502526734212983389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24189321001684489475322259 36283981502526734212983389)
              ·
                refine ⟨13606493063447525329868771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36283981502526734212983389 13606493063447525329868771)
                ·
                  refine ⟨20409739595171287994803157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13606493063447525329868771 20409739595171287994803157)
                  ·
                    refine ⟨478353271761827062378199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20409739595171287994803157 478353271761827062378199)
                    ·
                      rfl

theorem cell23_2794769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_2794769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794769 prefixEnd_2794769 := by exact prefixLift 2794769
  have htrace : WordTrace (prefixWord ++ tailWord_2794769) baseStart_2794769 baseEnd_2794769 := by
    simpa [prefixWord, tailWord_2794769, baseEnd_2794769] using wordTrace_append hprefix tailTrace_2794769
  have hstable : (prefixWord ++ tailWord_2794769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794769).length < 2 ^ (prefixWord ++ tailWord_2794769).sum := by decide
  have hdescent : baseEnd_2794769 < baseStart_2794769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794770 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2794770 : Nat := 118140960795 + 2794770 * 2 ^ 59
def prefixEnd_2794770 : Nat := 4983230072969 + 3 ^ 40 * 2794770 * 2
def baseEnd_2794770 : Nat := 1435060328766135683222093

theorem tailTrace_2794770 : CollatzResearch.WordTrace tailWord_2794770 prefixEnd_2794770 1435060328766135683222093 := by
  unfold tailWord_2794770
  simp only [CollatzResearch.WordTrace]
  refine ⟨25483409021258268390155441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67955757390022049040414509 25483409021258268390155441)
  ·
    refine ⟨19112556765943701292616581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25483409021258268390155441 19112556765943701292616581)
    ·
      refine ⟨3583604393614443992365609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19112556765943701292616581 3583604393614443992365609)
      ·
        refine ⟨2687703295210832994274207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3583604393614443992365609 2687703295210832994274207)
        ·
          refine ⟨4031554942816249491411311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687703295210832994274207 4031554942816249491411311)
          ·
            refine ⟨6047332414224374237116967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031554942816249491411311 6047332414224374237116967)
            ·
              refine ⟨9070998621336561355675451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6047332414224374237116967 9070998621336561355675451)
              ·
                refine ⟨13606497932004842033513177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9070998621336561355675451 13606497932004842033513177)
                ·
                  refine ⟨10204873449003631525134883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13606497932004842033513177 10204873449003631525134883)
                  ·
                    refine ⟨15307310173505447287702325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10204873449003631525134883 15307310173505447287702325)
                    ·
                      refine ⟨1435060328766135683222093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15307310173505447287702325 1435060328766135683222093)
                      ·
                        rfl

theorem cell23_2794770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2794770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794770 prefixEnd_2794770 := by exact prefixLift 2794770
  have htrace : WordTrace (prefixWord ++ tailWord_2794770) baseStart_2794770 baseEnd_2794770 := by
    simpa [prefixWord, tailWord_2794770, baseEnd_2794770] using wordTrace_append hprefix tailTrace_2794770
  have hstable : (prefixWord ++ tailWord_2794770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794770).length < 2 ^ (prefixWord ++ tailWord_2794770).sum := by decide
  have hdescent : baseEnd_2794770 < baseStart_2794770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794779 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 5]
def baseStart_2794779 : Nat := 118140960795 + 2794779 * 2 ^ 59
def prefixEnd_2794779 : Nat := 4983230072969 + 3 ^ 40 * 2794779 * 2
def baseEnd_2794779 : Nat := 1435064950092026148009551

theorem tailTrace_2794779 : CollatzResearch.WordTrace tailWord_2794779 prefixEnd_2794779 1435064950092026148009551 := by
  unfold tailWord_2794779
  simp only [CollatzResearch.WordTrace]
  refine ⟨101933964342000468097699391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67955976228000312065132927 101933964342000468097699391)
  ·
    refine ⟨152900946513000702146549087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101933964342000468097699391 152900946513000702146549087)
    ·
      refine ⟨229351419769501053219823631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152900946513000702146549087 229351419769501053219823631)
      ·
        refine ⟨344027129654251579829735447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229351419769501053219823631 344027129654251579829735447)
        ·
          refine ⟨516040694481377369744603171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344027129654251579829735447 516040694481377369744603171)
          ·
            refine ⟨774061041722066054616904757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516040694481377369744603171 774061041722066054616904757)
            ·
              refine ⟨72568222661443692620334821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 774061041722066054616904757 72568222661443692620334821)
              ·
                refine ⟨13606541749020692366312779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72568222661443692620334821 13606541749020692366312779)
                ·
                  refine ⟨20409812623531038549469169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13606541749020692366312779 20409812623531038549469169)
                  ·
                    refine ⟨15307359467648278912101877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20409812623531038549469169 15307359467648278912101877)
                    ·
                      refine ⟨1435064950092026148009551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15307359467648278912101877 1435064950092026148009551)
                      ·
                        rfl

theorem cell23_2794779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_2794779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794779 prefixEnd_2794779 := by exact prefixLift 2794779
  have htrace : WordTrace (prefixWord ++ tailWord_2794779) baseStart_2794779 baseEnd_2794779 := by
    simpa [prefixWord, tailWord_2794779, baseEnd_2794779] using wordTrace_append hprefix tailTrace_2794779
  have hstable : (prefixWord ++ tailWord_2794779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794779).length < 2 ^ (prefixWord ++ tailWord_2794779).sum := by decide
  have hdescent : baseEnd_2794779 < baseStart_2794779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794816 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 5, 4]
def baseStart_2794816 : Nat := 118140960795 + 2794816 * 2 ^ 59
def prefixEnd_2794816 : Nat := 4983230072969 + 3 ^ 40 * 2794816 * 2
def baseEnd_2794816 : Nat := 478361316292080834415627

theorem tailTrace_2794816 : CollatzResearch.WordTrace tailWord_2794816 prefixEnd_2794816 478361316292080834415627 := by
  unfold tailWord_2794816
  simp only [CollatzResearch.WordTrace]
  refine ⟨50967656921433211708398151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67956875895244282277864201 50967656921433211708398151)
  ·
    refine ⟨76451485382149817562597227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50967656921433211708398151 76451485382149817562597227)
    ·
      refine ⟨114677228073224726343895841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76451485382149817562597227 114677228073224726343895841)
      ·
        refine ⟨86007921054918544757921881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114677228073224726343895841 86007921054918544757921881)
        ·
          refine ⟨64505940791188908568441411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86007921054918544757921881 64505940791188908568441411)
          ·
            refine ⟨96758911186783362852662117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64505940791188908568441411 96758911186783362852662117)
            ·
              refine ⟨18142295847521880534874147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96758911186783362852662117 18142295847521880534874147)
              ·
                refine ⟨27213443771282820802311221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18142295847521880534874147 27213443771282820802311221)
                ·
                  refine ⟨2551260353557764450216677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27213443771282820802311221 2551260353557764450216677)
                  ·
                    refine ⟨478361316292080834415627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2551260353557764450216677 478361316292080834415627)
                    ·
                      rfl

theorem cell23_2794816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 4].length) (baseStart_2794816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794816 prefixEnd_2794816 := by exact prefixLift 2794816
  have htrace : WordTrace (prefixWord ++ tailWord_2794816) baseStart_2794816 baseEnd_2794816 := by
    simpa [prefixWord, tailWord_2794816, baseEnd_2794816] using wordTrace_append hprefix tailTrace_2794816
  have hstable : (prefixWord ++ tailWord_2794816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794816).length < 2 ^ (prefixWord ++ tailWord_2794816).sum := by decide
  have hdescent : baseEnd_2794816 < baseStart_2794816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794819 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 6]
def baseStart_2794819 : Nat := 118140960795 + 2794819 * 2 ^ 59
def prefixEnd_2794819 : Nat := 4983230072969 + 3 ^ 40 * 2794819 * 2
def baseEnd_2794819 : Nat := 1435085489318205991509367

theorem tailTrace_2794819 : CollatzResearch.WordTrace tailWord_2794819 prefixEnd_2794819 1435085489318205991509367 := by
  unfold tailWord_2794819
  simp only [CollatzResearch.WordTrace]
  refine ⟨101935423261855554929155511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67956948841237036619437007 101935423261855554929155511)
  ·
    refine ⟨152903134892783332393733267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101935423261855554929155511 152903134892783332393733267)
    ·
      refine ⟨229354702339174998590599901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152903134892783332393733267 229354702339174998590599901)
      ·
        refine ⟨86008013377190624471474963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229354702339174998590599901 86008013377190624471474963)
        ·
          refine ⟨129012020065785936707212445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86008013377190624471474963 129012020065785936707212445)
          ·
            refine ⟨48379507524669726265204667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129012020065785936707212445 48379507524669726265204667)
            ·
              refine ⟨72569261287004589397807001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48379507524669726265204667 72569261287004589397807001)
              ·
                refine ⟨54426945965253442048355251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72569261287004589397807001 54426945965253442048355251)
                ·
                  refine ⟨81640418947880163072532877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54426945965253442048355251 81640418947880163072532877)
                  ·
                    refine ⟨30615157105455061152199829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81640418947880163072532877 30615157105455061152199829)
                    ·
                      refine ⟨1435085489318205991509367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30615157105455061152199829 1435085489318205991509367)
                      ·
                        rfl

theorem cell23_2794819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_2794819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794819 prefixEnd_2794819 := by exact prefixLift 2794819
  have htrace : WordTrace (prefixWord ++ tailWord_2794819) baseStart_2794819 baseEnd_2794819 := by
    simpa [prefixWord, tailWord_2794819, baseEnd_2794819] using wordTrace_append hprefix tailTrace_2794819
  have hstable : (prefixWord ++ tailWord_2794819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794819).length < 2 ^ (prefixWord ++ tailWord_2794819).sum := by decide
  have hdescent : baseEnd_2794819 < baseStart_2794819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794820 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2794820 : Nat := 118140960795 + 2794820 * 2 ^ 59
def prefixEnd_2794820 : Nat := 4983230072969 + 3 ^ 40 * 2794820 * 2
def baseEnd_2794820 : Nat := 478362000932953495865621

theorem tailTrace_2794820 : CollatzResearch.WordTrace tailWord_2794820 prefixEnd_2794820 478362000932953495865621 := by
  unfold tailWord_2794820
  simp only [CollatzResearch.WordTrace]
  refine ⟨50967729867425966049970957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67956973156567954733294609 50967729867425966049970957)
  ·
    refine ⟨19112898700284737268739109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50967729867425966049970957 19112898700284737268739109)
    ·
      refine ⟨3583668506303388237888583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19112898700284737268739109 3583668506303388237888583)
      ·
        refine ⟨5375502759455082356832875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583668506303388237888583 5375502759455082356832875)
        ·
          refine ⟨8063254139182623535249313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5375502759455082356832875 8063254139182623535249313)
          ·
            refine ⟨6047440604386967651436985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8063254139182623535249313 6047440604386967651436985)
            ·
              refine ⟨4535580453290225738577739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6047440604386967651436985 4535580453290225738577739)
              ·
                refine ⟨6803370679935338607866609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535580453290225738577739 6803370679935338607866609)
                ·
                  refine ⟨5102528009951503955899957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6803370679935338607866609 5102528009951503955899957)
                  ·
                    refine ⟨478362000932953495865621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5102528009951503955899957 478362000932953495865621)
                    ·
                      rfl

theorem cell23_2794820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2794820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794820 prefixEnd_2794820 := by exact prefixLift 2794820
  have htrace : WordTrace (prefixWord ++ tailWord_2794820) baseStart_2794820 baseEnd_2794820 := by
    simpa [prefixWord, tailWord_2794820, baseEnd_2794820] using wordTrace_append hprefix tailTrace_2794820
  have hstable : (prefixWord ++ tailWord_2794820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794820).length < 2 ^ (prefixWord ++ tailWord_2794820).sum := by decide
  have hdescent : baseEnd_2794820 < baseStart_2794820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794823 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_2794823 : Nat := 118140960795 + 2794823 * 2 ^ 59
def prefixEnd_2794823 : Nat := 4983230072969 + 3 ^ 40 * 2794823 * 2
def baseEnd_2794823 : Nat := 1435087543240823975859349

theorem tailTrace_2794823 : CollatzResearch.WordTrace tailWord_2794823 prefixEnd_2794823 1435087543240823975859349 := by
  unfold tailWord_2794823
  simp only [CollatzResearch.WordTrace]
  refine ⟨101935569153841063612301123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67957046102560709074867415 101935569153841063612301123)
  ·
    refine ⟨152903353730761595418451685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101935569153841063612301123 152903353730761595418451685)
    ·
      refine ⟨28669378824517799140959691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152903353730761595418451685 28669378824517799140959691)
      ·
        refine ⟨43004068236776698711439537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28669378824517799140959691 43004068236776698711439537)
        ·
          refine ⟨32253051177582524033579653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43004068236776698711439537 32253051177582524033579653)
          ·
            refine ⟨6047447095796723256296185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32253051177582524033579653 6047447095796723256296185)
            ·
              refine ⟨4535585321847542442222139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6047447095796723256296185 4535585321847542442222139)
              ·
                refine ⟨6803377982771313663333209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535585321847542442222139 6803377982771313663333209)
                ·
                  refine ⟨5102533487078485247499907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6803377982771313663333209 5102533487078485247499907)
                  ·
                    refine ⟨7653800230617727871249861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5102533487078485247499907 7653800230617727871249861)
                    ·
                      refine ⟨1435087543240823975859349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7653800230617727871249861 1435087543240823975859349)
                      ·
                        rfl

theorem cell23_2794823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_2794823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794823 prefixEnd_2794823 := by exact prefixLift 2794823
  have htrace : WordTrace (prefixWord ++ tailWord_2794823) baseStart_2794823 baseEnd_2794823 := by
    simpa [prefixWord, tailWord_2794823, baseEnd_2794823] using wordTrace_append hprefix tailTrace_2794823
  have hstable : (prefixWord ++ tailWord_2794823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794823).length < 2 ^ (prefixWord ++ tailWord_2794823).sum := by decide
  have hdescent : baseEnd_2794823 < baseStart_2794823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794826 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_2794826 : Nat := 118140960795 + 2794826 * 2 ^ 59
def prefixEnd_2794826 : Nat := 4983230072969 + 3 ^ 40 * 2794826 * 2
def baseEnd_2794826 : Nat := 1435089083682787464121835

theorem tailTrace_2794826 : CollatzResearch.WordTrace tailWord_2794826 prefixEnd_2794826 1435089083682787464121835 := by
  unfold tailWord_2794826
  simp only [CollatzResearch.WordTrace]
  refine ⟨25483919643207548781165083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67957119048553463416440221 25483919643207548781165083)
  ·
    refine ⟨38225879464811323171747625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25483919643207548781165083 38225879464811323171747625)
    ·
      refine ⟨28669409598608492378810719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38225879464811323171747625 28669409598608492378810719)
      ·
        refine ⟨43004114397912738568216079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28669409598608492378810719 43004114397912738568216079)
        ·
          refine ⟨64506171596869107852324119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43004114397912738568216079 64506171596869107852324119)
          ·
            refine ⟨96759257395303661778486179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64506171596869107852324119 96759257395303661778486179)
            ·
              refine ⟨145138886092955492667729269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96759257395303661778486179 145138886092955492667729269)
              ·
                refine ⟨13606770571214577437599619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145138886092955492667729269 13606770571214577437599619)
                ·
                  refine ⟨20410155856821866156399429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13606770571214577437599619 20410155856821866156399429)
                  ·
                    refine ⟨3826904223154099904324893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20410155856821866156399429 3826904223154099904324893)
                    ·
                      refine ⟨1435089083682787464121835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3826904223154099904324893 1435089083682787464121835)
                      ·
                        rfl

theorem cell23_2794826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_2794826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794826 prefixEnd_2794826 := by exact prefixLift 2794826
  have htrace : WordTrace (prefixWord ++ tailWord_2794826) baseStart_2794826 baseEnd_2794826 := by
    simpa [prefixWord, tailWord_2794826, baseEnd_2794826] using wordTrace_append hprefix tailTrace_2794826
  have hstable : (prefixWord ++ tailWord_2794826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794826).length < 2 ^ (prefixWord ++ tailWord_2794826).sum := by decide
  have hdescent : baseEnd_2794826 < baseStart_2794826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794836 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_2794836 : Nat := 118140960795 + 2794836 * 2 ^ 59
def prefixEnd_2794836 : Nat := 4983230072969 + 3 ^ 40 * 2794836 * 2
def baseEnd_2794836 : Nat := 1435094218489332424996789

theorem tailTrace_2794836 : CollatzResearch.WordTrace tailWord_2794836 prefixEnd_2794836 1435094218489332424996789 := by
  unfold tailWord_2794836
  simp only [CollatzResearch.WordTrace]
  refine ⟨50968021651396983416262181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67957362201862644555016241 50968021651396983416262181)
  ·
    refine ⟨9556504059636934390549159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50968021651396983416262181 9556504059636934390549159)
    ·
      refine ⟨14334756089455401585823739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9556504059636934390549159 14334756089455401585823739)
      ·
        refine ⟨21502134134183102378735609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14334756089455401585823739 21502134134183102378735609)
        ·
          refine ⟨16126600600637326784051707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21502134134183102378735609 16126600600637326784051707)
          ·
            refine ⟨24189900900955990176077561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16126600600637326784051707 24189900900955990176077561)
            ·
              refine ⟨18142425675716992632058171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24189900900955990176077561 18142425675716992632058171)
              ·
                refine ⟨27213638513575488948087257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18142425675716992632058171 27213638513575488948087257)
                ·
                  refine ⟨20410228885181616711065443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27213638513575488948087257 20410228885181616711065443)
                  ·
                    refine ⟨30615343327772425066598165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20410228885181616711065443 30615343327772425066598165)
                    ·
                      refine ⟨1435094218489332424996789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30615343327772425066598165 1435094218489332424996789)
                      ·
                        rfl

theorem cell23_2794836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_2794836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794836 prefixEnd_2794836 := by exact prefixLift 2794836
  have htrace : WordTrace (prefixWord ++ tailWord_2794836) baseStart_2794836 baseEnd_2794836 := by
    simpa [prefixWord, tailWord_2794836, baseEnd_2794836] using wordTrace_append hprefix tailTrace_2794836
  have hstable : (prefixWord ++ tailWord_2794836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794836).length < 2 ^ (prefixWord ++ tailWord_2794836).sum := by decide
  have hdescent : baseEnd_2794836 < baseStart_2794836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794859 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 11]
def baseStart_2794859 : Nat := 118140960795 + 2794859 * 2 ^ 59
def prefixEnd_2794859 : Nat := 4983230072969 + 3 ^ 40 * 2794859 * 2
def baseEnd_2794859 : Nat := 478368676181461945003061

theorem tailTrace_2794859 : CollatzResearch.WordTrace tailWord_2794859 prefixEnd_2794859 478368676181461945003061 := by
  unfold tailWord_2794859
  simp only [CollatzResearch.WordTrace]
  refine ⟨101936882181710641760611631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67957921454473761173741087 101936882181710641760611631)
  ·
    refine ⟨152905323272565962640917447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101936882181710641760611631 152905323272565962640917447)
    ·
      refine ⟨229357984908848943961376171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152905323272565962640917447 229357984908848943961376171)
      ·
        refine ⟨344036977363273415942064257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229357984908848943961376171 344036977363273415942064257)
        ·
          refine ⟨258027733022455061956548193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344036977363273415942064257 258027733022455061956548193)
          ·
            refine ⟨193520799766841296467411145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258027733022455061956548193 193520799766841296467411145)
            ·
              refine ⟨145140599825130972350558359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193520799766841296467411145 145140599825130972350558359)
              ·
                refine ⟨217710899737696458525837539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145140599825130972350558359 217710899737696458525837539)
                ·
                  refine ⟨326566349606544687788756309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217710899737696458525837539 326566349606544687788756309)
                  ·
                    refine ⟨478368676181461945003061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 326566349606544687788756309 478368676181461945003061)
                    ·
                      rfl

theorem cell23_2794859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 11].length) (baseStart_2794859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794859 prefixEnd_2794859 := by exact prefixLift 2794859
  have htrace : WordTrace (prefixWord ++ tailWord_2794859) baseStart_2794859 baseEnd_2794859 := by
    simpa [prefixWord, tailWord_2794859, baseEnd_2794859] using wordTrace_append hprefix tailTrace_2794859
  have hstable : (prefixWord ++ tailWord_2794859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794859).length < 2 ^ (prefixWord ++ tailWord_2794859).sum := by decide
  have hdescent : baseEnd_2794859 < baseStart_2794859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794873 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 3]
def baseStart_2794873 : Nat := 118140960795 + 2794873 * 2 ^ 59
def prefixEnd_2794873 : Nat := 4983230072969 + 3 ^ 40 * 2794873 * 2
def baseEnd_2794873 : Nat := 1435113217273548780234119

theorem tailTrace_2794873 : CollatzResearch.WordTrace tailWord_2794873 prefixEnd_2794873 1435113217273548780234119 := by
  unfold tailWord_2794873
  simp only [CollatzResearch.WordTrace]
  refine ⟨101937392803659922151621273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67958261869106614767747515 101937392803659922151621273)
  ·
    refine ⟨76453044602744941613715955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101937392803659922151621273 76453044602744941613715955)
    ·
      refine ⟨114679566904117412420573933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76453044602744941613715955 114679566904117412420573933)
      ·
        refine ⟨43004837589044029657715225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114679566904117412420573933 43004837589044029657715225)
        ·
          refine ⟨32253628191783022243286419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43004837589044029657715225 32253628191783022243286419)
          ·
            refine ⟨48380442287674533364929629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32253628191783022243286419 48380442287674533364929629)
            ·
              refine ⟨18142665857877950011848611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48380442287674533364929629 18142665857877950011848611)
              ·
                refine ⟨27213998786816925017772917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18142665857877950011848611 27213998786816925017772917)
                ·
                  refine ⟨2551312386264086720416211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27213998786816925017772917 2551312386264086720416211)
                  ·
                    refine ⟨3826968579396130080624317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2551312386264086720416211 3826968579396130080624317)
                    ·
                      refine ⟨1435113217273548780234119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3826968579396130080624317 1435113217273548780234119)
                      ·
                        rfl

theorem cell23_2794873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_2794873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794873 prefixEnd_2794873 := by exact prefixLift 2794873
  have htrace : WordTrace (prefixWord ++ tailWord_2794873) baseStart_2794873 baseEnd_2794873 := by
    simpa [prefixWord, tailWord_2794873, baseEnd_2794873] using wordTrace_append hprefix tailTrace_2794873
  have hstable : (prefixWord ++ tailWord_2794873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794873).length < 2 ^ (prefixWord ++ tailWord_2794873).sum := by decide
  have hdescent : baseEnd_2794873 < baseStart_2794873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794876 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_2794876 : Nat := 118140960795 + 2794876 * 2 ^ 59
def prefixEnd_2794876 : Nat := 4983230072969 + 3 ^ 40 * 2794876 * 2
def baseEnd_2794876 : Nat := 478371585905170756165535

theorem tailTrace_2794876 : CollatzResearch.WordTrace tailWord_2794876 prefixEnd_2794876 478371585905170756165535 := by
  unfold tailWord_2794876
  simp only [CollatzResearch.WordTrace]
  refine ⟨50968751111324526831990241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67958334815099369109320321 50968751111324526831990241)
  ·
    refine ⟨38226563333493395123992681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50968751111324526831990241 38226563333493395123992681)
    ·
      refine ⟨28669922500120046342994511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38226563333493395123992681 28669922500120046342994511)
      ·
        refine ⟨43004883750180069514491767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28669922500120046342994511 43004883750180069514491767)
        ·
          refine ⟨64507325625270104271737651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43004883750180069514491767 64507325625270104271737651)
          ·
            refine ⟨96760988437905156407606477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64507325625270104271737651 96760988437905156407606477)
            ·
              refine ⟨36285370664214433652852429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96760988437905156407606477 36285370664214433652852429)
              ·
                refine ⟨13607013999080412619819661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36285370664214433652852429 13607013999080412619819661)
                ·
                  refine ⟨5102630249655154732432373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13607013999080412619819661 5102630249655154732432373)
                  ·
                    refine ⟨478371585905170756165535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5102630249655154732432373 478371585905170756165535)
                    ·
                      rfl

theorem cell23_2794876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_2794876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794876 prefixEnd_2794876 := by exact prefixLift 2794876
  have htrace : WordTrace (prefixWord ++ tailWord_2794876) baseStart_2794876 baseEnd_2794876 := by
    simpa [prefixWord, tailWord_2794876, baseEnd_2794876] using wordTrace_append hprefix tailTrace_2794876
  have hstable : (prefixWord ++ tailWord_2794876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794876).length < 2 ^ (prefixWord ++ tailWord_2794876).sum := by decide
  have hdescent : baseEnd_2794876 < baseStart_2794876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794930 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_2794930 : Nat := 118140960795 + 2794930 * 2 ^ 59
def prefixEnd_2794930 : Nat := 4983230072969 + 3 ^ 40 * 2794930 * 2
def baseEnd_2794930 : Nat := 1435142485670855057221357

theorem tailTrace_2794930 : CollatzResearch.WordTrace tailWord_2794930 prefixEnd_2794930 1435142485670855057221357 := by
  unfold tailWord_2794930
  simp only [CollatzResearch.WordTrace]
  refine ⟨25484867941113355221611561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67959647842968947257630829 25484867941113355221611561)
  ·
    refine ⟨19113650955835016416208671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25484867941113355221611561 19113650955835016416208671)
    ·
      refine ⟨28670476433752524624313007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19113650955835016416208671 28670476433752524624313007)
      ·
        refine ⟨43005714650628786936469511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28670476433752524624313007 43005714650628786936469511)
        ·
          refine ⟨64508571975943180404704267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43005714650628786936469511 64508571975943180404704267)
          ·
            refine ⟨96762857963914770607056401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64508571975943180404704267 96762857963914770607056401)
            ·
              refine ⟨72572143472936077955292301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96762857963914770607056401 72572143472936077955292301)
              ·
                refine ⟨27214553802351029233234613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72572143472936077955292301 27214553802351029233234613)
                ·
                  refine ⟨2551364418970408990615745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27214553802351029233234613 2551364418970408990615745)
                  ·
                    refine ⟨1913523314227806742961809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2551364418970408990615745 1913523314227806742961809)
                    ·
                      refine ⟨1435142485670855057221357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913523314227806742961809 1435142485670855057221357)
                      ·
                        rfl

theorem cell23_2794930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_2794930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794930 prefixEnd_2794930 := by exact prefixLift 2794930
  have htrace : WordTrace (prefixWord ++ tailWord_2794930) baseStart_2794930 baseEnd_2794930 := by
    simpa [prefixWord, tailWord_2794930, baseEnd_2794930] using wordTrace_append hprefix tailTrace_2794930
  have hstable : (prefixWord ++ tailWord_2794930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794930).length < 2 ^ (prefixWord ++ tailWord_2794930).sum := by decide
  have hdescent : baseEnd_2794930 < baseStart_2794930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794976 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_2794976 : Nat := 118140960795 + 2794976 * 2 ^ 59
def prefixEnd_2794976 : Nat := 4983230072969 + 3 ^ 40 * 2794976 * 2
def baseEnd_2794976 : Nat := 1435166105780961877246145

theorem tailTrace_2794976 : CollatzResearch.WordTrace tailWord_2794976 prefixEnd_2794976 1435166105780961877246145 := by
  unfold tailWord_2794976
  simp only [CollatzResearch.WordTrace]
  refine ⟨50970574761143385371310391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67960766348191180495080521 50970574761143385371310391)
  ·
    refine ⟨76455862141715078056965587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50970574761143385371310391 76455862141715078056965587)
    ·
      refine ⟨114683793212572617085448381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76455862141715078056965587 114683793212572617085448381)
      ·
        refine ⟨43006422454714731407043143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114683793212572617085448381 43006422454714731407043143)
        ·
          refine ⟨64509633682072097110564715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43006422454714731407043143 64509633682072097110564715)
          ·
            refine ⟨96764450523108145665847073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64509633682072097110564715 96764450523108145665847073)
            ·
              refine ⟨72573337892331109249385305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96764450523108145665847073 72573337892331109249385305)
              ·
                refine ⟨54430003419248331937038979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72573337892331109249385305 54430003419248331937038979)
                ·
                  refine ⟨81645005128872497905558469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54430003419248331937038979 81645005128872497905558469)
                  ·
                    refine ⟨15308438461663593357292213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81645005128872497905558469 15308438461663593357292213)
                    ·
                      refine ⟨1435166105780961877246145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15308438461663593357292213 1435166105780961877246145)
                      ·
                        rfl

theorem cell23_2794976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_2794976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794976 prefixEnd_2794976 := by exact prefixLift 2794976
  have htrace : WordTrace (prefixWord ++ tailWord_2794976) baseStart_2794976 baseEnd_2794976 := by
    simpa [prefixWord, tailWord_2794976, baseEnd_2794976] using wordTrace_append hprefix tailTrace_2794976
  have hstable : (prefixWord ++ tailWord_2794976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794976).length < 2 ^ (prefixWord ++ tailWord_2794976).sum := by decide
  have hdescent : baseEnd_2794976 < baseStart_2794976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794997 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2794997 : Nat := 118140960795 + 2794997 * 2 ^ 59
def prefixEnd_2794997 : Nat := 4983230072969 + 3 ^ 40 * 2794997 * 2
def baseEnd_2794997 : Nat := 1435176888874706295083549

theorem tailTrace_2794997 : CollatzResearch.WordTrace tailWord_2794997 prefixEnd_2794997 1435176888874706295083549 := by
  unfold tailWord_2794997
  simp only [CollatzResearch.WordTrace]
  refine ⟨101941915455210691329135245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67961276970140460886090163 101941915455210691329135245)
  ·
    refine ⟨38228218295704009248425717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101941915455210691329135245 38228218295704009248425717)
    ·
      refine ⟨3583895465222250867039911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38228218295704009248425717 3583895465222250867039911)
      ·
        refine ⟨5375843197833376300559867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583895465222250867039911 5375843197833376300559867)
        ·
          refine ⟨8063764796750064450839801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5375843197833376300559867 8063764796750064450839801)
          ·
            refine ⟨6047823597562548338129851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8063764796750064450839801 6047823597562548338129851)
            ·
              refine ⟨9071735396343822507194777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6047823597562548338129851 9071735396343822507194777)
              ·
                refine ⟨6803801547257866880396083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9071735396343822507194777 6803801547257866880396083)
                ·
                  refine ⟨10205702320886800320594125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6803801547257866880396083 10205702320886800320594125)
                  ·
                    refine ⟨3827138370332550120222797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10205702320886800320594125 3827138370332550120222797)
                    ·
                      refine ⟨1435176888874706295083549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3827138370332550120222797 1435176888874706295083549)
                      ·
                        rfl

theorem cell23_2794997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2794997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2794997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2794997 prefixEnd_2794997 := by exact prefixLift 2794997
  have htrace : WordTrace (prefixWord ++ tailWord_2794997) baseStart_2794997 baseEnd_2794997 := by
    simpa [prefixWord, tailWord_2794997, baseEnd_2794997] using wordTrace_append hprefix tailTrace_2794997
  have hstable : (prefixWord ++ tailWord_2794997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794997).length < 2 ^ (prefixWord ++ tailWord_2794997).sum := by decide
  have hdescent : baseEnd_2794997 < baseStart_2794997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795037 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_2795037 : Nat := 118140960795 + 2795037 * 2 ^ 59
def prefixEnd_2795037 : Nat := 4983230072969 + 3 ^ 40 * 2795037 * 2
def baseEnd_2795037 : Nat := 1435197428100886138583365

theorem tailTrace_2795037 : CollatzResearch.WordTrace tailWord_2795037 prefixEnd_2795037 1435197428100886138583365 := by
  unfold tailWord_2795037
  simp only [CollatzResearch.WordTrace]
  refine ⟨101943374375065778160591365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67962249583377185440394243 101943374375065778160591365)
  ·
    refine ⟨19114382695324833405110881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101943374375065778160591365 19114382695324833405110881)
    ·
      refine ⟨14335787021493625053833161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19114382695324833405110881 14335787021493625053833161)
      ·
        refine ⟨10751840266120218790374871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14335787021493625053833161 10751840266120218790374871)
        ·
          refine ⟨16127760399180328185562307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10751840266120218790374871 16127760399180328185562307)
          ·
            refine ⟨24191640598770492278343461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16127760399180328185562307 24191640598770492278343461)
            ·
              refine ⟨4535932612269467302189399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24191640598770492278343461 4535932612269467302189399)
              ·
                refine ⟨6803898918404200953284099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535932612269467302189399 6803898918404200953284099)
                ·
                  refine ⟨10205848377606301429926149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6803898918404200953284099 10205848377606301429926149)
                  ·
                    refine ⟨1913596570801181518111153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10205848377606301429926149 1913596570801181518111153)
                    ·
                      refine ⟨1435197428100886138583365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913596570801181518111153 1435197428100886138583365)
                      ·
                        rfl

theorem cell23_2795037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_2795037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795037 prefixEnd_2795037 := by exact prefixLift 2795037
  have htrace : WordTrace (prefixWord ++ tailWord_2795037) baseStart_2795037 baseEnd_2795037 := by
    simpa [prefixWord, tailWord_2795037, baseEnd_2795037] using wordTrace_append hprefix tailTrace_2795037
  have hstable : (prefixWord ++ tailWord_2795037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795037).length < 2 ^ (prefixWord ++ tailWord_2795037).sum := by decide
  have hdescent : baseEnd_2795037 < baseStart_2795037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795137 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 3, 4]
def baseStart_2795137 : Nat := 118140960795 + 2795137 * 2 ^ 59
def prefixEnd_2795137 : Nat := 4983230072969 + 3 ^ 40 * 2795137 * 2
def baseEnd_2795137 : Nat := 478416258722111915777635

theorem tailTrace_2795137 : CollatzResearch.WordTrace tailWord_2795137 prefixEnd_2795137 478416258722111915777635 := by
  unfold tailWord_2795137
  simp only [CollatzResearch.WordTrace]
  refine ⟨101947021674703495239231665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67964681116468996826154443 101947021674703495239231665)
  ·
    refine ⟨76460266256027621429423749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101947021674703495239231665 76460266256027621429423749)
    ·
      refine ⟨14336299923005179018016953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76460266256027621429423749 14336299923005179018016953)
      ·
        refine ⟨10752224942253884263512715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14336299923005179018016953 10752224942253884263512715)
        ·
          refine ⟨16128337413380826395269073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10752224942253884263512715 16128337413380826395269073)
          ·
            refine ⟨12096253060035619796451805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16128337413380826395269073 12096253060035619796451805)
            ·
              refine ⟨4536094897513357423669427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12096253060035619796451805 4536094897513357423669427)
              ·
                refine ⟨6804142346270036135504141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536094897513357423669427 6804142346270036135504141)
                ·
                  refine ⟨2551553379851263550814053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6804142346270036135504141 2551553379851263550814053)
                  ·
                    refine ⟨478416258722111915777635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2551553379851263550814053 478416258722111915777635)
                    ·
                      rfl

theorem cell23_2795137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_2795137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795137 prefixEnd_2795137 := by exact prefixLift 2795137
  have htrace : WordTrace (prefixWord ++ tailWord_2795137) baseStart_2795137 baseEnd_2795137 := by
    simpa [prefixWord, tailWord_2795137, baseEnd_2795137] using wordTrace_append hprefix tailTrace_2795137
  have hstable : (prefixWord ++ tailWord_2795137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795137).length < 2 ^ (prefixWord ++ tailWord_2795137).sum := by decide
  have hdescent : baseEnd_2795137 < baseStart_2795137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795164 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2795164 : Nat := 118140960795 + 2795164 * 2 ^ 59
def prefixEnd_2795164 : Nat := 4983230072969 + 3 ^ 40 * 2795164 * 2
def baseEnd_2795164 : Nat := 1435262640144007141695281

theorem tailTrace_2795164 : CollatzResearch.WordTrace tailWord_2795164 prefixEnd_2795164 1435262640144007141695281 := by
  unfold tailWord_2795164
  simp only [CollatzResearch.WordTrace]
  refine ⟨50974003222802839425232273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67965337630403785900309697 50974003222802839425232273)
  ·
    refine ⟨38230502417102129568924205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50974003222802839425232273 38230502417102129568924205)
    ·
      refine ⟨14336438406413298588346577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38230502417102129568924205 14336438406413298588346577)
      ·
        refine ⟨10752328804809973941259933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14336438406413298588346577 10752328804809973941259933)
        ·
          refine ⟨4032123301803740227972475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10752328804809973941259933 4032123301803740227972475)
          ·
            refine ⟨6048184952705610341958713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032123301803740227972475 6048184952705610341958713)
            ·
              refine ⟨4536138714529207756469035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6048184952705610341958713 4536138714529207756469035)
              ·
                refine ⟨6804208071793811634703553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536138714529207756469035 6804208071793811634703553)
                ·
                  refine ⟨5103156053845358726027665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6804208071793811634703553 5103156053845358726027665)
                  ·
                    refine ⟨3827367040384019044520749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5103156053845358726027665 3827367040384019044520749)
                    ·
                      refine ⟨1435262640144007141695281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3827367040384019044520749 1435262640144007141695281)
                      ·
                        rfl

theorem cell23_2795164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2795164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795164 prefixEnd_2795164 := by exact prefixLift 2795164
  have htrace : WordTrace (prefixWord ++ tailWord_2795164) baseStart_2795164 baseEnd_2795164 := by
    simpa [prefixWord, tailWord_2795164, baseEnd_2795164] using wordTrace_append hprefix tailTrace_2795164
  have hstable : (prefixWord ++ tailWord_2795164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795164).length < 2 ^ (prefixWord ++ tailWord_2795164).sum := by decide
  have hdescent : baseEnd_2795164 < baseStart_2795164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795187 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 2, 3, 2]
def baseStart_2795187 : Nat := 118140960795 + 2795187 * 2 ^ 59
def prefixEnd_2795187 : Nat := 4983230072969 + 3 ^ 40 * 2795187 * 2
def baseEnd_2795187 : Nat := 1435274450199060551707675

theorem tailTrace_2795187 : CollatzResearch.WordTrace tailWord_2795187 prefixEnd_2795187 1435274450199060551707675 := by
  unfold tailWord_2795187
  simp only [CollatzResearch.WordTrace]
  refine ⟨101948845324522353778551815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67965896883014902519034543 101948845324522353778551815)
  ·
    refine ⟨152923267986783530667827723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101948845324522353778551815 152923267986783530667827723)
    ·
      refine ⟨229384901980175296001741585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152923267986783530667827723 229384901980175296001741585)
      ·
        refine ⟨172038676485131472001306189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229384901980175296001741585 172038676485131472001306189)
        ·
          refine ⟨64514503681924302000489821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172038676485131472001306189 64514503681924302000489821)
          ·
            refine ⟨24192938880721613250183683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64514503681924302000489821 24192938880721613250183683)
            ·
              refine ⟨36289408321082419875275525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24192938880721613250183683 36289408321082419875275525)
              ·
                refine ⟨6804264060202953726614161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36289408321082419875275525 6804264060202953726614161)
                ·
                  refine ⟨5103198045152215294960621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6804264060202953726614161 5103198045152215294960621)
                  ·
                    refine ⟨1913699266932080735610233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5103198045152215294960621 1913699266932080735610233)
                    ·
                      refine ⟨1435274450199060551707675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913699266932080735610233 1435274450199060551707675)
                      ·
                        rfl

theorem cell23_2795187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 3, 2].length) (baseStart_2795187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795187 prefixEnd_2795187 := by exact prefixLift 2795187
  have htrace : WordTrace (prefixWord ++ tailWord_2795187) baseStart_2795187 baseEnd_2795187 := by
    simpa [prefixWord, tailWord_2795187, baseEnd_2795187] using wordTrace_append hprefix tailTrace_2795187
  have hstable : (prefixWord ++ tailWord_2795187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795187).length < 2 ^ (prefixWord ++ tailWord_2795187).sum := by decide
  have hdescent : baseEnd_2795187 < baseStart_2795187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795200 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_2795200 : Nat := 118140960795 + 2795200 * 2 ^ 59
def prefixEnd_2795200 : Nat := 4983230072969 + 3 ^ 40 * 2795200 * 2
def baseEnd_2795200 : Nat := 1435281125447569000845115

theorem tailTrace_2795200 : CollatzResearch.WordTrace tailWord_2795200 prefixEnd_2795200 1435281125447569000845115 := by
  unfold tailWord_2795200
  simp only [CollatzResearch.WordTrace]
  refine ⟨50974659736737628499387527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67966212982316837999183369 50974659736737628499387527)
  ·
    refine ⟨76461989605106442749081291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50974659736737628499387527 76461989605106442749081291)
    ·
      refine ⟨114692984407659664123621937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76461989605106442749081291 114692984407659664123621937)
      ·
        refine ⟨86019738305744748092716453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114692984407659664123621937 86019738305744748092716453)
        ·
          refine ⟨16128700932327140267384335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86019738305744748092716453 16128700932327140267384335)
          ·
            refine ⟨24193051398490710401076503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16128700932327140267384335 24193051398490710401076503)
            ·
              refine ⟨36289577097736065601614755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24193051398490710401076503 36289577097736065601614755)
              ·
                refine ⟨54434365646604098402422133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36289577097736065601614755 54434365646604098402422133)
                ·
                  refine ⟨5103221779369134225227075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54434365646604098402422133 5103221779369134225227075)
                  ·
                    refine ⟨7654832669053701337840613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5103221779369134225227075 7654832669053701337840613)
                    ·
                      refine ⟨1435281125447569000845115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7654832669053701337840613 1435281125447569000845115)
                      ·
                        rfl

theorem cell23_2795200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_2795200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795200 prefixEnd_2795200 := by exact prefixLift 2795200
  have htrace : WordTrace (prefixWord ++ tailWord_2795200) baseStart_2795200 baseEnd_2795200 := by
    simpa [prefixWord, tailWord_2795200, baseEnd_2795200] using wordTrace_append hprefix tailTrace_2795200
  have hstable : (prefixWord ++ tailWord_2795200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795200).length < 2 ^ (prefixWord ++ tailWord_2795200).sum := by decide
  have hdescent : baseEnd_2795200 < baseStart_2795200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795240 : List Nat := [2, 1, 4, 1, 3, 2, 10]
def baseStart_2795240 : Nat := 118140960795 + 2795240 * 2 ^ 59
def prefixEnd_2795240 : Nat := 4983230072969 + 3 ^ 40 * 2795240 * 2
def baseEnd_2795240 : Nat := 17719773637947516596851

theorem tailTrace_2795240 : CollatzResearch.WordTrace tailWord_2795240 prefixEnd_2795240 17719773637947516596851 := by
  unfold tailWord_2795240
  simp only [CollatzResearch.WordTrace]
  refine ⟨50975389196665171915115587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67967185595553562553487449 50975389196665171915115587)
  ·
    refine ⟨76463083794997757872673381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50975389196665171915115587 76463083794997757872673381)
    ·
      refine ⟨14336828211562079601126259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76463083794997757872673381 14336828211562079601126259)
      ·
        refine ⟨21505242317343119401689389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14336828211562079601126259 21505242317343119401689389)
        ·
          refine ⟨8064465869003669775633521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21505242317343119401689389 8064465869003669775633521)
          ·
            refine ⟨6048349401752752331725141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8064465869003669775633521 6048349401752752331725141)
            ·
              refine ⟨17719773637947516596851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6048349401752752331725141 17719773637947516596851)
              ·
                rfl

theorem cell23_2795240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 10].length) (baseStart_2795240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795240 prefixEnd_2795240 := by exact prefixLift 2795240
  have htrace : WordTrace (prefixWord ++ tailWord_2795240) baseStart_2795240 baseEnd_2795240 := by
    simpa [prefixWord, tailWord_2795240, baseEnd_2795240] using wordTrace_append hprefix tailTrace_2795240
  have hstable : (prefixWord ++ tailWord_2795240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795240).length < 2 ^ (prefixWord ++ tailWord_2795240).sum := by decide
  have hdescent : baseEnd_2795240 < baseStart_2795240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795251 : List Nat := [1, 1, 1, 2, 2, 3, 4, 4, 1, 2, 2]
def baseStart_2795251 : Nat := 118140960795 + 2795251 * 2 ^ 59
def prefixEnd_2795251 : Nat := 4983230072969 + 3 ^ 40 * 2795251 * 2
def baseEnd_2795251 : Nat := 1435307312960948301307381

theorem tailTrace_2795251 : CollatzResearch.WordTrace tailWord_2795251 prefixEnd_2795251 1435307312960948301307381 := by
  unfold tailWord_2795251
  simp only [CollatzResearch.WordTrace]
  refine ⟨101951179596290492708881607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67967453064193661805921071 101951179596290492708881607)
  ·
    refine ⟨152926769394435739063322411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101951179596290492708881607 152926769394435739063322411)
    ·
      refine ⟨229390154091653608594983617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152926769394435739063322411 229390154091653608594983617)
      ·
        refine ⟨172042615568740206446237713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229390154091653608594983617 172042615568740206446237713)
        ·
          refine ⟨129031961676555154834678285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172042615568740206446237713 129031961676555154834678285)
          ·
            refine ⟨48386985628708183063004357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129031961676555154834678285 48386985628708183063004357)
            ·
              refine ⟨9072559805382784324313317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48386985628708183063004357 9072559805382784324313317)
              ·
                refine ⟨1701104963509272060808747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9072559805382784324313317 1701104963509272060808747)
                ·
                  refine ⟨2551657445263908091213121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701104963509272060808747 2551657445263908091213121)
                  ·
                    refine ⟨1913743083947931068409841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2551657445263908091213121 1913743083947931068409841)
                    ·
                      refine ⟨1435307312960948301307381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913743083947931068409841 1435307312960948301307381)
                      ·
                        rfl

theorem cell23_2795251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 2, 2].length) (baseStart_2795251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795251 prefixEnd_2795251 := by exact prefixLift 2795251
  have htrace : WordTrace (prefixWord ++ tailWord_2795251) baseStart_2795251 baseEnd_2795251 := by
    simpa [prefixWord, tailWord_2795251, baseEnd_2795251] using wordTrace_append hprefix tailTrace_2795251
  have hstable : (prefixWord ++ tailWord_2795251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795251).length < 2 ^ (prefixWord ++ tailWord_2795251).sum := by decide
  have hdescent : baseEnd_2795251 < baseStart_2795251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795267 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 3]
def baseStart_2795267 : Nat := 118140960795 + 2795267 * 2 ^ 59
def prefixEnd_2795267 : Nat := 4983230072969 + 3 ^ 40 * 2795267 * 2
def baseEnd_2795267 : Nat := 1435315528651420238707307

theorem tailTrace_2795267 : CollatzResearch.WordTrace tailWord_2795267 prefixEnd_2795267 1435315528651420238707307 := by
  unfold tailWord_2795267
  simp only [CollatzResearch.WordTrace]
  refine ⟨101951763164232527441464055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67967842109488351627642703 101951763164232527441464055)
  ·
    refine ⟨152927644746348791162196083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101951763164232527441464055 152927644746348791162196083)
    ·
      refine ⟨229391467119523186743294125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152927644746348791162196083 229391467119523186743294125)
      ·
        refine ⟨86021800169821195028735297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229391467119523186743294125 86021800169821195028735297)
        ·
          refine ⟨64516350127365896271551473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86021800169821195028735297 64516350127365896271551473)
          ·
            refine ⟨48387262595524422203663605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64516350127365896271551473 48387262595524422203663605)
            ·
              refine ⟨4536305868330414581593463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48387262595524422203663605 4536305868330414581593463)
              ·
                refine ⟨6804458802495621872390195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536305868330414581593463 6804458802495621872390195)
                ·
                  refine ⟨10206688203743432808585293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6804458802495621872390195 10206688203743432808585293)
                  ·
                    refine ⟨3827508076403787303219485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10206688203743432808585293 3827508076403787303219485)
                    ·
                      refine ⟨1435315528651420238707307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3827508076403787303219485 1435315528651420238707307)
                      ·
                        rfl

theorem cell23_2795267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_2795267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795267 prefixEnd_2795267 := by exact prefixLift 2795267
  have htrace : WordTrace (prefixWord ++ tailWord_2795267) baseStart_2795267 baseEnd_2795267 := by
    simpa [prefixWord, tailWord_2795267, baseEnd_2795267] using wordTrace_append hprefix tailTrace_2795267
  have hstable : (prefixWord ++ tailWord_2795267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795267).length < 2 ^ (prefixWord ++ tailWord_2795267).sum := by decide
  have hdescent : baseEnd_2795267 < baseStart_2795267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795271 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2795271 : Nat := 118140960795 + 2795271 * 2 ^ 59
def prefixEnd_2795271 : Nat := 4983230072969 + 3 ^ 40 * 2795271 * 2
def baseEnd_2795271 : Nat := 1435317582574038223057289

theorem tailTrace_2795271 : CollatzResearch.WordTrace tailWord_2795271 prefixEnd_2795271 1435317582574038223057289 := by
  unfold tailWord_2795271
  simp only [CollatzResearch.WordTrace]
  refine ⟨101951909056218036124609667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67967939370812024083073111 101951909056218036124609667)
  ·
    refine ⟨152927863584327054186914501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101951909056218036124609667 152927863584327054186914501)
    ·
      refine ⟨28673974422061322660046469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152927863584327054186914501 28673974422061322660046469)
      ·
        refine ⟨5376370204136497998758713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28673974422061322660046469 5376370204136497998758713)
        ·
          refine ⟨4032277653102373499069035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5376370204136497998758713 4032277653102373499069035)
          ·
            refine ⟨6048416479653560248603553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032277653102373499069035 6048416479653560248603553)
            ·
              refine ⟨4536312359740170186452665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6048416479653560248603553 4536312359740170186452665)
              ·
                refine ⟨3402234269805127639839499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4536312359740170186452665 3402234269805127639839499)
                ·
                  refine ⟨5103351404707691459759249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3402234269805127639839499 5103351404707691459759249)
                  ·
                    refine ⟨3827513553530768594819437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5103351404707691459759249 3827513553530768594819437)
                    ·
                      refine ⟨1435317582574038223057289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3827513553530768594819437 1435317582574038223057289)
                      ·
                        rfl

theorem cell23_2795271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2795271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795271 prefixEnd_2795271 := by exact prefixLift 2795271
  have htrace : WordTrace (prefixWord ++ tailWord_2795271) baseStart_2795271 baseEnd_2795271 := by
    simpa [prefixWord, tailWord_2795271, baseEnd_2795271] using wordTrace_append hprefix tailTrace_2795271
  have hstable : (prefixWord ++ tailWord_2795271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795271).length < 2 ^ (prefixWord ++ tailWord_2795271).sum := by decide
  have hdescent : baseEnd_2795271 < baseStart_2795271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795318 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2795318 : Nat := 118140960795 + 2795318 * 2 ^ 59
def prefixEnd_2795318 : Nat := 4983230072969 + 3 ^ 40 * 2795318 * 2
def baseEnd_2795318 : Nat := 1435341716164799539169573

theorem tailTrace_2795318 : CollatzResearch.WordTrace tailWord_2795318 prefixEnd_2795318 1435341716164799539169573 := by
  unfold tailWord_2795318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6372101455440485196973163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67969082191365175434380405 6372101455440485196973163)
  ·
    refine ⟨9558152183160727795459745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6372101455440485196973163 9558152183160727795459745)
    ·
      refine ⟨7168614137370545846594809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9558152183160727795459745 7168614137370545846594809)
      ·
        refine ⟨5376460603027909384946107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7168614137370545846594809 5376460603027909384946107)
        ·
          refine ⟨8064690904541864077419161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5376460603027909384946107 8064690904541864077419161)
          ·
            refine ⟨6048518178406398058064371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8064690904541864077419161 6048518178406398058064371)
            ·
              refine ⟨9072777267609597087096557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6048518178406398058064371 9072777267609597087096557)
              ·
                refine ⟨3402291475353598907661209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9072777267609597087096557 3402291475353598907661209)
                ·
                  refine ⟨2551718606515199180745907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402291475353598907661209 2551718606515199180745907)
                  ·
                    refine ⟨3827577909772798771118861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2551718606515199180745907 3827577909772798771118861)
                    ·
                      refine ⟨1435341716164799539169573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3827577909772798771118861 1435341716164799539169573)
                      ·
                        rfl

theorem cell23_2795318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2795318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795318 prefixEnd_2795318 := by exact prefixLift 2795318
  have htrace : WordTrace (prefixWord ++ tailWord_2795318) baseStart_2795318 baseEnd_2795318 := by
    simpa [prefixWord, tailWord_2795318, baseEnd_2795318] using wordTrace_append hprefix tailTrace_2795318
  have hstable : (prefixWord ++ tailWord_2795318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795318).length < 2 ^ (prefixWord ++ tailWord_2795318).sum := by decide
  have hdescent : baseEnd_2795318 < baseStart_2795318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795341 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_2795341 : Nat := 118140960795 + 2795341 * 2 ^ 59
def prefixEnd_2795341 : Nat := 4983230072969 + 3 ^ 40 * 2795341 * 2
def baseEnd_2795341 : Nat := 1435353526219852949181967

theorem tailTrace_2795341 : CollatzResearch.WordTrace tailWord_2795341 prefixEnd_2795341 1435353526219852949181967 := by
  unfold tailWord_2795341
  simp only [CollatzResearch.WordTrace]
  refine ⟨101954462165964438079657877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67969641443976292053105251 101954462165964438079657877)
  ·
    refine ⟨4779115414029583034983963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101954462165964438079657877 4779115414029583034983963)
    ·
      refine ⟨7168673121044374552475945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4779115414029583034983963 7168673121044374552475945)
      ·
        refine ⟨5376504840783280914356959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7168673121044374552475945 5376504840783280914356959)
        ·
          refine ⟨8064757261174921371535439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5376504840783280914356959 8064757261174921371535439)
          ·
            refine ⟨12097135891762382057303159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8064757261174921371535439 12097135891762382057303159)
            ·
              refine ⟨18145703837643573085954739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12097135891762382057303159 18145703837643573085954739)
              ·
                refine ⟨27218555756465359628932109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18145703837643573085954739 27218555756465359628932109)
                ·
                  refine ⟨10206958408674509860849541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27218555756465359628932109 10206958408674509860849541)
                  ·
                    refine ⟨1913804701626470598909289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10206958408674509860849541 1913804701626470598909289)
                    ·
                      refine ⟨1435353526219852949181967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913804701626470598909289 1435353526219852949181967)
                      ·
                        rfl

theorem cell23_2795341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_2795341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795341 prefixEnd_2795341 := by exact prefixLift 2795341
  have htrace : WordTrace (prefixWord ++ tailWord_2795341) baseStart_2795341 baseEnd_2795341 := by
    simpa [prefixWord, tailWord_2795341, baseEnd_2795341] using wordTrace_append hprefix tailTrace_2795341
  have hstable : (prefixWord ++ tailWord_2795341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795341).length < 2 ^ (prefixWord ++ tailWord_2795341).sum := by decide
  have hdescent : baseEnd_2795341 < baseStart_2795341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795374 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2795374 : Nat := 118140960795 + 2795374 * 2 ^ 59
def prefixEnd_2795374 : Nat := 4983230072969 + 3 ^ 40 * 2795374 * 2
def baseEnd_2795374 : Nat := 1435370471081451320069315

theorem tailTrace_2795374 : CollatzResearch.WordTrace tailWord_2795374 prefixEnd_2795374 1435370471081451320069315 := by
  unfold tailWord_2795374
  simp only [CollatzResearch.WordTrace]
  refine ⟨12744458221855610589451147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67970443849896589810406117 12744458221855610589451147)
  ·
    refine ⟨19116687332783415884176721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12744458221855610589451147 19116687332783415884176721)
    ·
      refine ⟨14337515499587561913132541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19116687332783415884176721 14337515499587561913132541)
      ·
        refine ⟨5376568312345335717424703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14337515499587561913132541 5376568312345335717424703)
        ·
          refine ⟨8064852468518003576137055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5376568312345335717424703 8064852468518003576137055)
          ·
            refine ⟨12097278702777005364205583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8064852468518003576137055 12097278702777005364205583)
            ·
              refine ⟨18145918054165508046308375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12097278702777005364205583 18145918054165508046308375)
              ·
                refine ⟨27218877081248262069462563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18145918054165508046308375 27218877081248262069462563)
                ·
                  refine ⟨40828315621872393104193845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27218877081248262069462563 40828315621872393104193845)
                  ·
                    refine ⟨3827654589550536853518173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40828315621872393104193845 3827654589550536853518173)
                    ·
                      refine ⟨1435370471081451320069315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3827654589550536853518173 1435370471081451320069315)
                      ·
                        rfl

theorem cell23_2795374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2795374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795374 prefixEnd_2795374 := by exact prefixLift 2795374
  have htrace : WordTrace (prefixWord ++ tailWord_2795374) baseStart_2795374 baseEnd_2795374 := by
    simpa [prefixWord, tailWord_2795374, baseEnd_2795374] using wordTrace_append hprefix tailTrace_2795374
  have hstable : (prefixWord ++ tailWord_2795374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795374).length < 2 ^ (prefixWord ++ tailWord_2795374).sum := by decide
  have hdescent : baseEnd_2795374 < baseStart_2795374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795397 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_2795397 : Nat := 118140960795 + 2795397 * 2 ^ 59
def prefixEnd_2795397 : Nat := 4983230072969 + 3 ^ 40 * 2795397 * 2
def baseEnd_2795397 : Nat := 1435382281136504730081709

theorem tailTrace_2795397 : CollatzResearch.WordTrace tailWord_2795397 prefixEnd_2795397 1435382281136504730081709 := by
  unfold tailWord_2795397
  simp only [CollatzResearch.WordTrace]
  refine ⟨101956504653761559643696445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67971003102507706429130963 101956504653761559643696445)
  ·
    refine ⟨38233689245160584866386167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101956504653761559643696445 38233689245160584866386167)
    ·
      refine ⟨57350533867740877299579251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38233689245160584866386167 57350533867740877299579251)
      ·
        refine ⟨86025800801611315949368877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57350533867740877299579251 86025800801611315949368877)
        ·
          refine ⟨32259675300604243481013329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86025800801611315949368877 32259675300604243481013329)
          ·
            refine ⟨24194756475453182610759997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32259675300604243481013329 24194756475453182610759997)
            ·
              refine ⟨9073033678294943479034999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24194756475453182610759997 9073033678294943479034999)
              ·
                refine ⟨13609550517442415218552499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9073033678294943479034999 13609550517442415218552499)
                ·
                  refine ⟨20414325776163622827828749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13609550517442415218552499 20414325776163622827828749)
                  ·
                    refine ⟨7655372166061358560435781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20414325776163622827828749 7655372166061358560435781)
                    ·
                      refine ⟨1435382281136504730081709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7655372166061358560435781 1435382281136504730081709)
                      ·
                        rfl

theorem cell23_2795397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_2795397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795397 prefixEnd_2795397 := by exact prefixLift 2795397
  have htrace : WordTrace (prefixWord ++ tailWord_2795397) baseStart_2795397 baseEnd_2795397 := by
    simpa [prefixWord, tailWord_2795397, baseEnd_2795397] using wordTrace_append hprefix tailTrace_2795397
  have hstable : (prefixWord ++ tailWord_2795397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795397).length < 2 ^ (prefixWord ++ tailWord_2795397).sum := by decide
  have hdescent : baseEnd_2795397 < baseStart_2795397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795431 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_2795431 : Nat := 118140960795 + 2795431 * 2 ^ 59
def prefixEnd_2795431 : Nat := 4983230072969 + 3 ^ 40 * 2795431 * 2
def baseEnd_2795431 : Nat := 1435399739478757597056553

theorem tailTrace_2795431 : CollatzResearch.WordTrace tailWord_2795431 prefixEnd_2795431 1435399739478757597056553 := by
  unfold tailWord_2795431
  simp only [CollatzResearch.WordTrace]
  refine ⟨101957744735638383450434147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67971829823758922300289431 101957744735638383450434147)
  ·
    refine ⟨152936617103457575175651221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101957744735638383450434147 152936617103457575175651221)
    ·
      refine ⟨7168903926724573836358651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152936617103457575175651221 7168903926724573836358651)
      ·
        refine ⟨10753355890086860754537977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7168903926724573836358651 10753355890086860754537977)
        ·
          refine ⟨8065016917565145565903483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10753355890086860754537977 8065016917565145565903483)
          ·
            refine ⟨12097525376347718348855225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8065016917565145565903483 12097525376347718348855225)
            ·
              refine ⟨9073144032260788761641419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12097525376347718348855225 9073144032260788761641419)
              ·
                refine ⟨13609716048391183142462129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9073144032260788761641419 13609716048391183142462129)
                ·
                  refine ⟨10207287036293387356846597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13609716048391183142462129 10207287036293387356846597)
                  ·
                    refine ⟨1913866319305010129408737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10207287036293387356846597 1913866319305010129408737)
                    ·
                      refine ⟨1435399739478757597056553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913866319305010129408737 1435399739478757597056553)
                      ·
                        rfl

theorem cell23_2795431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_2795431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795431 prefixEnd_2795431 := by exact prefixLift 2795431
  have htrace : WordTrace (prefixWord ++ tailWord_2795431) baseStart_2795431 baseEnd_2795431 := by
    simpa [prefixWord, tailWord_2795431, baseEnd_2795431] using wordTrace_append hprefix tailTrace_2795431
  have hstable : (prefixWord ++ tailWord_2795431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795431).length < 2 ^ (prefixWord ++ tailWord_2795431).sum := by decide
  have hdescent : baseEnd_2795431 < baseStart_2795431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795447 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_2795447 : Nat := 118140960795 + 2795447 * 2 ^ 59
def prefixEnd_2795447 : Nat := 4983230072969 + 3 ^ 40 * 2795447 * 2
def baseEnd_2795447 : Nat := 1435407955169229534456479

theorem tailTrace_2795447 : CollatzResearch.WordTrace tailWord_2795447 prefixEnd_2795447 1435407955169229534456479 := by
  unfold tailWord_2795447
  simp only [CollatzResearch.WordTrace]
  refine ⟨101958328303580418183016595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67972218869053612122011063 101958328303580418183016595)
  ·
    refine ⟨152937492455370627274524893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101958328303580418183016595 152937492455370627274524893)
    ·
      refine ⟨57351559670763985227946835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152937492455370627274524893 57351559670763985227946835)
      ·
        refine ⟨86027339506145977841920253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57351559670763985227946835 86027339506145977841920253)
        ·
          refine ⟨32260252314804741690720095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86027339506145977841920253 32260252314804741690720095)
          ·
            refine ⟨48390378472207112536080143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32260252314804741690720095 48390378472207112536080143)
            ·
              refine ⟨72585567708310668804120215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48390378472207112536080143 72585567708310668804120215)
              ·
                refine ⟨108878351562466003206180323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72585567708310668804120215 108878351562466003206180323)
                ·
                  refine ⟨163317527343699004809270485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108878351562466003206180323 163317527343699004809270485)
                  ·
                    refine ⟨3827754547117945425217277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 163317527343699004809270485 3827754547117945425217277)
                    ·
                      refine ⟨1435407955169229534456479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3827754547117945425217277 1435407955169229534456479)
                      ·
                        rfl

theorem cell23_2795447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_2795447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795447 prefixEnd_2795447 := by exact prefixLift 2795447
  have htrace : WordTrace (prefixWord ++ tailWord_2795447) baseStart_2795447 baseEnd_2795447 := by
    simpa [prefixWord, tailWord_2795447, baseEnd_2795447] using wordTrace_append hprefix tailTrace_2795447
  have hstable : (prefixWord ++ tailWord_2795447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795447).length < 2 ^ (prefixWord ++ tailWord_2795447).sum := by decide
  have hdescent : baseEnd_2795447 < baseStart_2795447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795504 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 2, 6, 2]
def baseStart_2795504 : Nat := 118140960795 + 2795504 * 2 ^ 59
def prefixEnd_2795504 : Nat := 4983230072969 + 3 ^ 40 * 2795504 * 2
def baseEnd_2795504 : Nat := 1435437223566535811443717

theorem tailTrace_2795504 : CollatzResearch.WordTrace tailWord_2795504 prefixEnd_2795504 1435437223566535811443717 := by
  unfold tailWord_2795504
  simp only [CollatzResearch.WordTrace]
  refine ⟨50980203632186958458920783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67973604842915944611894377 50980203632186958458920783)
  ·
    refine ⟨76470305448280437688381175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50980203632186958458920783 76470305448280437688381175)
    ·
      refine ⟨114705458172420656532571763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76470305448280437688381175 114705458172420656532571763)
      ·
        refine ⟨172058187258630984798857645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114705458172420656532571763 172058187258630984798857645)
        ·
          refine ⟨64521820221986619299571617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172058187258630984798857645 64521820221986619299571617)
          ·
            refine ⟨48391365166489964474678713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64521820221986619299571617 48391365166489964474678713)
            ·
              refine ⟨36293523874867473356009035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48391365166489964474678713 36293523874867473356009035)
              ·
                refine ⟨54440285812301210034013553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36293523874867473356009035 54440285812301210034013553)
                ·
                  refine ⟨40830214359225907525510165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54440285812301210034013553 40830214359225907525510165)
                  ·
                    refine ⟨1913916298088714415258289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40830214359225907525510165 1913916298088714415258289)
                    ·
                      refine ⟨1435437223566535811443717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1913916298088714415258289 1435437223566535811443717)
                      ·
                        rfl

theorem cell23_2795504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 6, 2].length) (baseStart_2795504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795504 prefixEnd_2795504 := by exact prefixLift 2795504
  have htrace : WordTrace (prefixWord ++ tailWord_2795504) baseStart_2795504 baseEnd_2795504 := by
    simpa [prefixWord, tailWord_2795504, baseEnd_2795504] using wordTrace_append hprefix tailTrace_2795504
  have hstable : (prefixWord ++ tailWord_2795504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795504).length < 2 ^ (prefixWord ++ tailWord_2795504).sum := by decide
  have hdescent : baseEnd_2795504 < baseStart_2795504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795507 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 5]
def baseStart_2795507 : Nat := 118140960795 + 2795507 * 2 ^ 59
def prefixEnd_2795507 : Nat := 4983230072969 + 3 ^ 40 * 2795507 * 2
def baseEnd_2795507 : Nat := 1435438764008499299706203

theorem tailTrace_2795507 : CollatzResearch.WordTrace tailWord_2795507 prefixEnd_2795507 1435438764008499299706203 := by
  unfold tailWord_2795507
  simp only [CollatzResearch.WordTrace]
  refine ⟨101960516683363048430200775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67973677788908698953467183 101960516683363048430200775)
  ·
    refine ⟨152940775025044572645301163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101960516683363048430200775 152940775025044572645301163)
    ·
      refine ⟨229411162537566858967951745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152940775025044572645301163 229411162537566858967951745)
      ·
        refine ⟨172058371903175144225963809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229411162537566858967951745 172058371903175144225963809)
        ·
          refine ⟨129043778927381358169472857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172058371903175144225963809 129043778927381358169472857)
          ·
            refine ⟨96782834195536018627104643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129043778927381358169472857 96782834195536018627104643)
            ·
              refine ⟨145174251293304027940656965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96782834195536018627104643 145174251293304027940656965)
              ·
                refine ⟨27220172117494505238873181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145174251293304027940656965 27220172117494505238873181)
                ·
                  refine ⟨10207564544060439464577443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27220172117494505238873181 10207564544060439464577443)
                  ·
                    refine ⟨15311346816090659196866165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10207564544060439464577443 15311346816090659196866165)
                    ·
                      refine ⟨1435438764008499299706203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15311346816090659196866165 1435438764008499299706203)
                      ·
                        rfl

theorem cell23_2795507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_2795507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795507 prefixEnd_2795507 := by exact prefixLift 2795507
  have htrace : WordTrace (prefixWord ++ tailWord_2795507) baseStart_2795507 baseEnd_2795507 := by
    simpa [prefixWord, tailWord_2795507, baseEnd_2795507] using wordTrace_append hprefix tailTrace_2795507
  have hstable : (prefixWord ++ tailWord_2795507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795507).length < 2 ^ (prefixWord ++ tailWord_2795507).sum := by decide
  have hdescent : baseEnd_2795507 < baseStart_2795507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795527 : List Nat := [1, 1, 4, 3, 1, 13]
def baseStart_2795527 : Nat := 118140960795 + 2795527 * 2 ^ 59
def prefixEnd_2795527 : Nat := 4983230072969 + 3 ^ 40 * 2795527 * 2
def baseEnd_2795527 : Nat := 5907197669224647001877

theorem tailTrace_2795527 : CollatzResearch.WordTrace tailWord_2795527 prefixEnd_2795527 5907197669224647001877 := by
  unfold tailWord_2795527
  simp only [CollatzResearch.WordTrace]
  refine ⟨101961246143290591845928835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67974164095527061230619223 101961246143290591845928835)
  ·
    refine ⟨152941869214935887768893253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101961246143290591845928835 152941869214935887768893253)
    ·
      refine ⟨28676600477800478956667485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152941869214935887768893253 28676600477800478956667485)
      ·
        refine ⟨10753725179175179608750307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28676600477800478956667485 10753725179175179608750307)
        ·
          refine ⟨16130587768762769413125461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10753725179175179608750307 16130587768762769413125461)
          ·
            refine ⟨5907197669224647001877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 16130587768762769413125461 5907197669224647001877)
            ·
              rfl

theorem cell23_2795527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 13].length) (baseStart_2795527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795527 prefixEnd_2795527 := by exact prefixLift 2795527
  have htrace : WordTrace (prefixWord ++ tailWord_2795527) baseStart_2795527 baseEnd_2795527 := by
    simpa [prefixWord, tailWord_2795527, baseEnd_2795527] using wordTrace_append hprefix tailTrace_2795527
  have hstable : (prefixWord ++ tailWord_2795527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795527).length < 2 ^ (prefixWord ++ tailWord_2795527).sum := by decide
  have hdescent : baseEnd_2795527 < baseStart_2795527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795531 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 2, 4]
def baseStart_2795531 : Nat := 118140960795 + 2795531 * 2 ^ 59
def prefixEnd_2795531 : Nat := 4983230072969 + 3 ^ 40 * 2795531 * 2
def baseEnd_2795531 : Nat := 478483695848069068602031

theorem tailTrace_2795531 : CollatzResearch.WordTrace tailWord_2795531 prefixEnd_2795531 478483695848069068602031 := by
  unfold tailWord_2795531
  simp only [CollatzResearch.WordTrace]
  refine ⟨101961392035276100529074447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67974261356850733686049631 101961392035276100529074447)
  ·
    refine ⟨152942088052914150793611671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101961392035276100529074447 152942088052914150793611671)
    ·
      refine ⟨229413132079371226190417507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152942088052914150793611671 229413132079371226190417507)
      ·
        refine ⟨344119698119056839285626261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229413132079371226190417507 344119698119056839285626261)
        ·
          refine ⟨16130610849330789341513731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 344119698119056839285626261 16130610849330789341513731)
          ·
            refine ⟨24195916273996184012270597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16130610849330789341513731 24195916273996184012270597)
            ·
              refine ⟨4536734301374284502300737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24195916273996184012270597 4536734301374284502300737)
              ·
                refine ⟨3402550726030713376725553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4536734301374284502300737 3402550726030713376725553)
                ·
                  refine ⟨2551913044523035032544165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402550726030713376725553 2551913044523035032544165)
                  ·
                    refine ⟨478483695848069068602031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2551913044523035032544165 478483695848069068602031)
                    ·
                      rfl

theorem cell23_2795531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 4].length) (baseStart_2795531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795531 prefixEnd_2795531 := by exact prefixLift 2795531
  have htrace : WordTrace (prefixWord ++ tailWord_2795531) baseStart_2795531 baseEnd_2795531 := by
    simpa [prefixWord, tailWord_2795531, baseEnd_2795531] using wordTrace_append hprefix tailTrace_2795531
  have hstable : (prefixWord ++ tailWord_2795531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795531).length < 2 ^ (prefixWord ++ tailWord_2795531).sum := by decide
  have hdescent : baseEnd_2795531 < baseStart_2795531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795534 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2795534 : Nat := 118140960795 + 2795534 * 2 ^ 59
def prefixEnd_2795534 : Nat := 4983230072969 + 3 ^ 40 * 2795534 * 2
def baseEnd_2795534 : Nat := 1435452627986170694068579

theorem tailTrace_2795534 : CollatzResearch.WordTrace tailWord_2795534 prefixEnd_2795534 1435452627986170694068579 := by
  unfold tailWord_2795534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745187681783154005179207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67974334302843488027622437 12745187681783154005179207)
  ·
    refine ⟨19117781522674731007768811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12745187681783154005179207 19117781522674731007768811)
    ·
      refine ⟨28676672284012096511653217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19117781522674731007768811 28676672284012096511653217)
      ·
        refine ⟨21507504213009072383739913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28676672284012096511653217 21507504213009072383739913)
        ·
          refine ⟨16130628159756804287804935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21507504213009072383739913 16130628159756804287804935)
          ·
            refine ⟨24195942239635206431707403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16130628159756804287804935 24195942239635206431707403)
            ·
              refine ⟨36293913359452809647561105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24195942239635206431707403 36293913359452809647561105)
              ·
                refine ⟨27220435019589607235670829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36293913359452809647561105 27220435019589607235670829)
                ·
                  refine ⟨10207663132346102713376561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27220435019589607235670829 10207663132346102713376561)
                  ·
                    refine ⟨7655747349259577035032421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10207663132346102713376561 7655747349259577035032421)
                    ·
                      refine ⟨1435452627986170694068579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7655747349259577035032421 1435452627986170694068579)
                      ·
                        rfl

theorem cell23_2795534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2795534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795534 prefixEnd_2795534 := by exact prefixLift 2795534
  have htrace : WordTrace (prefixWord ++ tailWord_2795534) baseStart_2795534 baseEnd_2795534 := by
    simpa [prefixWord, tailWord_2795534, baseEnd_2795534] using wordTrace_append hprefix tailTrace_2795534
  have hstable : (prefixWord ++ tailWord_2795534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795534).length < 2 ^ (prefixWord ++ tailWord_2795534).sum := by decide
  have hdescent : baseEnd_2795534 < baseStart_2795534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795572 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_2795572 : Nat := 118140960795 + 2795572 * 2 ^ 59
def prefixEnd_2795572 : Nat := 4983230072969 + 3 ^ 40 * 2795572 * 2
def baseEnd_2795572 : Nat := 1435472140251041545393405

theorem tailTrace_2795572 : CollatzResearch.WordTrace tailWord_2795572 prefixEnd_2795572 1435472140251041545393405 := by
  unfold tailWord_2795572
  simp only [CollatzResearch.WordTrace]
  refine ⟨50981443714063782265658485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67975258285418376354211313 50981443714063782265658485)
  ·
    refine ⟨4779510348193479587405483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50981443714063782265658485 4779510348193479587405483)
    ·
      refine ⟨7169265522290219381108225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4779510348193479587405483 7169265522290219381108225)
      ·
        refine ⟨5376949141717664535831169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7169265522290219381108225 5376949141717664535831169)
        ·
          refine ⟨4032711856288248401873377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5376949141717664535831169 4032711856288248401873377)
          ·
            refine ⟨3024533892216186301405033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4032711856288248401873377 3024533892216186301405033)
            ·
              refine ⟨2268400419162139726053775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3024533892216186301405033 2268400419162139726053775)
              ·
                refine ⟨3402600628743209589080663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268400419162139726053775 3402600628743209589080663)
                ·
                  refine ⟨5103900943114814383620995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3402600628743209589080663 5103900943114814383620995)
                  ·
                    refine ⟨7655851414672221575431493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5103900943114814383620995 7655851414672221575431493)
                    ·
                      refine ⟨1435472140251041545393405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7655851414672221575431493 1435472140251041545393405)
                      ·
                        rfl

theorem cell23_2795572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_2795572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795572 prefixEnd_2795572 := by exact prefixLift 2795572
  have htrace : WordTrace (prefixWord ++ tailWord_2795572) baseStart_2795572 baseEnd_2795572 := by
    simpa [prefixWord, tailWord_2795572, baseEnd_2795572] using wordTrace_append hprefix tailTrace_2795572
  have hstable : (prefixWord ++ tailWord_2795572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795572).length < 2 ^ (prefixWord ++ tailWord_2795572).sum := by decide
  have hdescent : baseEnd_2795572 < baseStart_2795572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795582 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_2795582 : Nat := 118140960795 + 2795582 * 2 ^ 59
def prefixEnd_2795582 : Nat := 4983230072969 + 3 ^ 40 * 2795582 * 2
def baseEnd_2795582 : Nat := 478492425019195502089453

theorem tailTrace_2795582 : CollatzResearch.WordTrace tailWord_2795582 prefixEnd_2795582 478492425019195502089453 := by
  unfold tailWord_2795582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745406519761417029897625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67975501438727557492787333 12745406519761417029897625)
  ·
    refine ⟨9559054889821062772423219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12745406519761417029897625 9559054889821062772423219)
    ·
      refine ⟨14338582334731594158634829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9559054889821062772423219 14338582334731594158634829)
      ·
        refine ⟨5376968375524347809488061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14338582334731594158634829 5376968375524347809488061)
        ·
          refine ⟨2016363140821630428558023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5376968375524347809488061 2016363140821630428558023)
          ·
            refine ⟨3024544711232445642837035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016363140821630428558023 3024544711232445642837035)
            ·
              refine ⟨4536817066848668464255553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024544711232445642837035 4536817066848668464255553)
              ·
                refine ⟨3402612800136501348191665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4536817066848668464255553 3402612800136501348191665)
                ·
                  refine ⟨2551959600102376011143749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402612800136501348191665 2551959600102376011143749)
                  ·
                    refine ⟨478492425019195502089453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2551959600102376011143749 478492425019195502089453)
                    ·
                      rfl

theorem cell23_2795582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_2795582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795582 prefixEnd_2795582 := by exact prefixLift 2795582
  have htrace : WordTrace (prefixWord ++ tailWord_2795582) baseStart_2795582 baseEnd_2795582 := by
    simpa [prefixWord, tailWord_2795582, baseEnd_2795582] using wordTrace_append hprefix tailTrace_2795582
  have hstable : (prefixWord ++ tailWord_2795582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795582).length < 2 ^ (prefixWord ++ tailWord_2795582).sum := by decide
  have hdescent : baseEnd_2795582 < baseStart_2795582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795605 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_2795605 : Nat := 118140960795 + 2795605 * 2 ^ 59
def prefixEnd_2795605 : Nat := 4983230072969 + 3 ^ 40 * 2795605 * 2
def baseEnd_2795605 : Nat := 1435489085112639916280753

theorem tailTrace_2795605 : CollatzResearch.WordTrace tailWord_2795605 prefixEnd_2795605 1435489085112639916280753 := by
  unfold tailWord_2795605
  simp only [CollatzResearch.WordTrace]
  refine ⟨101964091037008011167268269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67976060691338674111512179 101964091037008011167268269)
  ·
    refine ⟨38236534138878004187725601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101964091037008011167268269 38236534138878004187725601)
    ·
      refine ⟨28677400604158503140794201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38236534138878004187725601 28677400604158503140794201)
      ·
        refine ⟨21508050453118877355595651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28677400604158503140794201 21508050453118877355595651)
        ·
          refine ⟨32262075679678316033393477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21508050453118877355595651 32262075679678316033393477)
          ·
            refine ⟨6049139189939684256261277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32262075679678316033393477 6049139189939684256261277)
            ·
              refine ⟨2268427196227381596097979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6049139189939684256261277 2268427196227381596097979)
              ·
                refine ⟨3402640794341072394146969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268427196227381596097979 3402640794341072394146969)
                ·
                  refine ⟨2551980595755804295610227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402640794341072394146969 2551980595755804295610227)
                  ·
                    refine ⟨3827970893633706443415341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2551980595755804295610227 3827970893633706443415341)
                    ·
                      refine ⟨1435489085112639916280753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3827970893633706443415341 1435489085112639916280753)
                      ·
                        rfl

theorem cell23_2795605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_2795605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795605 prefixEnd_2795605 := by exact prefixLift 2795605
  have htrace : WordTrace (prefixWord ++ tailWord_2795605) baseStart_2795605 baseEnd_2795605 := by
    simpa [prefixWord, tailWord_2795605, baseEnd_2795605] using wordTrace_append hprefix tailTrace_2795605
  have hstable : (prefixWord ++ tailWord_2795605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795605).length < 2 ^ (prefixWord ++ tailWord_2795605).sum := by decide
  have hdescent : baseEnd_2795605 < baseStart_2795605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795628 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 4, 2, 2]
def baseStart_2795628 : Nat := 118140960795 + 2795628 * 2 ^ 59
def prefixEnd_2795628 : Nat := 4983230072969 + 3 ^ 40 * 2795628 * 2
def baseEnd_2795628 : Nat := 1435500895167693326293147

theorem tailTrace_2795628 : CollatzResearch.WordTrace tailWord_2795628 prefixEnd_2795628 1435500895167693326293147 := by
  unfold tailWord_2795628
  simp only [CollatzResearch.WordTrace]
  refine ⟨50982464957962343047677769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67976619943949790730237025 50982464957962343047677769)
  ·
    refine ⟨38236848718471757285758327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50982464957962343047677769 38236848718471757285758327)
    ·
      refine ⟨57355273077707635928637491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38236848718471757285758327 57355273077707635928637491)
      ·
        refine ⟨86032909616561453892956237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57355273077707635928637491 86032909616561453892956237)
        ·
          refine ⟨32262341106210545209858589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86032909616561453892956237 32262341106210545209858589)
          ·
            refine ⟨12098377914828954453696971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32262341106210545209858589 12098377914828954453696971)
            ·
              refine ⟨18147566872243431680545457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12098377914828954453696971 18147566872243431680545457)
              ·
                refine ⟨13610675154182573760409093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18147566872243431680545457 13610675154182573760409093)
                ·
                  refine ⟨2552001591409232580076705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13610675154182573760409093 2552001591409232580076705)
                  ·
                    refine ⟨1914001193556924435057529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2552001591409232580076705 1914001193556924435057529)
                    ·
                      refine ⟨1435500895167693326293147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914001193556924435057529 1435500895167693326293147)
                      ·
                        rfl

theorem cell23_2795628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_2795628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795628 prefixEnd_2795628 := by exact prefixLift 2795628
  have htrace : WordTrace (prefixWord ++ tailWord_2795628) baseStart_2795628 baseEnd_2795628 := by
    simpa [prefixWord, tailWord_2795628, baseEnd_2795628] using wordTrace_append hprefix tailTrace_2795628
  have hstable : (prefixWord ++ tailWord_2795628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795628).length < 2 ^ (prefixWord ++ tailWord_2795628).sum := by decide
  have hdescent : baseEnd_2795628 < baseStart_2795628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795651 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 7]
def baseStart_2795651 : Nat := 118140960795 + 2795651 * 2 ^ 59
def prefixEnd_2795651 : Nat := 4983230072969 + 3 ^ 40 * 2795651 * 2
def baseEnd_2795651 : Nat := 159501411691416304033949

theorem tailTrace_2795651 : CollatzResearch.WordTrace tailWord_2795651 prefixEnd_2795651 159501411691416304033949 := by
  unfold tailWord_2795651
  simp only [CollatzResearch.WordTrace]
  refine ⟨101965768794841361023442807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67977179196560907348961871 101965768794841361023442807)
  ·
    refine ⟨152948653192262041535164211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101965768794841361023442807 152948653192262041535164211)
    ·
      refine ⟨229422979788393062302746317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152948653192262041535164211 229422979788393062302746317)
      ·
        refine ⟨86033617420647398363529869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229422979788393062302746317 86033617420647398363529869)
        ·
          refine ⟨32262606532742774386323701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86033617420647398363529869 32262606532742774386323701)
          ·
            refine ⟨3024619362444635098717847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32262606532742774386323701 3024619362444635098717847)
            ·
              refine ⟨4536929043666952648076771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024619362444635098717847 4536929043666952648076771)
              ·
                refine ⟨6805393565500428972115157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536929043666952648076771 6805393565500428972115157)
                ·
                  refine ⟨159501411691416304033949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6805393565500428972115157 159501411691416304033949)
                  ·
                    rfl

theorem cell23_2795651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 7].length) (baseStart_2795651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795651 prefixEnd_2795651 := by exact prefixLift 2795651
  have htrace : WordTrace (prefixWord ++ tailWord_2795651) baseStart_2795651 baseEnd_2795651 := by
    simpa [prefixWord, tailWord_2795651, baseEnd_2795651] using wordTrace_append hprefix tailTrace_2795651
  have hstable : (prefixWord ++ tailWord_2795651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795651).length < 2 ^ (prefixWord ++ tailWord_2795651).sum := by decide
  have hdescent : baseEnd_2795651 < baseStart_2795651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795662 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_2795662 : Nat := 118140960795 + 2795662 * 2 ^ 59
def prefixEnd_2795662 : Nat := 4983230072969 + 3 ^ 40 * 2795662 * 2
def baseEnd_2795662 : Nat := 1435518353509946193267991

theorem tailTrace_2795662 : CollatzResearch.WordTrace tailWord_2795662 prefixEnd_2795662 1435518353509946193267991 := by
  unfold tailWord_2795662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745771249725188737761655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67977446665201006601395493 12745771249725188737761655)
  ·
    refine ⟨19118656874587783106642483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12745771249725188737761655 19118656874587783106642483)
    ·
      refine ⟨28677985311881674659963725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19118656874587783106642483 28677985311881674659963725)
      ·
        refine ⟨10754244491955627997486397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28677985311881674659963725 10754244491955627997486397)
        ·
          refine ⟨4032841684483360499057399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10754244491955627997486397 4032841684483360499057399)
          ·
            refine ⟨6049262526725040748586099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032841684483360499057399 6049262526725040748586099)
            ·
              refine ⟨9073893790087561122879149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049262526725040748586099 9073893790087561122879149)
              ·
                refine ⟨3402710171282835421079681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9073893790087561122879149 3402710171282835421079681)
                ·
                  refine ⟨2552032628462126565809761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402710171282835421079681 2552032628462126565809761)
                  ·
                    refine ⟨1914024471346594924357321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2552032628462126565809761 1914024471346594924357321)
                    ·
                      refine ⟨1435518353509946193267991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914024471346594924357321 1435518353509946193267991)
                      ·
                        rfl

theorem cell23_2795662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_2795662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795662 prefixEnd_2795662 := by exact prefixLift 2795662
  have htrace : WordTrace (prefixWord ++ tailWord_2795662) baseStart_2795662 baseEnd_2795662 := by
    simpa [prefixWord, tailWord_2795662, baseEnd_2795662] using wordTrace_append hprefix tailTrace_2795662
  have hstable : (prefixWord ++ tailWord_2795662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795662).length < 2 ^ (prefixWord ++ tailWord_2795662).sum := by decide
  have hdescent : baseEnd_2795662 < baseStart_2795662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795664 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 4, 5]
def baseStart_2795664 : Nat := 118140960795 + 2795664 * 2 ^ 59
def prefixEnd_2795664 : Nat := 4983230072969 + 3 ^ 40 * 2795664 * 2
def baseEnd_2795664 : Nat := 478506460157085061814327

theorem tailTrace_2795664 : CollatzResearch.WordTrace tailWord_2795664 prefixEnd_2795664 478506460157085061814327 := by
  unfold tailWord_2795664
  simp only [CollatzResearch.WordTrace]
  refine ⟨50983121471897132121833023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67977495295862842829110697 50983121471897132121833023)
  ·
    refine ⟨76474682207845698182749535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50983121471897132121833023 76474682207845698182749535)
    ·
      refine ⟨114712023311768547274124303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76474682207845698182749535 114712023311768547274124303)
      ·
        refine ⟨172068034967652820911186455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114712023311768547274124303 172068034967652820911186455)
        ·
          refine ⟨258102052451479231366779683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172068034967652820911186455 258102052451479231366779683)
          ·
            refine ⟨387153078677218847050169525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258102052451479231366779683 387153078677218847050169525)
            ·
              refine ⟨36295601125989266910953393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 387153078677218847050169525 36295601125989266910953393)
              ·
                refine ⟨27221700844491950183215045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36295601125989266910953393 27221700844491950183215045)
                ·
                  refine ⟨5104068908342240659352821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27221700844491950183215045 5104068908342240659352821)
                  ·
                    refine ⟨478506460157085061814327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5104068908342240659352821 478506460157085061814327)
                    ·
                      rfl

theorem cell23_2795664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_2795664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795664 prefixEnd_2795664 := by exact prefixLift 2795664
  have htrace : WordTrace (prefixWord ++ tailWord_2795664) baseStart_2795664 baseEnd_2795664 := by
    simpa [prefixWord, tailWord_2795664, baseEnd_2795664] using wordTrace_append hprefix tailTrace_2795664
  have hstable : (prefixWord ++ tailWord_2795664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795664).length < 2 ^ (prefixWord ++ tailWord_2795664).sum := by decide
  have hdescent : baseEnd_2795664 < baseStart_2795664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795681 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 2, 5]
def baseStart_2795681 : Nat := 118140960795 + 2795681 * 2 ^ 59
def prefixEnd_2795681 : Nat := 4983230072969 + 3 ^ 40 * 2795681 * 2
def baseEnd_2795681 : Nat := 478509369880793872976801

theorem tailTrace_2795681 : CollatzResearch.WordTrace tailWord_2795681 prefixEnd_2795681 478509369880793872976801 := by
  unfold tailWord_2795681
  simp only [CollatzResearch.WordTrace]
  refine ⟨101966862984732676147034897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67977908656488450764689931 101966862984732676147034897)
  ·
    refine ⟨76475147238549507110276173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101966862984732676147034897 76475147238549507110276173)
    ·
      refine ⟨28678180214456065166353565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76475147238549507110276173 28678180214456065166353565)
      ·
        refine ⟨10754317580421024437382587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28678180214456065166353565 10754317580421024437382587)
        ·
          refine ⟨16131476370631536656073881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10754317580421024437382587 16131476370631536656073881)
          ·
            refine ⟨12098607277973652492055411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16131476370631536656073881 12098607277973652492055411)
            ·
              refine ⟨18147910916960478738083117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12098607277973652492055411 18147910916960478738083117)
              ·
                refine ⟨6805466593860179526781169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18147910916960478738083117 6805466593860179526781169)
                ·
                  refine ⟨5104099945395134645085877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6805466593860179526781169 5104099945395134645085877)
                  ·
                    refine ⟨478509369880793872976801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5104099945395134645085877 478509369880793872976801)
                    ·
                      rfl

theorem cell23_2795681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_2795681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795681 prefixEnd_2795681 := by exact prefixLift 2795681
  have htrace : WordTrace (prefixWord ++ tailWord_2795681) baseStart_2795681 baseEnd_2795681 := by
    simpa [prefixWord, tailWord_2795681, baseEnd_2795681] using wordTrace_append hprefix tailTrace_2795681
  have hstable : (prefixWord ++ tailWord_2795681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795681).length < 2 ^ (prefixWord ++ tailWord_2795681).sum := by decide
  have hdescent : baseEnd_2795681 < baseStart_2795681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795704 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_2795704 : Nat := 118140960795 + 2795704 * 2 ^ 59
def prefixEnd_2795704 : Nat := 4983230072969 + 3 ^ 40 * 2795704 * 2
def baseEnd_2795704 : Nat := 1435539919697435028942797

theorem tailTrace_2795704 : CollatzResearch.WordTrace tailWord_2795704 prefixEnd_2795704 1435539919697435028942797 := by
  unfold tailWord_2795704
  simp only [CollatzResearch.WordTrace]
  refine ⟨50983850931824675537561083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67978467909099567383414777 50983850931824675537561083)
  ·
    refine ⟨76475776397737013306341625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50983850931824675537561083 76475776397737013306341625)
    ·
      refine ⟨57356832298302759979756219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76475776397737013306341625 57356832298302759979756219)
      ·
        refine ⟨86035248447454139969634329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57356832298302759979756219 86035248447454139969634329)
        ·
          refine ⟨64526436335590604977225747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86035248447454139969634329 64526436335590604977225747)
          ·
            refine ⟨96789654503385907465838621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64526436335590604977225747 96789654503385907465838621)
            ·
              refine ⟨36296120438769715299689483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96789654503385907465838621 36296120438769715299689483)
              ·
                refine ⟨54444180658154572949534225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36296120438769715299689483 54444180658154572949534225)
                ·
                  refine ⟨40833135493615929712150669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54444180658154572949534225 40833135493615929712150669)
                  ·
                    refine ⟨15312425810105973642056501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40833135493615929712150669 15312425810105973642056501)
                    ·
                      refine ⟨1435539919697435028942797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15312425810105973642056501 1435539919697435028942797)
                      ·
                        rfl

theorem cell23_2795704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_2795704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795704 prefixEnd_2795704 := by exact prefixLift 2795704
  have htrace : WordTrace (prefixWord ++ tailWord_2795704) baseStart_2795704 baseEnd_2795704 := by
    simpa [prefixWord, tailWord_2795704, baseEnd_2795704] using wordTrace_append hprefix tailTrace_2795704
  have hstable : (prefixWord ++ tailWord_2795704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795704).length < 2 ^ (prefixWord ++ tailWord_2795704).sum := by decide
  have hdescent : baseEnd_2795704 < baseStart_2795704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795711 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 3, 4]
def baseStart_2795711 : Nat := 118140960795 + 2795711 * 2 ^ 59
def prefixEnd_2795711 : Nat := 4983230072969 + 3 ^ 40 * 2795711 * 2
def baseEnd_2795711 : Nat := 478514504687338833851755

theorem tailTrace_2795711 : CollatzResearch.WordTrace tailWord_2795711 prefixEnd_2795711 478514504687338833851755 := by
  unfold tailWord_2795711
  simp only [CollatzResearch.WordTrace]
  refine ⟨101967957174623991270626987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67978638116415994180417991 101967957174623991270626987)
  ·
    refine ⟨152951935761935986905940481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101967957174623991270626987 152951935761935986905940481)
    ·
      refine ⟨114713951821451990179455361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152951935761935986905940481 114713951821451990179455361)
      ·
        refine ⟨86035463866088992634591521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114713951821451990179455361 86035463866088992634591521)
        ·
          refine ⟨64526597899566744475943641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86035463866088992634591521 64526597899566744475943641)
          ·
            refine ⟨48394948424675058356957731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64526597899566744475943641 48394948424675058356957731)
            ·
              refine ⟨72592422637012587535436597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48394948424675058356957731 72592422637012587535436597)
              ·
                refine ⟨6805539622219930081447181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72592422637012587535436597 6805539622219930081447181)
                ·
                  refine ⟨2552077358332473780542693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6805539622219930081447181 2552077358332473780542693)
                  ·
                    refine ⟨478514504687338833851755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2552077358332473780542693 478514504687338833851755)
                    ·
                      rfl

theorem cell23_2795711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 4].length) (baseStart_2795711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795711 prefixEnd_2795711 := by exact prefixLift 2795711
  have htrace : WordTrace (prefixWord ++ tailWord_2795711) baseStart_2795711 baseEnd_2795711 := by
    simpa [prefixWord, tailWord_2795711, baseEnd_2795711] using wordTrace_append hprefix tailTrace_2795711
  have hstable : (prefixWord ++ tailWord_2795711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795711).length < 2 ^ (prefixWord ++ tailWord_2795711).sum := by decide
  have hdescent : baseEnd_2795711 < baseStart_2795711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795738 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_2795738 : Nat := 118140960795 + 2795738 * 2 ^ 59
def prefixEnd_2795738 : Nat := 4983230072969 + 3 ^ 40 * 2795738 * 2
def baseEnd_2795738 : Nat := 1435557378039687895917641

theorem tailTrace_2795738 : CollatzResearch.WordTrace tailWord_2795738 prefixEnd_2795738 1435557378039687895917641 := by
  unfold tailWord_2795738
  simp only [CollatzResearch.WordTrace]
  refine ⟨25492235486381543720464967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67979294630350783254573245 25492235486381543720464967)
  ·
    refine ⟨38238353229572315580697451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25492235486381543720464967 38238353229572315580697451)
    ·
      refine ⟨57357529844358473371046177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38238353229572315580697451 57357529844358473371046177)
      ·
        refine ⟨43018147383268855028284633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57357529844358473371046177 43018147383268855028284633)
        ·
          refine ⟨32263610537451641271213475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43018147383268855028284633 32263610537451641271213475)
          ·
            refine ⟨48395415806177461906820213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32263610537451641271213475 48395415806177461906820213)
            ·
              refine ⟨4537070231829137053764395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48395415806177461906820213 4537070231829137053764395)
              ·
                refine ⟨6805605347743705580646593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537070231829137053764395 6805605347743705580646593)
                ·
                  refine ⟨5104204010807779185484945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6805605347743705580646593 5104204010807779185484945)
                  ·
                    refine ⟨3828153008105834389113709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5104204010807779185484945 3828153008105834389113709)
                    ·
                      refine ⟨1435557378039687895917641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3828153008105834389113709 1435557378039687895917641)
                      ·
                        rfl

theorem cell23_2795738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_2795738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795738 prefixEnd_2795738 := by exact prefixLift 2795738
  have htrace : WordTrace (prefixWord ++ tailWord_2795738) baseStart_2795738 baseEnd_2795738 := by
    simpa [prefixWord, tailWord_2795738, baseEnd_2795738] using wordTrace_append hprefix tailTrace_2795738
  have hstable : (prefixWord ++ tailWord_2795738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795738).length < 2 ^ (prefixWord ++ tailWord_2795738).sum := by decide
  have hdescent : baseEnd_2795738 < baseStart_2795738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795745 : List Nat := [1, 2, 3, 1, 3, 1, 4, 3, 1, 4]
def baseStart_2795745 : Nat := 118140960795 + 2795745 * 2 ^ 59
def prefixEnd_2795745 : Nat := 4983230072969 + 3 ^ 40 * 2795745 * 2
def baseEnd_2795745 : Nat := 478520324134756456176703

theorem tailTrace_2795745 : CollatzResearch.WordTrace tailWord_2795745 prefixEnd_2795745 478520324134756456176703 := by
  unfold tailWord_2795745
  simp only [CollatzResearch.WordTrace]
  refine ⟨101969197256500815077364689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67979464837667210051576459 101969197256500815077364689)
  ·
    refine ⟨76476897942375611308023517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101969197256500815077364689 76476897942375611308023517)
    ·
      refine ⟨28678836728390854240508819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76476897942375611308023517 28678836728390854240508819)
      ·
        refine ⟨43018255092586281360763229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28678836728390854240508819 43018255092586281360763229)
        ·
          refine ⟨16131845659719855510286211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43018255092586281360763229 16131845659719855510286211)
          ·
            refine ⟨24197768489579783265429317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16131845659719855510286211 24197768489579783265429317)
            ·
              refine ⟨4537081591796209362267997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24197768489579783265429317 4537081591796209362267997)
              ·
                refine ⟨1701405596923578510850499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4537081591796209362267997 1701405596923578510850499)
                ·
                  refine ⟨2552108395385367766275749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701405596923578510850499 2552108395385367766275749)
                  ·
                    refine ⟨478520324134756456176703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2552108395385367766275749 478520324134756456176703)
                    ·
                      rfl

theorem cell23_2795745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_2795745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795745 prefixEnd_2795745 := by exact prefixLift 2795745
  have htrace : WordTrace (prefixWord ++ tailWord_2795745) baseStart_2795745 baseEnd_2795745 := by
    simpa [prefixWord, tailWord_2795745, baseEnd_2795745] using wordTrace_append hprefix tailTrace_2795745
  have hstable : (prefixWord ++ tailWord_2795745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795745).length < 2 ^ (prefixWord ++ tailWord_2795745).sum := by decide
  have hdescent : baseEnd_2795745 < baseStart_2795745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795788 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_2795788 : Nat := 118140960795 + 2795788 * 2 ^ 59
def prefixEnd_2795788 : Nat := 4983230072969 + 3 ^ 40 * 2795788 * 2
def baseEnd_2795788 : Nat := 478527684024137566764137

theorem tailTrace_2795788 : CollatzResearch.WordTrace tailWord_2795788 prefixEnd_2795788 478527684024137566764137 := by
  unfold tailWord_2795788
  simp only [CollatzResearch.WordTrace]
  refine ⟨50985382797672516710590009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67980510396896688947453345 50985382797672516710590009)
  ·
    refine ⟨38239037098254387532942507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50985382797672516710590009 38239037098254387532942507)
    ·
      refine ⟨57358555647381581299413761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38239037098254387532942507 57358555647381581299413761)
      ·
        refine ⟨43018916735536185974560321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57358555647381581299413761 43018916735536185974560321)
        ·
          refine ⟨32264187551652139480920241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43018916735536185974560321 32264187551652139480920241)
          ·
            refine ⟨24198140663739104610690181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32264187551652139480920241 24198140663739104610690181)
            ·
              refine ⟨4537151374451082114504409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24198140663739104610690181 4537151374451082114504409)
              ·
                refine ⟨3402863530838311585878307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4537151374451082114504409 3402863530838311585878307)
                ·
                  refine ⟨5104295296257467378817461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3402863530838311585878307 5104295296257467378817461)
                  ·
                    refine ⟨478527684024137566764137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5104295296257467378817461 478527684024137566764137)
                    ·
                      rfl

theorem cell23_2795788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_2795788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795788 prefixEnd_2795788 := by exact prefixLift 2795788
  have htrace : WordTrace (prefixWord ++ tailWord_2795788) baseStart_2795788 baseEnd_2795788 := by
    simpa [prefixWord, tailWord_2795788, baseEnd_2795788] using wordTrace_append hprefix tailTrace_2795788
  have hstable : (prefixWord ++ tailWord_2795788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795788).length < 2 ^ (prefixWord ++ tailWord_2795788).sum := by decide
  have hdescent : baseEnd_2795788 < baseStart_2795788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795791 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_2795791 : Nat := 118140960795 + 2795791 * 2 ^ 59
def prefixEnd_2795791 : Nat := 4983230072969 + 3 ^ 40 * 2795791 * 2
def baseEnd_2795791 : Nat := 1435584592514376188554897

theorem tailTrace_2795791 : CollatzResearch.WordTrace tailWord_2795791 prefixEnd_2795791 1435584592514376188554897 := by
  unfold tailWord_2795791
  simp only [CollatzResearch.WordTrace]
  refine ⟨101970875014334164933539227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67980583342889443289026151 101970875014334164933539227)
  ·
    refine ⟨152956312521501247400308841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101970875014334164933539227 152956312521501247400308841)
    ·
      refine ⟨114717234391125935550231631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152956312521501247400308841 114717234391125935550231631)
      ·
        refine ⟨172075851586688903325347447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114717234391125935550231631 172075851586688903325347447)
        ·
          refine ⟨258113777380033354988021171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172075851586688903325347447 258113777380033354988021171)
          ·
            refine ⟨387170666070050032482031757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258113777380033354988021171 387170666070050032482031757)
            ·
              refine ⟨145188999776268762180761909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 387170666070050032482031757 145188999776268762180761909)
              ·
                refine ⟨13611468729025196454446429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145188999776268762180761909 13611468729025196454446429)
                ·
                  refine ⟨5104300773384448670417411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13611468729025196454446429 5104300773384448670417411)
                  ·
                    refine ⟨7656451160076673005626117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5104300773384448670417411 7656451160076673005626117)
                    ·
                      refine ⟨1435584592514376188554897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7656451160076673005626117 1435584592514376188554897)
                      ·
                        rfl

theorem cell23_2795791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_2795791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795791 prefixEnd_2795791 := by exact prefixLift 2795791
  have htrace : WordTrace (prefixWord ++ tailWord_2795791) baseStart_2795791 baseEnd_2795791 := by
    simpa [prefixWord, tailWord_2795791, baseEnd_2795791] using wordTrace_append hprefix tailTrace_2795791
  have hstable : (prefixWord ++ tailWord_2795791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795791).length < 2 ^ (prefixWord ++ tailWord_2795791).sum := by decide
  have hdescent : baseEnd_2795791 < baseStart_2795791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795838 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2795838 : Nat := 118140960795 + 2795838 * 2 ^ 59
def prefixEnd_2795838 : Nat := 4983230072969 + 3 ^ 40 * 2795838 * 2
def baseEnd_2795838 : Nat := 1435608726105137504667181

theorem tailTrace_2795838 : CollatzResearch.WordTrace tailWord_2795838 prefixEnd_2795838 1435608726105137504667181 := by
  unfold tailWord_2795838
  simp only [CollatzResearch.WordTrace]
  refine ⟨12746573655645486495062521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67981726163442594640333445 12746573655645486495062521)
  ·
    refine ⟨9559930241734114871296891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12746573655645486495062521 9559930241734114871296891)
    ·
      refine ⟨14339895362601172306945337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9559930241734114871296891 14339895362601172306945337)
      ·
        refine ⟨10754921521950879230209003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14339895362601172306945337 10754921521950879230209003)
        ·
          refine ⟨16132382282926318845313505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10754921521950879230209003 16132382282926318845313505)
          ·
            refine ⟨12099286712194739133985129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16132382282926318845313505 12099286712194739133985129)
            ·
              refine ⟨9074465034146054350488847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12099286712194739133985129 9074465034146054350488847)
              ·
                refine ⟨13611697551219081525733271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9074465034146054350488847 13611697551219081525733271)
                ·
                  refine ⟨20417546326828622288599907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13611697551219081525733271 20417546326828622288599907)
                  ·
                    refine ⟨30626319490242933432899861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20417546326828622288599907 30626319490242933432899861)
                    ·
                      refine ⟨1435608726105137504667181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30626319490242933432899861 1435608726105137504667181)
                      ·
                        rfl

theorem cell23_2795838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2795838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795838 prefixEnd_2795838 := by exact prefixLift 2795838
  have htrace : WordTrace (prefixWord ++ tailWord_2795838) baseStart_2795838 baseEnd_2795838 := by
    simpa [prefixWord, tailWord_2795838, baseEnd_2795838] using wordTrace_append hprefix tailTrace_2795838
  have hstable : (prefixWord ++ tailWord_2795838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795838).length < 2 ^ (prefixWord ++ tailWord_2795838).sum := by decide
  have hdescent : baseEnd_2795838 < baseStart_2795838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795858 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_2795858 : Nat := 118140960795 + 2795858 * 2 ^ 59
def prefixEnd_2795858 : Nat := 4983230072969 + 3 ^ 40 * 2795858 * 2
def baseEnd_2795858 : Nat := 1435618995718227426417089

theorem tailTrace_2795858 : CollatzResearch.WordTrace tailWord_2795858 prefixEnd_2795858 1435618995718227426417089 := by
  unfold tailWord_2795858
  simp only [CollatzResearch.WordTrace]
  refine ⟨25493329676272858844057057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67982212470060956917485485 25493329676272858844057057)
  ·
    refine ⟨19119997257204644133042793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25493329676272858844057057 19119997257204644133042793)
    ·
      refine ⟨14339997942903483099782095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19119997257204644133042793 14339997942903483099782095)
      ·
        refine ⟨21509996914355224649673143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14339997942903483099782095 21509996914355224649673143)
        ·
          refine ⟨32264995371532836974509715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21509996914355224649673143 32264995371532836974509715)
          ·
            refine ⟨48397493057299255461764573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32264995371532836974509715 48397493057299255461764573)
            ·
              refine ⟨18149059896487220798161715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48397493057299255461764573 18149059896487220798161715)
              ·
                refine ⟨27223589844730831197242573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18149059896487220798161715 27223589844730831197242573)
                ·
                  refine ⟨10208846191774061698965965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27223589844730831197242573 10208846191774061698965965)
                  ·
                    refine ⟨3828317321915273137112237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10208846191774061698965965 3828317321915273137112237)
                    ·
                      refine ⟨1435618995718227426417089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3828317321915273137112237 1435618995718227426417089)
                      ·
                        rfl

theorem cell23_2795858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_2795858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795858 prefixEnd_2795858 := by exact prefixLift 2795858
  have htrace : WordTrace (prefixWord ++ tailWord_2795858) baseStart_2795858 baseEnd_2795858 := by
    simpa [prefixWord, tailWord_2795858, baseEnd_2795858] using wordTrace_append hprefix tailTrace_2795858
  have hstable : (prefixWord ++ tailWord_2795858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795858).length < 2 ^ (prefixWord ++ tailWord_2795858).sum := by decide
  have hdescent : baseEnd_2795858 < baseStart_2795858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795870 : List Nat := [4, 4, 2, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2795870 : Nat := 118140960795 + 2795870 * 2 ^ 59
def prefixEnd_2795870 : Nat := 4983230072969 + 3 ^ 40 * 2795870 * 2
def baseEnd_2795870 : Nat := 1435625157486081379467035

theorem tailTrace_2795870 : CollatzResearch.WordTrace tailWord_2795870 prefixEnd_2795870 1435625157486081379467035 := by
  unfold tailWord_2795870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12746719547630995178208133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67982504254031974283776709 12746719547630995178208133)
  ·
    refine ⟨2390009915180811595914025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12746719547630995178208133 2390009915180811595914025)
    ·
      refine ⟨1792507436385608696935519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2390009915180811595914025 1792507436385608696935519)
      ·
        refine ⟨2688761154578413045403279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792507436385608696935519 2688761154578413045403279)
        ·
          refine ⟨4033141731867619568104919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688761154578413045403279 4033141731867619568104919)
          ·
            refine ⟨6049712597801429352157379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033141731867619568104919 6049712597801429352157379)
            ·
              refine ⟨9074568896702144028236069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049712597801429352157379 9074568896702144028236069)
              ·
                refine ⟨1701481668131652005294263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9074568896702144028236069 1701481668131652005294263)
                ·
                  refine ⟨2552222502197478007941395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701481668131652005294263 2552222502197478007941395)
                  ·
                    refine ⟨3828333753296217011912093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2552222502197478007941395 3828333753296217011912093)
                    ·
                      refine ⟨1435625157486081379467035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3828333753296217011912093 1435625157486081379467035)
                      ·
                        rfl

theorem cell23_2795870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2795870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795870 prefixEnd_2795870 := by exact prefixLift 2795870
  have htrace : WordTrace (prefixWord ++ tailWord_2795870) baseStart_2795870 baseEnd_2795870 := by
    simpa [prefixWord, tailWord_2795870, baseEnd_2795870] using wordTrace_append hprefix tailTrace_2795870
  have hstable : (prefixWord ++ tailWord_2795870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795870).length < 2 ^ (prefixWord ++ tailWord_2795870).sum := by decide
  have hdescent : baseEnd_2795870 < baseStart_2795870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795871 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_2795871 : Nat := 118140960795 + 2795871 * 2 ^ 59
def prefixEnd_2795871 : Nat := 4983230072969 + 3 ^ 40 * 2795871 * 2
def baseEnd_2795871 : Nat := 1435625670966735875554529

theorem tailTrace_2795871 : CollatzResearch.WordTrace tailWord_2795871 prefixEnd_2795871 1435625670966735875554529 := by
  unfold tailWord_2795871
  simp only [CollatzResearch.WordTrace]
  refine ⟨101973792854044338596451467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67982528569362892397634311 101973792854044338596451467)
  ·
    refine ⟨152960689281066507894677201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101973792854044338596451467 152960689281066507894677201)
    ·
      refine ⟨114720516960799880921007901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152960689281066507894677201 114720516960799880921007901)
      ·
        refine ⟨43020193860299955345377963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114720516960799880921007901 43020193860299955345377963)
        ·
          refine ⟨64530290790449933018066945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43020193860299955345377963 64530290790449933018066945)
          ·
            refine ⟨48397718092837449763550209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64530290790449933018066945 48397718092837449763550209)
            ·
              refine ⟨36298288569628087322662657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48397718092837449763550209 36298288569628087322662657)
              ·
                refine ⟨27223716427221065491996993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36298288569628087322662657 27223716427221065491996993)
                ·
                  refine ⟨20417787320415799118997745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27223716427221065491996993 20417787320415799118997745)
                  ·
                    refine ⟨15313340490311849339248309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20417787320415799118997745 15313340490311849339248309)
                    ·
                      refine ⟨1435625670966735875554529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15313340490311849339248309 1435625670966735875554529)
                      ·
                        rfl

theorem cell23_2795871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_2795871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795871 prefixEnd_2795871 := by exact prefixLift 2795871
  have htrace : WordTrace (prefixWord ++ tailWord_2795871) baseStart_2795871 baseEnd_2795871 := by
    simpa [prefixWord, tailWord_2795871, baseEnd_2795871] using wordTrace_append hprefix tailTrace_2795871
  have hstable : (prefixWord ++ tailWord_2795871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795871).length < 2 ^ (prefixWord ++ tailWord_2795871).sum := by decide
  have hdescent : baseEnd_2795871 < baseStart_2795871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795881 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_2795881 : Nat := 118140960795 + 2795881 * 2 ^ 59
def prefixEnd_2795881 : Nat := 4983230072969 + 3 ^ 40 * 2795881 * 2
def baseEnd_2795881 : Nat := 1435630805773280836429483

theorem tailTrace_2795881 : CollatzResearch.WordTrace tailWord_2795881 prefixEnd_2795881 1435630805773280836429483 := by
  unfold tailWord_2795881
  simp only [CollatzResearch.WordTrace]
  refine ⟨101974157584008110304315497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67982771722672073536210331 101974157584008110304315497)
  ·
    refine ⟨76480618188006082728236623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101974157584008110304315497 76480618188006082728236623)
    ·
      refine ⟨114720927282009124092354935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76480618188006082728236623 114720927282009124092354935)
      ·
        refine ⟨172081390923013686138532403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114720927282009124092354935 172081390923013686138532403)
        ·
          refine ⟨258122086384520529207798605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172081390923013686138532403 258122086384520529207798605)
          ·
            refine ⟨96795782394195198452924477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258122086384520529207798605 96795782394195198452924477)
            ·
              refine ⟨36298418397823199419846679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96795782394195198452924477 36298418397823199419846679)
              ·
                refine ⟨54447627596734799129770019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36298418397823199419846679 54447627596734799129770019)
                ·
                  refine ⟨81671441395102198694655029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54447627596734799129770019 81671441395102198694655029)
                  ·
                    refine ⟨7656697630790831127623909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81671441395102198694655029 7656697630790831127623909)
                    ·
                      refine ⟨1435630805773280836429483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7656697630790831127623909 1435630805773280836429483)
                      ·
                        rfl

theorem cell23_2795881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_2795881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795881 prefixEnd_2795881 := by exact prefixLift 2795881
  have htrace : WordTrace (prefixWord ++ tailWord_2795881) baseStart_2795881 baseEnd_2795881 := by
    simpa [prefixWord, tailWord_2795881, baseEnd_2795881] using wordTrace_append hprefix tailTrace_2795881
  have hstable : (prefixWord ++ tailWord_2795881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795881).length < 2 ^ (prefixWord ++ tailWord_2795881).sum := by decide
  have hdescent : baseEnd_2795881 < baseStart_2795881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795885 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_2795885 : Nat := 118140960795 + 2795885 * 2 ^ 59
def prefixEnd_2795885 : Nat := 4983230072969 + 3 ^ 40 * 2795885 * 2
def baseEnd_2795885 : Nat := 1435632859695898820779465

theorem tailTrace_2795885 : CollatzResearch.WordTrace tailWord_2795885 prefixEnd_2795885 1435632859695898820779465 := by
  unfold tailWord_2795885
  simp only [CollatzResearch.WordTrace]
  refine ⟨101974303475993618987461109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67982868983995745991640739 101974303475993618987461109)
  ·
    refine ⟨9560090950874401780074479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101974303475993618987461109 9560090950874401780074479)
    ·
      refine ⟨14340136426311602670111719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9560090950874401780074479 14340136426311602670111719)
      ·
        refine ⟨21510204639467404005167579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14340136426311602670111719 21510204639467404005167579)
        ·
          refine ⟨32265306959201106007751369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21510204639467404005167579 32265306959201106007751369)
          ·
            refine ⟨24198980219400829505813527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32265306959201106007751369 24198980219400829505813527)
            ·
              refine ⟨36298470329101244258720291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24198980219400829505813527 36298470329101244258720291)
              ·
                refine ⟨54447705493651866388080437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36298470329101244258720291 54447705493651866388080437)
                ·
                  refine ⟨5104472390029862473882541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54447705493651866388080437 5104472390029862473882541)
                  ·
                    refine ⟨1914177146261198427705953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5104472390029862473882541 1914177146261198427705953)
                    ·
                      refine ⟨1435632859695898820779465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914177146261198427705953 1435632859695898820779465)
                      ·
                        rfl

theorem cell23_2795885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_2795885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795885 prefixEnd_2795885 := by exact prefixLift 2795885
  have htrace : WordTrace (prefixWord ++ tailWord_2795885) baseStart_2795885 baseEnd_2795885 := by
    simpa [prefixWord, tailWord_2795885, baseEnd_2795885] using wordTrace_append hprefix tailTrace_2795885
  have hstable : (prefixWord ++ tailWord_2795885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795885).length < 2 ^ (prefixWord ++ tailWord_2795885).sum := by decide
  have hdescent : baseEnd_2795885 < baseStart_2795885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795891 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 2, 6]
def baseStart_2795891 : Nat := 118140960795 + 2795891 * 2 ^ 59
def prefixEnd_2795891 : Nat := 4983230072969 + 3 ^ 40 * 2795891 * 2
def baseEnd_2795891 : Nat := 478545313526608599101479

theorem tailTrace_2795891 : CollatzResearch.WordTrace tailWord_2795891 prefixEnd_2795891 478545313526608599101479 := by
  unfold tailWord_2795891
  simp only [CollatzResearch.WordTrace]
  refine ⟨101974522313971882012179527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67983014875981254674786351 101974522313971882012179527)
  ·
    refine ⟨152961783470957823018269291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101974522313971882012179527 152961783470957823018269291)
    ·
      refine ⟨229442675206436734527403937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152961783470957823018269291 229442675206436734527403937)
      ·
        refine ⟨172082006404827550895552953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229442675206436734527403937 172082006404827550895552953)
        ·
          refine ⟨129061504803620663171664715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172082006404827550895552953 129061504803620663171664715)
          ·
            refine ⟨193592257205430994757497073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129061504803620663171664715 193592257205430994757497073)
            ·
              refine ⟨145194192904073246068122805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193592257205430994757497073 145194192904073246068122805)
              ·
                refine ⟨13611955584756866818886513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145194192904073246068122805 13611955584756866818886513)
                ·
                  refine ⟨10208966688567650114164885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13611955584756866818886513 10208966688567650114164885)
                  ·
                    refine ⟨478545313526608599101479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10208966688567650114164885 478545313526608599101479)
                    ·
                      rfl

theorem cell23_2795891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 6].length) (baseStart_2795891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795891 prefixEnd_2795891 := by exact prefixLift 2795891
  have htrace : WordTrace (prefixWord ++ tailWord_2795891) baseStart_2795891 baseEnd_2795891 := by
    simpa [prefixWord, tailWord_2795891, baseEnd_2795891] using wordTrace_append hprefix tailTrace_2795891
  have hstable : (prefixWord ++ tailWord_2795891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795891).length < 2 ^ (prefixWord ++ tailWord_2795891).sum := by decide
  have hdescent : baseEnd_2795891 < baseStart_2795891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795915 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 1, 4, 2]
def baseStart_2795915 : Nat := 118140960795 + 2795915 * 2 ^ 59
def prefixEnd_2795915 : Nat := 4983230072969 + 3 ^ 40 * 2795915 * 2
def baseEnd_2795915 : Nat := 1435648264115533703404327

theorem tailTrace_2795915 : CollatzResearch.WordTrace tailWord_2795915 prefixEnd_2795915 1435648264115533703404327 := by
  unfold tailWord_2795915
  simp only [CollatzResearch.WordTrace]
  refine ⟨101975397665884934111053199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67983598443923289407368799 101975397665884934111053199)
  ·
    refine ⟨152963096498827401166579799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101975397665884934111053199 152963096498827401166579799)
    ·
      refine ⟨229444644748241101749869699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152963096498827401166579799 229444644748241101749869699)
      ·
        refine ⟨344166967122361652624804549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229444644748241101749869699 344166967122361652624804549)
        ·
          refine ⟨64531306335442809867150853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 344166967122361652624804549 64531306335442809867150853)
          ·
            refine ⟨12099619937895526850090785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64531306335442809867150853 12099619937895526850090785)
            ·
              refine ⟨9074714953421645137568089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12099619937895526850090785 9074714953421645137568089)
              ·
                refine ⟨6806036215066233853176067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9074714953421645137568089 6806036215066233853176067)
                ·
                  refine ⟨10209054322599350779764101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6806036215066233853176067 10209054322599350779764101)
                  ·
                    refine ⟨1914197685487378271205769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10209054322599350779764101 1914197685487378271205769)
                    ·
                      refine ⟨1435648264115533703404327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914197685487378271205769 1435648264115533703404327)
                      ·
                        rfl

theorem cell23_2795915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 4, 2].length) (baseStart_2795915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795915 prefixEnd_2795915 := by exact prefixLift 2795915
  have htrace : WordTrace (prefixWord ++ tailWord_2795915) baseStart_2795915 baseEnd_2795915 := by
    simpa [prefixWord, tailWord_2795915, baseEnd_2795915] using wordTrace_append hprefix tailTrace_2795915
  have hstable : (prefixWord ++ tailWord_2795915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795915).length < 2 ^ (prefixWord ++ tailWord_2795915).sum := by decide
  have hdescent : baseEnd_2795915 < baseStart_2795915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795968 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 2, 5]
def baseStart_2795968 : Nat := 118140960795 + 2795968 * 2 ^ 59
def prefixEnd_2795968 : Nat := 4983230072969 + 3 ^ 40 * 2795968 * 2
def baseEnd_2795968 : Nat := 478558492863407332013861

theorem tailTrace_2795968 : CollatzResearch.WordTrace tailWord_2795968 prefixEnd_2795968 478558492863407332013861 := by
  unfold tailWord_2795968
  simp only [CollatzResearch.WordTrace]
  refine ⟨50988665367346462081366279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67984887156461949441821705 50988665367346462081366279)
  ·
    refine ⟨76482998051019693122049419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50988665367346462081366279 76482998051019693122049419)
    ·
      refine ⟨114724497076529539683074129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76482998051019693122049419 114724497076529539683074129)
      ·
        refine ⟨86043372807397154762305597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114724497076529539683074129 86043372807397154762305597)
        ·
          refine ⟨32266264802773933035864599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86043372807397154762305597 32266264802773933035864599)
          ·
            refine ⟨48399397204160899553796899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32266264802773933035864599 48399397204160899553796899)
            ·
              refine ⟨72599095806241349330695349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48399397204160899553796899 72599095806241349330695349)
              ·
                refine ⟨6806165231835126499752689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72599095806241349330695349 6806165231835126499752689)
                ·
                  refine ⟨5104623923876344874814517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6806165231835126499752689 5104623923876344874814517)
                  ·
                    refine ⟨478558492863407332013861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5104623923876344874814517 478558492863407332013861)
                    ·
                      rfl

theorem cell23_2795968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_2795968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795968 prefixEnd_2795968 := by exact prefixLift 2795968
  have htrace : WordTrace (prefixWord ++ tailWord_2795968) baseStart_2795968 baseEnd_2795968 := by
    simpa [prefixWord, tailWord_2795968, baseEnd_2795968] using wordTrace_append hprefix tailTrace_2795968
  have hstable : (prefixWord ++ tailWord_2795968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795968).length < 2 ^ (prefixWord ++ tailWord_2795968).sum := by decide
  have hdescent : baseEnd_2795968 < baseStart_2795968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795969 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2795969 : Nat := 118140960795 + 2795969 * 2 ^ 59
def prefixEnd_2795969 : Nat := 4983230072969 + 3 ^ 40 * 2795969 * 2
def baseEnd_2795969 : Nat := 1435675992070876492129079

theorem tailTrace_2795969 : CollatzResearch.WordTrace tailWord_2795969 prefixEnd_2795969 1435675992070876492129079 := by
  unfold tailWord_2795969
  simp only [CollatzResearch.WordTrace]
  refine ⟨101977367207689301333518961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67984911471792867555679307 101977367207689301333518961)
  ·
    refine ⟨76483025405766976000139221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101977367207689301333518961 76483025405766976000139221)
    ·
      refine ⟨1792570907947663500003263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 76483025405766976000139221 1792570907947663500003263)
      ·
        refine ⟨2688856361921495250004895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792570907947663500003263 2688856361921495250004895)
        ·
          refine ⟨4033284542882242875007343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688856361921495250004895 4033284542882242875007343)
          ·
            refine ⟨6049926814323364312511015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033284542882242875007343 6049926814323364312511015)
            ·
              refine ⟨9074890221485046468766523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049926814323364312511015 9074890221485046468766523)
              ·
                refine ⟨13612335332227569703149785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9074890221485046468766523 13612335332227569703149785)
                ·
                  refine ⟨10209251499170677277362339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13612335332227569703149785 10209251499170677277362339)
                  ·
                    refine ⟨15313877248756015916043509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10209251499170677277362339 15313877248756015916043509)
                    ·
                      refine ⟨1435675992070876492129079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15313877248756015916043509 1435675992070876492129079)
                      ·
                        rfl

theorem cell23_2795969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2795969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795969 prefixEnd_2795969 := by exact prefixLift 2795969
  have htrace : WordTrace (prefixWord ++ tailWord_2795969) baseStart_2795969 baseEnd_2795969 := by
    simpa [prefixWord, tailWord_2795969, baseEnd_2795969] using wordTrace_append hprefix tailTrace_2795969
  have hstable : (prefixWord ++ tailWord_2795969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795969).length < 2 ^ (prefixWord ++ tailWord_2795969).sum := by decide
  have hdescent : baseEnd_2795969 < baseStart_2795969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795978 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_2795978 : Nat := 118140960795 + 2795978 * 2 ^ 59
def prefixEnd_2795978 : Nat := 4983230072969 + 3 ^ 40 * 2795978 * 2
def baseEnd_2795978 : Nat := 1435680613396766956916537

theorem tailTrace_2795978 : CollatzResearch.WordTrace tailWord_2795978 prefixEnd_2795978 1435680613396766956916537 := by
  unfold tailWord_2795978
  simp only [CollatzResearch.WordTrace]
  refine ⟨25494423866164173967649147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67985130309771130580397725 25494423866164173967649147)
  ·
    refine ⟨38241635799246260951473721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25494423866164173967649147 38241635799246260951473721)
    ·
      refine ⟨28681226849434695713605291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38241635799246260951473721 28681226849434695713605291)
      ·
        refine ⟨43021840274152043570407937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28681226849434695713605291 43021840274152043570407937)
        ·
          refine ⟨32266380205614032677805953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43021840274152043570407937 32266380205614032677805953)
          ·
            refine ⟨24199785154210524508354465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32266380205614032677805953 24199785154210524508354465)
            ·
              refine ⟨18149838865657893381265849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24199785154210524508354465 18149838865657893381265849)
              ·
                refine ⟨13612379149243420035949387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18149838865657893381265849 13612379149243420035949387)
                ·
                  refine ⟨20418568723865130053924081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13612379149243420035949387 20418568723865130053924081)
                  ·
                    refine ⟨15313926542898847540443061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20418568723865130053924081 15313926542898847540443061)
                    ·
                      refine ⟨1435680613396766956916537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15313926542898847540443061 1435680613396766956916537)
                      ·
                        rfl

theorem cell23_2795978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_2795978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2795978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2795978 prefixEnd_2795978 := by exact prefixLift 2795978
  have htrace : WordTrace (prefixWord ++ tailWord_2795978) baseStart_2795978 baseEnd_2795978 := by
    simpa [prefixWord, tailWord_2795978, baseEnd_2795978] using wordTrace_append hprefix tailTrace_2795978
  have hstable : (prefixWord ++ tailWord_2795978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795978).length < 2 ^ (prefixWord ++ tailWord_2795978).sum := by decide
  have hdescent : baseEnd_2795978 < baseStart_2795978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796022 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2796022 : Nat := 118140960795 + 2796022 * 2 ^ 59
def prefixEnd_2796022 : Nat := 4983230072969 + 3 ^ 40 * 2796022 * 2
def baseEnd_2796022 : Nat := 1435703206545564784766335

theorem tailTrace_2796022 : CollatzResearch.WordTrace tailWord_2796022 prefixEnd_2796022 1435703206545564784766335 := by
  unfold tailWord_2796022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6373706267281080711574895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67986200184331527590132213 6373706267281080711574895)
  ·
    refine ⟨9560559400921621067362343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6373706267281080711574895 9560559400921621067362343)
    ·
      refine ⟨14340839101382431601043515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9560559400921621067362343 14340839101382431601043515)
      ·
        refine ⟨21511258652073647401565273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14340839101382431601043515 21511258652073647401565273)
        ·
          refine ⟨16133443989055235551173955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21511258652073647401565273 16133443989055235551173955)
          ·
            refine ⟨24200165983582853326760933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16133443989055235551173955 24200165983582853326760933)
            ·
              refine ⟨4537531121921784998767675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24200165983582853326760933 4537531121921784998767675)
              ·
                refine ⟨6806296682882677498151513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537531121921784998767675 6806296682882677498151513)
                ·
                  refine ⟨5104722512162008123613635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6806296682882677498151513 5104722512162008123613635)
                  ·
                    refine ⟨7657083768243012185420453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5104722512162008123613635 7657083768243012185420453)
                    ·
                      refine ⟨1435703206545564784766335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7657083768243012185420453 1435703206545564784766335)
                      ·
                        rfl

theorem cell23_2796022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2796022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796022 prefixEnd_2796022 := by exact prefixLift 2796022
  have htrace : WordTrace (prefixWord ++ tailWord_2796022) baseStart_2796022 baseEnd_2796022 := by
    simpa [prefixWord, tailWord_2796022, baseEnd_2796022] using wordTrace_append hprefix tailTrace_2796022
  have hstable : (prefixWord ++ tailWord_2796022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796022).length < 2 ^ (prefixWord ++ tailWord_2796022).sum := by decide
  have hdescent : baseEnd_2796022 < baseStart_2796022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796025 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 3]
def baseStart_2796025 : Nat := 118140960795 + 2796025 * 2 ^ 59
def prefixEnd_2796025 : Nat := 4983230072969 + 3 ^ 40 * 2796025 * 2
def baseEnd_2796025 : Nat := 1435704746987528273028821

theorem tailTrace_2796025 : CollatzResearch.WordTrace tailWord_2796025 prefixEnd_2796025 1435704746987528273028821 := by
  unfold tailWord_2796025
  simp only [CollatzResearch.WordTrace]
  refine ⟨101979409695486422897557529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67986273130324281931705019 101979409695486422897557529)
  ·
    refine ⟨76484557271614817173168147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101979409695486422897557529 76484557271614817173168147)
    ·
      refine ⟨114726835907422225759752221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76484557271614817173168147 114726835907422225759752221)
      ·
        refine ⟨43022563465283334659907083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114726835907422225759752221 43022563465283334659907083)
        ·
          refine ⟨64533845197925001989860625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43022563465283334659907083 64533845197925001989860625)
          ·
            refine ⟨48400383898443751492395469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64533845197925001989860625 48400383898443751492395469)
            ·
              refine ⟨18150143961916406809648301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48400383898443751492395469 18150143961916406809648301)
              ·
                refine ⟨6806303985718652553618113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18150143961916406809648301 6806303985718652553618113)
                ·
                  refine ⟨5104727989288989415213585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6806303985718652553618113 5104727989288989415213585)
                  ·
                    refine ⟨3828545991966742061410189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5104727989288989415213585 3828545991966742061410189)
                    ·
                      refine ⟨1435704746987528273028821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3828545991966742061410189 1435704746987528273028821)
                      ·
                        rfl

theorem cell23_2796025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_2796025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796025 prefixEnd_2796025 := by exact prefixLift 2796025
  have htrace : WordTrace (prefixWord ++ tailWord_2796025) baseStart_2796025 baseEnd_2796025 := by
    simpa [prefixWord, tailWord_2796025, baseEnd_2796025] using wordTrace_append hprefix tailTrace_2796025
  have hstable : (prefixWord ++ tailWord_2796025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796025).length < 2 ^ (prefixWord ++ tailWord_2796025).sum := by decide
  have hdescent : baseEnd_2796025 < baseStart_2796025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796092 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_2796092 : Nat := 118140960795 + 2796092 * 2 ^ 59
def prefixEnd_2796092 : Nat := 4983230072969 + 3 ^ 40 * 2796092 * 2
def baseEnd_2796092 : Nat := 478579716730459836963671

theorem tailTrace_2796092 : CollatzResearch.WordTrace tailWord_2796092 prefixEnd_2796092 478579716730459836963671 := by
  unfold tailWord_2796092
  simp only [CollatzResearch.WordTrace]
  refine ⟨50990926693121846670123265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67987902257495795560164353 50990926693121846670123265)
  ·
    refine ⟨38243195019841385002592449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50990926693121846670123265 38243195019841385002592449)
    ·
      refine ⟨28682396264881038751944337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38243195019841385002592449 28682396264881038751944337)
      ·
        refine ⟨21511797198660779063958253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28682396264881038751944337 21511797198660779063958253)
        ·
          refine ⟨8066923949497792148984345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21511797198660779063958253 8066923949497792148984345)
          ·
            refine ⟨6050192962123344111738259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8066923949497792148984345 6050192962123344111738259)
            ·
              refine ⟨9075289443185016167607389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6050192962123344111738259 9075289443185016167607389)
              ·
                refine ⟨3403233541194381062852771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9075289443185016167607389 3403233541194381062852771)
                ·
                  refine ⟨5104850311791571594279157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403233541194381062852771 5104850311791571594279157)
                  ·
                    refine ⟨478579716730459836963671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5104850311791571594279157 478579716730459836963671)
                    ·
                      rfl

theorem cell23_2796092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_2796092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796092 prefixEnd_2796092 := by exact prefixLift 2796092
  have htrace : WordTrace (prefixWord ++ tailWord_2796092) baseStart_2796092 baseEnd_2796092 := by
    simpa [prefixWord, tailWord_2796092, baseEnd_2796092] using wordTrace_append hprefix tailTrace_2796092
  have hstable : (prefixWord ++ tailWord_2796092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796092).length < 2 ^ (prefixWord ++ tailWord_2796092).sum := by decide
  have hdescent : baseEnd_2796092 < baseStart_2796092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796129 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_2796129 : Nat := 118140960795 + 2796129 * 2 ^ 59
def prefixEnd_2796129 : Nat := 4983230072969 + 3 ^ 40 * 2796129 * 2
def baseEnd_2796129 : Nat := 1435758148975595866128343

theorem tailTrace_2796129 : CollatzResearch.WordTrace tailWord_2796129 prefixEnd_2796129 1435758148975595866128343 := by
  unfold tailWord_2796129
  simp only [CollatzResearch.WordTrace]
  refine ⟨101983202887109648659343441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67988801924739765772895627 101983202887109648659343441)
  ·
    refine ⟨76487402165332236494507581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101983202887109648659343441 76487402165332236494507581)
    ·
      refine ⟨28682775811999588685440343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76487402165332236494507581 28682775811999588685440343)
      ·
        refine ⟨43024163717999383028160515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28682775811999588685440343 43024163717999383028160515)
        ·
          refine ⟨64536245576999074542240773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43024163717999383028160515 64536245576999074542240773)
          ·
            refine ⟨12100546045687326476670145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64536245576999074542240773 12100546045687326476670145)
            ·
              refine ⟨9075409534265494857502609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12100546045687326476670145 9075409534265494857502609)
              ·
                refine ⟨6806557150699121143126957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9075409534265494857502609 6806557150699121143126957)
                ·
                  refine ⟨2552458931512170428672609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6806557150699121143126957 2552458931512170428672609)
                  ·
                    refine ⟨1914344198634127821504457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2552458931512170428672609 1914344198634127821504457)
                    ·
                      refine ⟨1435758148975595866128343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914344198634127821504457 1435758148975595866128343)
                      ·
                        rfl

theorem cell23_2796129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_2796129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796129 prefixEnd_2796129 := by exact prefixLift 2796129
  have htrace : WordTrace (prefixWord ++ tailWord_2796129) baseStart_2796129 baseEnd_2796129 := by
    simpa [prefixWord, tailWord_2796129, baseEnd_2796129] using wordTrace_append hprefix tailTrace_2796129
  have hstable : (prefixWord ++ tailWord_2796129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796129).length < 2 ^ (prefixWord ++ tailWord_2796129).sum := by decide
  have hdescent : baseEnd_2796129 < baseStart_2796129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796149 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2796149 : Nat := 118140960795 + 2796149 * 2 ^ 59
def prefixEnd_2796149 : Nat := 4983230072969 + 3 ^ 40 * 2796149 * 2
def baseEnd_2796149 : Nat := 1435768418588685787878251

theorem tailTrace_2796149 : CollatzResearch.WordTrace tailWord_2796149 prefixEnd_2796149 1435768418588685787878251 := by
  unfold tailWord_2796149
  simp only [CollatzResearch.WordTrace]
  refine ⟨101983932347037192075071501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67989288231358128050047667 101983932347037192075071501)
  ·
    refine ⟨38243974630138947028151813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101983932347037192075071501 38243974630138947028151813)
    ·
      refine ⟨7170745243151052567778465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38243974630138947028151813 7170745243151052567778465)
      ·
        refine ⟨5378058932363289425833849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7170745243151052567778465 5378058932363289425833849)
        ·
          refine ⟨4033544199272467069375387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5378058932363289425833849 4033544199272467069375387)
          ·
            refine ⟨6050316298908700604063081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033544199272467069375387 6050316298908700604063081)
            ·
              refine ⟨4537737224181525453047311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6050316298908700604063081 4537737224181525453047311)
              ·
                refine ⟨6806605836272288179570967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537737224181525453047311 6806605836272288179570967)
                ·
                  refine ⟨10209908754408432269356451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6806605836272288179570967 10209908754408432269356451)
                  ·
                    refine ⟨15314863131612648404034677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10209908754408432269356451 15314863131612648404034677)
                    ·
                      refine ⟨1435768418588685787878251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15314863131612648404034677 1435768418588685787878251)
                      ·
                        rfl

theorem cell23_2796149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2796149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796149 prefixEnd_2796149 := by exact prefixLift 2796149
  have htrace : WordTrace (prefixWord ++ tailWord_2796149) baseStart_2796149 baseEnd_2796149 := by
    simpa [prefixWord, tailWord_2796149, baseEnd_2796149] using wordTrace_append hprefix tailTrace_2796149
  have hstable : (prefixWord ++ tailWord_2796149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796149).length < 2 ^ (prefixWord ++ tailWord_2796149).sum := by decide
  have hdescent : baseEnd_2796149 < baseStart_2796149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796214 : List Nat := [5, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_2796214 : Nat := 118140960795 + 2796214 * 2 ^ 59
def prefixEnd_2796214 : Nat := 4983230072969 + 3 ^ 40 * 2796214 * 2
def baseEnd_2796214 : Nat := 1435801794831228033565453

theorem tailTrace_2796214 : CollatzResearch.WordTrace tailWord_2796214 prefixEnd_2796214 1435801794831228033565453 := by
  unfold tailWord_2796214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374143943237606761011731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67990868727867805450791797 6374143943237606761011731)
  ·
    refine ⟨9561215914856410141517597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6374143943237606761011731 9561215914856410141517597)
    ·
      refine ⟨3585455968071153803069099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9561215914856410141517597 3585455968071153803069099)
      ·
        refine ⟨5378183952106730704603649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3585455968071153803069099 5378183952106730704603649)
        ·
          refine ⟨4033637964080048028452737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5378183952106730704603649 4033637964080048028452737)
          ·
            refine ⟨3025228473060036021339553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4033637964080048028452737 3025228473060036021339553)
            ·
              refine ⟨2268921354795027016004665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3025228473060036021339553 2268921354795027016004665)
              ·
                refine ⟨1701691016096270262003499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2268921354795027016004665 1701691016096270262003499)
                ·
                  refine ⟨2552536524144405393005249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701691016096270262003499 2552536524144405393005249)
                  ·
                    refine ⟨1914402393108304044753937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2552536524144405393005249 1914402393108304044753937)
                    ·
                      refine ⟨1435801794831228033565453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914402393108304044753937 1435801794831228033565453)
                      ·
                        rfl

theorem cell23_2796214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_2796214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796214 prefixEnd_2796214 := by exact prefixLift 2796214
  have htrace : WordTrace (prefixWord ++ tailWord_2796214) baseStart_2796214 baseEnd_2796214 := by
    simpa [prefixWord, tailWord_2796214, baseEnd_2796214] using wordTrace_append hprefix tailTrace_2796214
  have hstable : (prefixWord ++ tailWord_2796214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796214).length < 2 ^ (prefixWord ++ tailWord_2796214).sum := by decide
  have hdescent : baseEnd_2796214 < baseStart_2796214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796222 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_2796222 : Nat := 118140960795 + 2796222 * 2 ^ 59
def prefixEnd_2796222 : Nat := 4983230072969 + 3 ^ 40 * 2796222 * 2
def baseEnd_2796222 : Nat := 1435805902676464002265415

theorem tailTrace_2796222 : CollatzResearch.WordTrace tailWord_2796222 prefixEnd_2796222 1435805902676464002265415 := by
  unfold tailWord_2796222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12748324359471590692809865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67991063250515150361652613 12748324359471590692809865)
  ·
    refine ⟨9561243269603693019607399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12748324359471590692809865 9561243269603693019607399)
    ·
      refine ⟨14341864904405539529411099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9561243269603693019607399 14341864904405539529411099)
      ·
        refine ⟨21512797356608309294116649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14341864904405539529411099 21512797356608309294116649)
        ·
          refine ⟨16134598017456231970587487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21512797356608309294116649 16134598017456231970587487)
          ·
            refine ⟨24201897026184347955881231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16134598017456231970587487 24201897026184347955881231)
            ·
              refine ⟨36302845539276521933821847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24201897026184347955881231 36302845539276521933821847)
              ·
                refine ⟨54454268308914782900732771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36302845539276521933821847 54454268308914782900732771)
                ·
                  refine ⟨81681402463372174351099157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54454268308914782900732771 81681402463372174351099157)
                  ·
                    refine ⟨3828815740470570672707773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81681402463372174351099157 3828815740470570672707773)
                    ·
                      refine ⟨1435805902676464002265415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3828815740470570672707773 1435805902676464002265415)
                      ·
                        rfl

theorem cell23_2796222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_2796222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796222 prefixEnd_2796222 := by exact prefixLift 2796222
  have htrace : WordTrace (prefixWord ++ tailWord_2796222) baseStart_2796222 baseEnd_2796222 := by
    simpa [prefixWord, tailWord_2796222, baseEnd_2796222] using wordTrace_append hprefix tailTrace_2796222
  have hstable : (prefixWord ++ tailWord_2796222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796222).length < 2 ^ (prefixWord ++ tailWord_2796222).sum := by decide
  have hdescent : baseEnd_2796222 < baseStart_2796222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796232 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_2796232 : Nat := 118140960795 + 2796232 * 2 ^ 59
def prefixEnd_2796232 : Nat := 4983230072969 + 3 ^ 40 * 2796232 * 2
def baseEnd_2796232 : Nat := 1435811037483008963140369

theorem tailTrace_2796232 : CollatzResearch.WordTrace tailWord_2796232 prefixEnd_2796232 1435811037483008963140369 := by
  unfold tailWord_2796232
  simp only [CollatzResearch.WordTrace]
  refine ⟨50993479802868248625171475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67991306403824331500228633 50993479802868248625171475)
  ·
    refine ⟨76490219704302372937757213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50993479802868248625171475 76490219704302372937757213)
    ·
      refine ⟨28683832389113389851658955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76490219704302372937757213 28683832389113389851658955)
      ·
        refine ⟨43025748583670084777488433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28683832389113389851658955 43025748583670084777488433)
        ·
          refine ⟨32269311437752563583116325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43025748583670084777488433 32269311437752563583116325)
          ·
            refine ⟨6050495894578605671834311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32269311437752563583116325 6050495894578605671834311)
            ·
              refine ⟨9075743841867908507751467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6050495894578605671834311 9075743841867908507751467)
              ·
                refine ⟨13613615762801862761627201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9075743841867908507751467 13613615762801862761627201)
                ·
                  refine ⟨10210211822101397071220401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13613615762801862761627201 10210211822101397071220401)
                  ·
                    refine ⟨7657658866576047803415301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10210211822101397071220401 7657658866576047803415301)
                    ·
                      refine ⟨1435811037483008963140369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7657658866576047803415301 1435811037483008963140369)
                      ·
                        rfl

theorem cell23_2796232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_2796232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796232 prefixEnd_2796232 := by exact prefixLift 2796232
  have htrace : WordTrace (prefixWord ++ tailWord_2796232) baseStart_2796232 baseEnd_2796232 := by
    simpa [prefixWord, tailWord_2796232, baseEnd_2796232] using wordTrace_append hprefix tailTrace_2796232
  have hstable : (prefixWord ++ tailWord_2796232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796232).length < 2 ^ (prefixWord ++ tailWord_2796232).sum := by decide
  have hdescent : baseEnd_2796232 < baseStart_2796232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796236 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 1, 4, 2]
def baseStart_2796236 : Nat := 118140960795 + 2796236 * 2 ^ 59
def prefixEnd_2796236 : Nat := 4983230072969 + 3 ^ 40 * 2796236 * 2
def baseEnd_2796236 : Nat := 1435813091405626947490351

theorem tailTrace_2796236 : CollatzResearch.WordTrace tailWord_2796236 prefixEnd_2796236 1435813091405626947490351 := by
  unfold tailWord_2796236
  simp only [CollatzResearch.WordTrace]
  refine ⟨50993552748861002966744281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67991403665148003955659041 50993552748861002966744281)
  ·
    refine ⟨38245164561645752225058211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50993552748861002966744281 38245164561645752225058211)
    ·
      refine ⟨57367746842468628337587317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38245164561645752225058211 57367746842468628337587317)
      ·
        refine ⟨5378226266481433906648811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57367746842468628337587317 5378226266481433906648811)
        ·
          refine ⟨8067339399722150859973217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5378226266481433906648811 8067339399722150859973217)
          ·
            refine ⟨6050504549791613144979913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8067339399722150859973217 6050504549791613144979913)
            ·
              refine ⟨4537878412343709858734935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6050504549791613144979913 4537878412343709858734935)
              ·
                refine ⟨6806817618515564788102403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537878412343709858734935 6806817618515564788102403)
                ·
                  refine ⟨10210226427773347182153605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6806817618515564788102403 10210226427773347182153605)
                  ·
                    refine ⟨1914417455207502596653801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10210226427773347182153605 1914417455207502596653801)
                    ·
                      refine ⟨1435813091405626947490351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914417455207502596653801 1435813091405626947490351)
                      ·
                        rfl

theorem cell23_2796236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_2796236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796236 prefixEnd_2796236 := by exact prefixLift 2796236
  have htrace : WordTrace (prefixWord ++ tailWord_2796236) baseStart_2796236 baseEnd_2796236 := by
    simpa [prefixWord, tailWord_2796236, baseEnd_2796236] using wordTrace_append hprefix tailTrace_2796236
  have hstable : (prefixWord ++ tailWord_2796236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796236).length < 2 ^ (prefixWord ++ tailWord_2796236).sum := by decide
  have hdescent : baseEnd_2796236 < baseStart_2796236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796259 : List Nat := [1, 1, 1, 7, 1, 1, 1, 5, 5]
def baseStart_2796259 : Nat := 118140960795 + 2796259 * 2 ^ 59
def prefixEnd_2796259 : Nat := 4983230072969 + 3 ^ 40 * 2796259 * 2
def baseEnd_2796259 : Nat := 159536100162297817500305

theorem tailTrace_2796259 : CollatzResearch.WordTrace tailWord_2796259 prefixEnd_2796259 159536100162297817500305 := by
  unfold tailWord_2796259
  simp only [CollatzResearch.WordTrace]
  refine ⟨101987944376638680861575831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67991962917759120574383887 101987944376638680861575831)
  ·
    refine ⟨152981916564958021292363747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101987944376638680861575831 152981916564958021292363747)
    ·
      refine ⟨229472874847437031938545621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152981916564958021292363747 229472874847437031938545621)
      ·
        refine ⟨5378270504236805436059663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 229472874847437031938545621 5378270504236805436059663)
        ·
          refine ⟨8067405756355208154089495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5378270504236805436059663 8067405756355208154089495)
          ·
            refine ⟨12101108634532812231134243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8067405756355208154089495 12101108634532812231134243)
            ·
              refine ⟨18151662951799218346701365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12101108634532812231134243 18151662951799218346701365)
              ·
                refine ⟨1701718401731176720003253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18151662951799218346701365 1701718401731176720003253)
                ·
                  refine ⟨159536100162297817500305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1701718401731176720003253 159536100162297817500305)
                  ·
                    rfl

theorem cell23_2796259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 5].length) (baseStart_2796259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796259 prefixEnd_2796259 := by exact prefixLift 2796259
  have htrace : WordTrace (prefixWord ++ tailWord_2796259) baseStart_2796259 baseEnd_2796259 := by
    simpa [prefixWord, tailWord_2796259, baseEnd_2796259] using wordTrace_append hprefix tailTrace_2796259
  have hstable : (prefixWord ++ tailWord_2796259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796259).length < 2 ^ (prefixWord ++ tailWord_2796259).sum := by decide
  have hdescent : baseEnd_2796259 < baseStart_2796259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796265 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_2796265 : Nat := 118140960795 + 2796265 * 2 ^ 59
def prefixEnd_2796265 : Nat := 4983230072969 + 3 ^ 40 * 2796265 * 2
def baseEnd_2796265 : Nat := 1435827982344607334027717

theorem tailTrace_2796265 : CollatzResearch.WordTrace tailWord_2796265 prefixEnd_2796265 1435827982344607334027717 := by
  unfold tailWord_2796265
  simp only [CollatzResearch.WordTrace]
  refine ⟨101988163214616943886294249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67992108809744629257529499 101988163214616943886294249)
  ·
    refine ⟨76491122410962707914720687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101988163214616943886294249 76491122410962707914720687)
    ·
      refine ⟨114736683616444061872081031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76491122410962707914720687 114736683616444061872081031)
      ·
        refine ⟨172105025424666092808121547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114736683616444061872081031 172105025424666092808121547)
        ·
          refine ⟨258157538136999139212182321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172105025424666092808121547 258157538136999139212182321)
          ·
            refine ⟨193618153602749354409136741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258157538136999139212182321 193618153602749354409136741)
            ·
              refine ⟨36303403800515503951713139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193618153602749354409136741 36303403800515503951713139)
              ·
                refine ⟨54455105700773255927569709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36303403800515503951713139 54455105700773255927569709)
                ·
                  refine ⟨20420664637789970972838641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54455105700773255927569709 20420664637789970972838641)
                  ·
                    refine ⟨15315498478342478229628981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20420664637789970972838641 15315498478342478229628981)
                    ·
                      refine ⟨1435827982344607334027717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15315498478342478229628981 1435827982344607334027717)
                      ·
                        rfl

theorem cell23_2796265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_2796265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796265 prefixEnd_2796265 := by exact prefixLift 2796265
  have htrace : WordTrace (prefixWord ++ tailWord_2796265) baseStart_2796265 baseEnd_2796265 := by
    simpa [prefixWord, tailWord_2796265, baseEnd_2796265] using wordTrace_append hprefix tailTrace_2796265
  have hstable : (prefixWord ++ tailWord_2796265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796265).length < 2 ^ (prefixWord ++ tailWord_2796265).sum := by decide
  have hdescent : baseEnd_2796265 < baseStart_2796265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796292 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2796292 : Nat := 118140960795 + 2796292 * 2 ^ 59
def prefixEnd_2796292 : Nat := 4983230072969 + 3 ^ 40 * 2796292 * 2
def baseEnd_2796292 : Nat := 1435841846322278728390093

theorem tailTrace_2796292 : CollatzResearch.WordTrace tailWord_2796292 prefixEnd_2796292 1435841846322278728390093 := by
  unfold tailWord_2796292
  simp only [CollatzResearch.WordTrace]
  refine ⟨50994573992759563748763565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67992765323679418331684753 50994573992759563748763565)
  ·
    refine ⟨19122965247284836405786337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50994573992759563748763565 19122965247284836405786337)
    ·
      refine ⟨14342223935463627304339753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19122965247284836405786337 14342223935463627304339753)
      ·
        refine ⟨10756667951597720478254815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14342223935463627304339753 10756667951597720478254815)
        ·
          refine ⟨16135001927396580717382223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10756667951597720478254815 16135001927396580717382223)
          ·
            refine ⟨24202502891094871076073335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16135001927396580717382223 24202502891094871076073335)
            ·
              refine ⟨36303754336642306614110003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24202502891094871076073335 36303754336642306614110003)
              ·
                refine ⟨54455631504963459921165005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36303754336642306614110003 54455631504963459921165005)
                ·
                  refine ⟨20420861814361297470436877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54455631504963459921165005 20420861814361297470436877)
                  ·
                    refine ⟨7657823180385486551413829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20420861814361297470436877 7657823180385486551413829)
                    ·
                      refine ⟨1435841846322278728390093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7657823180385486551413829 1435841846322278728390093)
                      ·
                        rfl

theorem cell23_2796292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2796292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796292 prefixEnd_2796292 := by exact prefixLift 2796292
  have htrace : WordTrace (prefixWord ++ tailWord_2796292) baseStart_2796292 baseEnd_2796292 := by
    simpa [prefixWord, tailWord_2796292, baseEnd_2796292] using wordTrace_append hprefix tailTrace_2796292
  have hstable : (prefixWord ++ tailWord_2796292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796292).length < 2 ^ (prefixWord ++ tailWord_2796292).sum := by decide
  have hdescent : baseEnd_2796292 < baseStart_2796292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796332 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 6]
def baseStart_2796332 : Nat := 118140960795 + 2796332 * 2 ^ 59
def prefixEnd_2796332 : Nat := 4983230072969 + 3 ^ 40 * 2796332 * 2
def baseEnd_2796332 : Nat := 159540265060939841321101

theorem tailTrace_2796332 : CollatzResearch.WordTrace tailWord_2796332 prefixEnd_2796332 159540265060939841321101 := by
  unfold tailWord_2796332
  simp only [CollatzResearch.WordTrace]
  refine ⟨50995303452687107164491625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67993737936916142885988833 50995303452687107164491625)
  ·
    refine ⟨38246477589515330373368719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50995303452687107164491625 38246477589515330373368719)
    ·
      refine ⟨57369716384272995560053079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38246477589515330373368719 57369716384272995560053079)
      ·
        refine ⟨86054574576409493340079619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57369716384272995560053079 86054574576409493340079619)
        ·
          refine ⟨129081861864614240010119429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86054574576409493340079619 129081861864614240010119429)
          ·
            refine ⟨24202849099615170001897393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129081861864614240010119429 24202849099615170001897393)
            ·
              refine ⟨18152136824711377501423045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24202849099615170001897393 18152136824711377501423045)
              ·
                refine ⟨3403525654633383281516821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18152136824711377501423045 3403525654633383281516821)
                ·
                  refine ⟨159540265060939841321101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3403525654633383281516821 159540265060939841321101)
                  ·
                    rfl

theorem cell23_2796332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_2796332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796332 prefixEnd_2796332 := by exact prefixLift 2796332
  have htrace : WordTrace (prefixWord ++ tailWord_2796332) baseStart_2796332 baseEnd_2796332 := by
    simpa [prefixWord, tailWord_2796332, baseEnd_2796332] using wordTrace_append hprefix tailTrace_2796332
  have hstable : (prefixWord ++ tailWord_2796332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796332).length < 2 ^ (prefixWord ++ tailWord_2796332).sum := by decide
  have hdescent : baseEnd_2796332 < baseStart_2796332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796359 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_2796359 : Nat := 118140960795 + 2796359 * 2 ^ 59
def prefixEnd_2796359 : Nat := 4983230072969 + 3 ^ 40 * 2796359 * 2
def baseEnd_2796359 : Nat := 1435876249526129966252285

theorem tailTrace_2796359 : CollatzResearch.WordTrace tailWord_2796359 prefixEnd_2796359 1435876249526129966252285 := by
  unfold tailWord_2796359
  simp only [CollatzResearch.WordTrace]
  refine ⟨101991591676276397940216131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67994394450850931960144087 101991591676276397940216131)
  ·
    refine ⟨152987387514414596910324197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101991591676276397940216131 152987387514414596910324197)
    ·
      refine ⟨28685135158952736920685787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152987387514414596910324197 28685135158952736920685787)
      ·
        refine ⟨43027702738429105381028681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28685135158952736920685787 43027702738429105381028681)
        ·
          refine ⟨32270777053821829035771511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43027702738429105381028681 32270777053821829035771511)
          ·
            refine ⟨48406165580732743553657267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32270777053821829035771511 48406165580732743553657267)
            ·
              refine ⟨72609248371099115330485901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48406165580732743553657267 72609248371099115330485901)
              ·
                refine ⟨27228468139162168248932213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72609248371099115330485901 27228468139162168248932213)
                ·
                  refine ⟨2552668888046453273337395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27228468139162168248932213 2552668888046453273337395)
                  ·
                    refine ⟨3829003332069679910006093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2552668888046453273337395 3829003332069679910006093)
                    ·
                      refine ⟨1435876249526129966252285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3829003332069679910006093 1435876249526129966252285)
                      ·
                        rfl

theorem cell23_2796359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_2796359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796359 prefixEnd_2796359 := by exact prefixLift 2796359
  have htrace : WordTrace (prefixWord ++ tailWord_2796359) baseStart_2796359 baseEnd_2796359 := by
    simpa [prefixWord, tailWord_2796359, baseEnd_2796359] using wordTrace_append hprefix tailTrace_2796359
  have hstable : (prefixWord ++ tailWord_2796359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796359).length < 2 ^ (prefixWord ++ tailWord_2796359).sum := by decide
  have hdescent : baseEnd_2796359 < baseStart_2796359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796409 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 1, 6]
def baseStart_2796409 : Nat := 118140960795 + 2796409 * 2 ^ 59
def prefixEnd_2796409 : Nat := 4983230072969 + 3 ^ 40 * 2796409 * 2
def baseEnd_2796409 : Nat := 478633974519618256875685

theorem tailTrace_2796409 : CollatzResearch.WordTrace tailWord_2796409 prefixEnd_2796409 478633974519618256875685 := by
  unfold tailWord_2796409
  simp only [CollatzResearch.WordTrace]
  refine ⟨101993415326095256479536281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67995610217396837653024187 101993415326095256479536281)
  ·
    refine ⟨76495061494571442359652211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101993415326095256479536281 76495061494571442359652211)
    ·
      refine ⟨114742592241857163539478317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76495061494571442359652211 114742592241857163539478317)
      ·
        refine ⟨43028472090696436327304369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114742592241857163539478317 43028472090696436327304369)
        ·
          refine ⟨32271354068022327245478277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43028472090696436327304369 32271354068022327245478277)
          ·
            refine ⟨6050878887754186358527177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32271354068022327245478277 6050878887754186358527177)
            ·
              refine ⟨4538159165815639768895383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6050878887754186358527177 4538159165815639768895383)
              ·
                refine ⟨6807238748723459653343075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538159165815639768895383 6807238748723459653343075)
                ·
                  refine ⟨10210858123085189480014613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6807238748723459653343075 10210858123085189480014613)
                  ·
                    refine ⟨478633974519618256875685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10210858123085189480014613 478633974519618256875685)
                    ·
                      rfl

theorem cell23_2796409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_2796409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796409 prefixEnd_2796409 := by exact prefixLift 2796409
  have htrace : WordTrace (prefixWord ++ tailWord_2796409) baseStart_2796409 baseEnd_2796409 := by
    simpa [prefixWord, tailWord_2796409, baseEnd_2796409] using wordTrace_append hprefix tailTrace_2796409
  have hstable : (prefixWord ++ tailWord_2796409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796409).length < 2 ^ (prefixWord ++ tailWord_2796409).sum := by decide
  have hdescent : baseEnd_2796409 < baseStart_2796409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796412 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2796412 : Nat := 118140960795 + 2796412 * 2 ^ 59
def prefixEnd_2796412 : Nat := 4983230072969 + 3 ^ 40 * 2796412 * 2
def baseEnd_2796412 : Nat := 1435903464000818258889541

theorem tailTrace_2796412 : CollatzResearch.WordTrace tailWord_2796412 prefixEnd_2796412 1435903464000818258889541 := by
  unfold tailWord_2796412
  simp only [CollatzResearch.WordTrace]
  refine ⟨50996762372542193995947745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67995683163389591994596993 50996762372542193995947745)
  ·
    refine ⟨38247571779406645496960809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50996762372542193995947745 38247571779406645496960809)
    ·
      refine ⟨28685678834554984122720607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38247571779406645496960809 28685678834554984122720607)
      ·
        refine ⟨43028518251832476184080911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28685678834554984122720607 43028518251832476184080911)
        ·
          refine ⟨64542777377748714276121367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43028518251832476184080911 64542777377748714276121367)
          ·
            refine ⟨96814166066623071414182051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64542777377748714276121367 96814166066623071414182051)
            ·
              refine ⟨145221249099934607121273077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96814166066623071414182051 145221249099934607121273077)
              ·
                refine ⟨13614492103118869417619351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145221249099934607121273077 13614492103118869417619351)
                ·
                  refine ⟨20421738154678304126429027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13614492103118869417619351 20421738154678304126429027)
                  ·
                    refine ⟨30632607232017456189643541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20421738154678304126429027 30632607232017456189643541)
                    ·
                      refine ⟨1435903464000818258889541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30632607232017456189643541 1435903464000818258889541)
                      ·
                        rfl

theorem cell23_2796412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2796412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796412 prefixEnd_2796412 := by exact prefixLift 2796412
  have htrace : WordTrace (prefixWord ++ tailWord_2796412) baseStart_2796412 baseEnd_2796412 := by
    simpa [prefixWord, tailWord_2796412, baseEnd_2796412] using wordTrace_append hprefix tailTrace_2796412
  have hstable : (prefixWord ++ tailWord_2796412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796412).length < 2 ^ (prefixWord ++ tailWord_2796412).sum := by decide
  have hdescent : baseEnd_2796412 < baseStart_2796412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796419 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 3]
def baseStart_2796419 : Nat := 118140960795 + 2796419 * 2 ^ 59
def prefixEnd_2796419 : Nat := 4983230072969 + 3 ^ 40 * 2796419 * 2
def baseEnd_2796419 : Nat := 1435907058365399731502009

theorem tailTrace_2796419 : CollatzResearch.WordTrace tailWord_2796419 prefixEnd_2796419 1435907058365399731502009 := by
  unfold tailWord_2796419
  simp only [CollatzResearch.WordTrace]
  refine ⟨101993780056059028187400311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67995853370706018791600207 101993780056059028187400311)
  ·
    refine ⟨152990670084088542281100467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101993780056059028187400311 152990670084088542281100467)
    ·
      refine ⟨229486005126132813421650701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152990670084088542281100467 229486005126132813421650701)
      ·
        refine ⟨86057251922299805033119013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229486005126132813421650701 86057251922299805033119013)
        ·
          refine ⟨16135734735431213443709815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86057251922299805033119013 16135734735431213443709815)
          ·
            refine ⟨24203602103146820165564723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16135734735431213443709815 24203602103146820165564723)
            ·
              refine ⟨36305403154720230248347085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24203602103146820165564723 36305403154720230248347085)
              ·
                refine ⟨13614526183020086343130157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36305403154720230248347085 13614526183020086343130157)
                ·
                  refine ⟨5105447318632532378673809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13614526183020086343130157 5105447318632532378673809)
                  ·
                    refine ⟨3829085488974399284005357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5105447318632532378673809 3829085488974399284005357)
                    ·
                      refine ⟨1435907058365399731502009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3829085488974399284005357 1435907058365399731502009)
                      ·
                        rfl

theorem cell23_2796419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_2796419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796419 prefixEnd_2796419 := by exact prefixLift 2796419
  have htrace : WordTrace (prefixWord ++ tailWord_2796419) baseStart_2796419 baseEnd_2796419 := by
    simpa [prefixWord, tailWord_2796419, baseEnd_2796419] using wordTrace_append hprefix tailTrace_2796419
  have hstable : (prefixWord ++ tailWord_2796419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796419).length < 2 ^ (prefixWord ++ tailWord_2796419).sum := by decide
  have hdescent : baseEnd_2796419 < baseStart_2796419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796450 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_2796450 : Nat := 118140960795 + 2796450 * 2 ^ 59
def prefixEnd_2796450 : Nat := 4983230072969 + 3 ^ 40 * 2796450 * 2
def baseEnd_2796450 : Nat := 1435922976265689110214367

theorem tailTrace_2796450 : CollatzResearch.WordTrace tailWord_2796450 prefixEnd_2796450 1435922976265689110214367 := by
  unfold tailWord_2796450
  simp only [CollatzResearch.WordTrace]
  refine ⟨25498727679736680120444701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67996607145964480321185869 25498727679736680120444701)
  ·
    refine ⟨9562022879901255045166763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25498727679736680120444701 9562022879901255045166763)
    ·
      refine ⟨14343034319851882567750145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9562022879901255045166763 14343034319851882567750145)
      ·
        refine ⟨10757275739888911925812609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14343034319851882567750145 10757275739888911925812609)
        ·
          refine ⟨8067956804916683944359457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10757275739888911925812609 8067956804916683944359457)
          ·
            refine ⟨6050967603687512958269593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8067956804916683944359457 6050967603687512958269593)
            ·
              refine ⟨4538225702765634718702195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6050967603687512958269593 4538225702765634718702195)
              ·
                refine ⟨6807338554148452078053293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538225702765634718702195 6807338554148452078053293)
                ·
                  refine ⟨2552751957805669529269985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6807338554148452078053293 2552751957805669529269985)
                  ·
                    refine ⟨1914563968354252146952489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2552751957805669529269985 1914563968354252146952489)
                    ·
                      refine ⟨1435922976265689110214367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914563968354252146952489 1435922976265689110214367)
                      ·
                        rfl

theorem cell23_2796450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_2796450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796450 prefixEnd_2796450 := by exact prefixLift 2796450
  have htrace : WordTrace (prefixWord ++ tailWord_2796450) baseStart_2796450 baseEnd_2796450 := by
    simpa [prefixWord, tailWord_2796450, baseEnd_2796450] using wordTrace_append hprefix tailTrace_2796450
  have hstable : (prefixWord ++ tailWord_2796450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796450).length < 2 ^ (prefixWord ++ tailWord_2796450).sum := by decide
  have hdescent : baseEnd_2796450 < baseStart_2796450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796539 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 3]
def baseStart_2796539 : Nat := 118140960795 + 2796539 * 2 ^ 59
def prefixEnd_2796539 : Nat := 4983230072969 + 3 ^ 40 * 2796539 * 2
def baseEnd_2796539 : Nat := 1435968676043939262001457

theorem tailTrace_2796539 : CollatzResearch.WordTrace tailWord_2796539 prefixEnd_2796539 1435968676043939262001457 := by
  unfold tailWord_2796539
  simp only [CollatzResearch.WordTrace]
  refine ⟨101998156815624288681768671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67998771210416192454512447 101998156815624288681768671)
  ·
    refine ⟨152997235223436433022653007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101998156815624288681768671 152997235223436433022653007)
    ·
      refine ⟨229495852835154649533979511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152997235223436433022653007 229495852835154649533979511)
      ·
        refine ⟨344243779252731974300969267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229495852835154649533979511 344243779252731974300969267)
        ·
          refine ⟨516365668879097961451453901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344243779252731974300969267 516365668879097961451453901)
          ·
            refine ⟨193637125829661735544295213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516365668879097961451453901 193637125829661735544295213)
            ·
              refine ⟨72613922186123150829110705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193637125829661735544295213 72613922186123150829110705)
              ·
                refine ⟨54460441639592363121833029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72613922186123150829110705 54460441639592363121833029)
                ·
                  refine ⟨10211332807423568085343693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54460441639592363121833029 10211332807423568085343693)
                  ·
                    refine ⟨3829249802783838032003885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10211332807423568085343693 3829249802783838032003885)
                    ·
                      refine ⟨1435968676043939262001457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3829249802783838032003885 1435968676043939262001457)
                      ·
                        rfl

theorem cell23_2796539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 3].length) (baseStart_2796539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796539 prefixEnd_2796539 := by exact prefixLift 2796539
  have htrace : WordTrace (prefixWord ++ tailWord_2796539) baseStart_2796539 baseEnd_2796539 := by
    simpa [prefixWord, tailWord_2796539, baseEnd_2796539] using wordTrace_append hprefix tailTrace_2796539
  have hstable : (prefixWord ++ tailWord_2796539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796539).length < 2 ^ (prefixWord ++ tailWord_2796539).sum := by decide
  have hdescent : baseEnd_2796539 < baseStart_2796539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796569 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_2796569 : Nat := 118140960795 + 2796569 * 2 ^ 59
def prefixEnd_2796569 : Nat := 4983230072969 + 3 ^ 40 * 2796569 * 2
def baseEnd_2796569 : Nat := 1435984080463574144626319

theorem tailTrace_2796569 : CollatzResearch.WordTrace tailWord_2796569 prefixEnd_2796569 1435984080463574144626319 := by
  unfold tailWord_2796569
  simp only [CollatzResearch.WordTrace]
  refine ⟨101999251005515603805360761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67999500670343735870240507 101999251005515603805360761)
  ·
    refine ⟨76499438254136702854020571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101999251005515603805360761 76499438254136702854020571)
    ·
      refine ⟨114749157381205054281030857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76499438254136702854020571 114749157381205054281030857)
      ·
        refine ⟨86061868035903790710773143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114749157381205054281030857 86061868035903790710773143)
        ·
          refine ⟨129092802053855686066159715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86061868035903790710773143 129092802053855686066159715)
          ·
            refine ⟨193639203080783529099239573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129092802053855686066159715 193639203080783529099239573)
            ·
              refine ⟨9076837644411727926526855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 193639203080783529099239573 9076837644411727926526855)
              ·
                refine ⟨13615256466617591889790283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9076837644411727926526855 13615256466617591889790283)
                ·
                  refine ⟨20422884699926387834685425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13615256466617591889790283 20422884699926387834685425)
                  ·
                    refine ⟨15317163524944790876014069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20422884699926387834685425 15317163524944790876014069)
                    ·
                      refine ⟨1435984080463574144626319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15317163524944790876014069 1435984080463574144626319)
                      ·
                        rfl

theorem cell23_2796569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_2796569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796569 prefixEnd_2796569 := by exact prefixLift 2796569
  have htrace : WordTrace (prefixWord ++ tailWord_2796569) baseStart_2796569 baseEnd_2796569 := by
    simpa [prefixWord, tailWord_2796569, baseEnd_2796569] using wordTrace_append hprefix tailTrace_2796569
  have hstable : (prefixWord ++ tailWord_2796569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796569).length < 2 ^ (prefixWord ++ tailWord_2796569).sum := by decide
  have hdescent : baseEnd_2796569 < baseStart_2796569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796573 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2796573 : Nat := 118140960795 + 2796573 * 2 ^ 59
def prefixEnd_2796573 : Nat := 4983230072969 + 3 ^ 40 * 2796573 * 2
def baseEnd_2796573 : Nat := 1435986134386192128976301

theorem tailTrace_2796573 : CollatzResearch.WordTrace tailWord_2796573 prefixEnd_2796573 1435986134386192128976301 := by
  unfold tailWord_2796573
  simp only [CollatzResearch.WordTrace]
  refine ⟨101999396897501112488506373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67999597931667408325670915 101999396897501112488506373)
  ·
    refine ⟨19124886918281458591594945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101999396897501112488506373 19124886918281458591594945)
    ·
      refine ⟨14343665188711093943696209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19124886918281458591594945 14343665188711093943696209)
      ·
        refine ⟨10757748891533320457772157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14343665188711093943696209 10757748891533320457772157)
        ·
          refine ⟨4034155834324995171664559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10757748891533320457772157 4034155834324995171664559)
          ·
            refine ⟨6051233751487492757496839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034155834324995171664559 6051233751487492757496839)
            ·
              refine ⟨9076850627231239136245259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051233751487492757496839 9076850627231239136245259)
              ·
                refine ⟨13615275940846858704367889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9076850627231239136245259 13615275940846858704367889)
                ·
                  refine ⟨10211456955635144028275917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13615275940846858704367889 10211456955635144028275917)
                  ·
                    refine ⟨3829296358363179010603469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10211456955635144028275917 3829296358363179010603469)
                    ·
                      refine ⟨1435986134386192128976301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3829296358363179010603469 1435986134386192128976301)
                      ·
                        rfl

theorem cell23_2796573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2796573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796573 prefixEnd_2796573 := by exact prefixLift 2796573
  have htrace : WordTrace (prefixWord ++ tailWord_2796573) baseStart_2796573 baseEnd_2796573 := by
    simpa [prefixWord, tailWord_2796573, baseEnd_2796573] using wordTrace_append hprefix tailTrace_2796573
  have hstable : (prefixWord ++ tailWord_2796573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796573).length < 2 ^ (prefixWord ++ tailWord_2796573).sum := by decide
  have hdescent : baseEnd_2796573 < baseStart_2796573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796616 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_2796616 : Nat := 118140960795 + 2796616 * 2 ^ 59
def prefixEnd_2796616 : Nat := 4983230072969 + 3 ^ 40 * 2796616 * 2
def baseEnd_2796616 : Nat := 1436008214054335460738603

theorem tailTrace_2796616 : CollatzResearch.WordTrace tailWord_2796616 prefixEnd_2796616 1436008214054335460738603 := by
  unfold tailWord_2796616
  simp only [CollatzResearch.WordTrace]
  refine ⟨51000482618172665416160851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68000643490896887221547801 51000482618172665416160851)
  ·
    refine ⟨76500723927258998124241277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51000482618172665416160851 76500723927258998124241277)
    ·
      refine ⟨28687771472722124296590479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76500723927258998124241277 28687771472722124296590479)
      ·
        refine ⟨43031657209083186444885719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28687771472722124296590479 43031657209083186444885719)
        ·
          refine ⟨64547485813624779667328579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43031657209083186444885719 64547485813624779667328579)
          ·
            refine ⟨96821228720437169500992869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64547485813624779667328579 96821228720437169500992869)
            ·
              refine ⟨18153980385081969281436163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96821228720437169500992869 18153980385081969281436163)
              ·
                refine ⟨27230970577622953922154245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18153980385081969281436163 27230970577622953922154245)
                ·
                  refine ⟨5105806983304303860403921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27230970577622953922154245 5105806983304303860403921)
                  ·
                    refine ⟨3829355237478227895302941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5105806983304303860403921 3829355237478227895302941)
                    ·
                      refine ⟨1436008214054335460738603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3829355237478227895302941 1436008214054335460738603)
                      ·
                        rfl

theorem cell23_2796616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_2796616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796616 prefixEnd_2796616 := by exact prefixLift 2796616
  have htrace : WordTrace (prefixWord ++ tailWord_2796616) baseStart_2796616 baseEnd_2796616 := by
    simpa [prefixWord, tailWord_2796616, baseEnd_2796616] using wordTrace_append hprefix tailTrace_2796616
  have hstable : (prefixWord ++ tailWord_2796616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796616).length < 2 ^ (prefixWord ++ tailWord_2796616).sum := by decide
  have hdescent : baseEnd_2796616 < baseStart_2796616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796639 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_2796639 : Nat := 118140960795 + 2796639 * 2 ^ 59
def prefixEnd_2796639 : Nat := 4983230072969 + 3 ^ 40 * 2796639 * 2
def baseEnd_2796639 : Nat := 1436020024109388870750997

theorem tailTrace_2796639 : CollatzResearch.WordTrace tailWord_2796639 prefixEnd_2796639 1436020024109388870750997 := by
  unfold tailWord_2796639
  simp only [CollatzResearch.WordTrace]
  refine ⟨102001804115262005760408971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68001202743508003840272647 102001804115262005760408971)
  ·
    refine ⟨153002706172893008640613457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102001804115262005760408971 153002706172893008640613457)
    ·
      refine ⟨114752029629669756480460093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153002706172893008640613457 114752029629669756480460093)
      ·
        refine ⟨43032011111126158680172535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114752029629669756480460093 43032011111126158680172535)
        ·
          refine ⟨64548016666689238020258803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43032011111126158680172535 64548016666689238020258803)
          ·
            refine ⟨96822025000033857030388205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64548016666689238020258803 96822025000033857030388205)
            ·
              refine ⟨36308259375012696386395577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96822025000033857030388205 36308259375012696386395577)
              ·
                refine ⟨27231194531259522289796683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36308259375012696386395577 27231194531259522289796683)
                ·
                  refine ⟨40846791796889283434695025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27231194531259522289796683 40846791796889283434695025)
                  ·
                    refine ⟨30635093847666962576021269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40846791796889283434695025 30635093847666962576021269)
                    ·
                      refine ⟨1436020024109388870750997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30635093847666962576021269 1436020024109388870750997)
                      ·
                        rfl

theorem cell23_2796639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_2796639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796639 prefixEnd_2796639 := by exact prefixLift 2796639
  have htrace : WordTrace (prefixWord ++ tailWord_2796639) baseStart_2796639 baseEnd_2796639 := by
    simpa [prefixWord, tailWord_2796639, baseEnd_2796639] using wordTrace_append hprefix tailTrace_2796639
  have hstable : (prefixWord ++ tailWord_2796639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796639).length < 2 ^ (prefixWord ++ tailWord_2796639).sum := by decide
  have hdescent : baseEnd_2796639 < baseStart_2796639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796700 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_2796700 : Nat := 118140960795 + 2796700 * 2 ^ 59
def prefixEnd_2796700 : Nat := 4983230072969 + 3 ^ 40 * 2796700 * 2
def baseEnd_2796700 : Nat := 478683782143104377362739

theorem tailTrace_2796700 : CollatzResearch.WordTrace tailWord_2796700 prefixEnd_2796700 478683782143104377362739 := by
  unfold tailWord_2796700
  simp only [CollatzResearch.WordTrace]
  refine ⟨51002014484020506589189777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68002685978694008785586369 51002014484020506589189777)
  ·
    refine ⟨38251510863015379941892333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51002014484020506589189777 38251510863015379941892333)
    ·
      refine ⟨14344316573630767478209625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38251510863015379941892333 14344316573630767478209625)
      ·
        refine ⟨10758237430223075608657219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14344316573630767478209625 10758237430223075608657219)
        ·
          refine ⟨16137356145334613412985829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10758237430223075608657219 16137356145334613412985829)
          ·
            refine ⟨3025754277250240014934843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16137356145334613412985829 3025754277250240014934843)
            ·
              refine ⟨4538631415875360022402265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025754277250240014934843 4538631415875360022402265)
              ·
                refine ⟨3403973561906520016801699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4538631415875360022402265 3403973561906520016801699)
                ·
                  refine ⟨5105960342859780025202549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403973561906520016801699 5105960342859780025202549)
                  ·
                    refine ⟨478683782143104377362739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5105960342859780025202549 478683782143104377362739)
                    ·
                      rfl

theorem cell23_2796700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_2796700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796700 prefixEnd_2796700 := by exact prefixLift 2796700
  have htrace : WordTrace (prefixWord ++ tailWord_2796700) baseStart_2796700 baseEnd_2796700 := by
    simpa [prefixWord, tailWord_2796700, baseEnd_2796700] using wordTrace_append hprefix tailTrace_2796700
  have hstable : (prefixWord ++ tailWord_2796700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796700).length < 2 ^ (prefixWord ++ tailWord_2796700).sum := by decide
  have hdescent : baseEnd_2796700 < baseStart_2796700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796717 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2796717 : Nat := 118140960795 + 2796717 * 2 ^ 59
def prefixEnd_2796717 : Nat := 4983230072969 + 3 ^ 40 * 2796717 * 2
def baseEnd_2796717 : Nat := 478686691866813188525213

theorem tailTrace_2796717 : CollatzResearch.WordTrace tailWord_2796717 prefixEnd_2796717 478686691866813188525213 := by
  unfold tailWord_2796717
  simp only [CollatzResearch.WordTrace]
  refine ⟨102004649008979425081748405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68003099339319616721165603 102004649008979425081748405)
  ·
    refine ⟨9562935844591821101413913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102004649008979425081748405 9562935844591821101413913)
    ·
      refine ⟨7172201883443865826060435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9562935844591821101413913 7172201883443865826060435)
      ·
        refine ⟨10758302825165798739090653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7172201883443865826060435 10758302825165798739090653)
        ·
          refine ⟨4034363559437174527158995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10758302825165798739090653 4034363559437174527158995)
          ·
            refine ⟨6051545339155761790738493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034363559437174527158995 6051545339155761790738493)
            ·
              refine ⟨2269329502183410671526935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6051545339155761790738493 2269329502183410671526935)
              ·
                refine ⟨3403994253275116007290403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269329502183410671526935 3403994253275116007290403)
                ·
                  refine ⟨5105991379912674010935605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403994253275116007290403 5105991379912674010935605)
                  ·
                    refine ⟨478686691866813188525213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5105991379912674010935605 478686691866813188525213)
                    ·
                      rfl

theorem cell23_2796717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2796717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796717 prefixEnd_2796717 := by exact prefixLift 2796717
  have htrace : WordTrace (prefixWord ++ tailWord_2796717) baseStart_2796717 baseEnd_2796717 := by
    simpa [prefixWord, tailWord_2796717, baseEnd_2796717] using wordTrace_append hprefix tailTrace_2796717
  have hstable : (prefixWord ++ tailWord_2796717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796717).length < 2 ^ (prefixWord ++ tailWord_2796717).sum := by decide
  have hdescent : baseEnd_2796717 < baseStart_2796717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796723 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 3]
def baseStart_2796723 : Nat := 118140960795 + 2796723 * 2 ^ 59
def prefixEnd_2796723 : Nat := 4983230072969 + 3 ^ 40 * 2796723 * 2
def baseEnd_2796723 : Nat := 1436063156484366542100611

theorem tailTrace_2796723 : CollatzResearch.WordTrace tailWord_2796723 prefixEnd_2796723 1436063156484366542100611 := by
  unfold tailWord_2796723
  simp only [CollatzResearch.WordTrace]
  refine ⟨102004867846957688106466823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68003245231305125404311215 102004867846957688106466823)
  ·
    refine ⟨153007301770436532159700235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102004867846957688106466823 153007301770436532159700235)
    ·
      refine ⟨229510952655654798239550353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153007301770436532159700235 229510952655654798239550353)
      ·
        refine ⟨172133214491741098679662765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229510952655654798239550353 172133214491741098679662765)
        ·
          refine ⟨64549955434402912004873537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172133214491741098679662765 64549955434402912004873537)
          ·
            refine ⟨48412466575802184003655153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64549955434402912004873537 48412466575802184003655153)
            ·
              refine ⟨36309349931851638002741365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48412466575802184003655153 36309349931851638002741365)
              ·
                refine ⟨3404001556111091062757003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36309349931851638002741365 3404001556111091062757003)
                ·
                  refine ⟨5106002334166636594135505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404001556111091062757003 5106002334166636594135505)
                  ·
                    refine ⟨3829501750624977445601629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5106002334166636594135505 3829501750624977445601629)
                    ·
                      refine ⟨1436063156484366542100611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3829501750624977445601629 1436063156484366542100611)
                      ·
                        rfl

theorem cell23_2796723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 3].length) (baseStart_2796723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796723 prefixEnd_2796723 := by exact prefixLift 2796723
  have htrace : WordTrace (prefixWord ++ tailWord_2796723) baseStart_2796723 baseEnd_2796723 := by
    simpa [prefixWord, tailWord_2796723, baseEnd_2796723] using wordTrace_append hprefix tailTrace_2796723
  have hstable : (prefixWord ++ tailWord_2796723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796723).length < 2 ^ (prefixWord ++ tailWord_2796723).sum := by decide
  have hdescent : baseEnd_2796723 < baseStart_2796723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796750 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_2796750 : Nat := 118140960795 + 2796750 * 2 ^ 59
def prefixEnd_2796750 : Nat := 4983230072969 + 3 ^ 40 * 2796750 * 2
def baseEnd_2796750 : Nat := 1436077020462037936462987

theorem tailTrace_2796750 : CollatzResearch.WordTrace tailWord_2796750 prefixEnd_2796750 1436077020462037936462987 := by
  unfold tailWord_2796750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12750731577232483964712463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68003901745239914478466469 12750731577232483964712463)
  ·
    refine ⟨19126097365848725947068695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12750731577232483964712463 19126097365848725947068695)
    ·
      refine ⟨28689146048773088920603043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19126097365848725947068695 28689146048773088920603043)
      ·
        refine ⟨43033719073159633380904565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28689146048773088920603043 43033719073159633380904565)
        ·
          refine ⟨4034411163108715629459803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43033719073159633380904565 4034411163108715629459803)
          ·
            refine ⟨6051616744663073444189705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034411163108715629459803 6051616744663073444189705)
            ·
              refine ⟨4538712558497305083142279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6051616744663073444189705 4538712558497305083142279)
              ·
                refine ⟨6808068837745957624713419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538712558497305083142279 6808068837745957624713419)
                ·
                  refine ⟨10212103256618936437070129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6808068837745957624713419 10212103256618936437070129)
                  ·
                    refine ⟨7659077442464202327802597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10212103256618936437070129 7659077442464202327802597)
                    ·
                      refine ⟨1436077020462037936462987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7659077442464202327802597 1436077020462037936462987)
                      ·
                        rfl

theorem cell23_2796750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_2796750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796750 prefixEnd_2796750 := by exact prefixLift 2796750
  have htrace : WordTrace (prefixWord ++ tailWord_2796750) baseStart_2796750 baseEnd_2796750 := by
    simpa [prefixWord, tailWord_2796750, baseEnd_2796750] using wordTrace_append hprefix tailTrace_2796750
  have hstable : (prefixWord ++ tailWord_2796750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796750).length < 2 ^ (prefixWord ++ tailWord_2796750).sum := by decide
  have hdescent : baseEnd_2796750 < baseStart_2796750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796753 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 3]
def baseStart_2796753 : Nat := 118140960795 + 2796753 * 2 ^ 59
def prefixEnd_2796753 : Nat := 4983230072969 + 3 ^ 40 * 2796753 * 2
def baseEnd_2796753 : Nat := 1436078560904001424725473

theorem tailTrace_2796753 : CollatzResearch.WordTrace tailWord_2796753 prefixEnd_2796753 1436078560904001424725473 := by
  unfold tailWord_2796753
  simp only [CollatzResearch.WordTrace]
  refine ⟨102005962036849003230058913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68003974691232668820039275 102005962036849003230058913)
  ·
    refine ⟨76504471527636752422544185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102005962036849003230058913 76504471527636752422544185)
    ·
      refine ⟨57378353645727564316908139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76504471527636752422544185 57378353645727564316908139)
      ·
        refine ⟨86067530468591346475362209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57378353645727564316908139 86067530468591346475362209)
        ·
          refine ⟨64550647851443509856521657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86067530468591346475362209 64550647851443509856521657)
          ·
            refine ⟨48412985888582632392391243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64550647851443509856521657 48412985888582632392391243)
            ·
              refine ⟨72619478832873948588586865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48412985888582632392391243 72619478832873948588586865)
              ·
                refine ⟨54464609124655461441440149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72619478832873948588586865 54464609124655461441440149)
                ·
                  refine ⟨2553028552718224755067507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54464609124655461441440149 2553028552718224755067507)
                  ·
                    refine ⟨3829542829077337132601261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2553028552718224755067507 3829542829077337132601261)
                    ·
                      refine ⟨1436078560904001424725473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3829542829077337132601261 1436078560904001424725473)
                      ·
                        rfl

theorem cell23_2796753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_2796753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796753 prefixEnd_2796753 := by exact prefixLift 2796753
  have htrace : WordTrace (prefixWord ++ tailWord_2796753) baseStart_2796753 baseEnd_2796753 := by
    simpa [prefixWord, tailWord_2796753, baseEnd_2796753] using wordTrace_append hprefix tailTrace_2796753
  have hstable : (prefixWord ++ tailWord_2796753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796753).length < 2 ^ (prefixWord ++ tailWord_2796753).sum := by decide
  have hdescent : baseEnd_2796753 < baseStart_2796753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796763 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 7, 3, 2]
def baseStart_2796763 : Nat := 118140960795 + 2796763 * 2 ^ 59
def prefixEnd_2796763 : Nat := 4983230072969 + 3 ^ 40 * 2796763 * 2
def baseEnd_2796763 : Nat := 1436083695710546385600427

theorem tailTrace_2796763 : CollatzResearch.WordTrace tailWord_2796763 prefixEnd_2796763 1436083695710546385600427 := by
  unfold tailWord_2796763
  simp only [CollatzResearch.WordTrace]
  refine ⟨102006326766812774937922943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68004217844541849958615295 102006326766812774937922943)
  ·
    refine ⟨153009490150219162406884415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102006326766812774937922943 153009490150219162406884415)
    ·
      refine ⟨229514235225328743610326623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153009490150219162406884415 229514235225328743610326623)
      ·
        refine ⟨344271352837993115415489935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229514235225328743610326623 344271352837993115415489935)
        ·
          refine ⟨516407029256989673123234903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344271352837993115415489935 516407029256989673123234903)
          ·
            refine ⟨774610543885484509684852355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516407029256989673123234903 774610543885484509684852355)
            ·
              refine ⟨1161915815828226764527278533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774610543885484509684852355 1161915815828226764527278533)
              ·
                refine ⟨217859215467792518348864725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1161915815828226764527278533 217859215467792518348864725)
                ·
                  refine ⟨5106075362526387148801517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 217859215467792518348864725 5106075362526387148801517)
                  ·
                    refine ⟨1914778260947395180800569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5106075362526387148801517 1914778260947395180800569)
                    ·
                      refine ⟨1436083695710546385600427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914778260947395180800569 1436083695710546385600427)
                      ·
                        rfl

theorem cell23_2796763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 3, 2].length) (baseStart_2796763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796763 prefixEnd_2796763 := by exact prefixLift 2796763
  have htrace : WordTrace (prefixWord ++ tailWord_2796763) baseStart_2796763 baseEnd_2796763 := by
    simpa [prefixWord, tailWord_2796763, baseEnd_2796763] using wordTrace_append hprefix tailTrace_2796763
  have hstable : (prefixWord ++ tailWord_2796763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796763).length < 2 ^ (prefixWord ++ tailWord_2796763).sum := by decide
  have hdescent : baseEnd_2796763 < baseStart_2796763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796787 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 3]
def baseStart_2796787 : Nat := 118140960795 + 2796787 * 2 ^ 59
def prefixEnd_2796787 : Nat := 4983230072969 + 3 ^ 40 * 2796787 * 2
def baseEnd_2796787 : Nat := 1436096019246254291700317

theorem tailTrace_2796787 : CollatzResearch.WordTrace tailWord_2796787 prefixEnd_2796787 1436096019246254291700317 := by
  unfold tailWord_2796787
  simp only [CollatzResearch.WordTrace]
  refine ⟨102007202118725827036796615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68004801412483884691197743 102007202118725827036796615)
  ·
    refine ⟨153010803178088740555194923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102007202118725827036796615 153010803178088740555194923)
    ·
      refine ⟨229516204767133110832792385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153010803178088740555194923 229516204767133110832792385)
      ·
        refine ⟨172137153575349833124594289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229516204767133110832792385 172137153575349833124594289)
        ·
          refine ⟨129102865181512374843445717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172137153575349833124594289 129102865181512374843445717)
          ·
            refine ⟨3025848402691696285393259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 129102865181512374843445717 3025848402691696285393259)
            ·
              refine ⟨4538772604037544428089889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025848402691696285393259 4538772604037544428089889)
              ·
                refine ⟨3404079453028158321067417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4538772604037544428089889 3404079453028158321067417)
                ·
                  refine ⟨2553059589771118740800563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404079453028158321067417 2553059589771118740800563)
                  ·
                    refine ⟨3829589384656678111200845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2553059589771118740800563 3829589384656678111200845)
                    ·
                      refine ⟨1436096019246254291700317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3829589384656678111200845 1436096019246254291700317)
                      ·
                        rfl

theorem cell23_2796787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 3].length) (baseStart_2796787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796787 prefixEnd_2796787 := by exact prefixLift 2796787
  have htrace : WordTrace (prefixWord ++ tailWord_2796787) baseStart_2796787 baseEnd_2796787 := by
    simpa [prefixWord, tailWord_2796787, baseEnd_2796787] using wordTrace_append hprefix tailTrace_2796787
  have hstable : (prefixWord ++ tailWord_2796787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796787).length < 2 ^ (prefixWord ++ tailWord_2796787).sum := by decide
  have hdescent : baseEnd_2796787 < baseStart_2796787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796788 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2796788 : Nat := 118140960795 + 2796788 * 2 ^ 59
def prefixEnd_2796788 : Nat := 4983230072969 + 3 ^ 40 * 2796788 * 2
def baseEnd_2796788 : Nat := 1436096532726908787787813

theorem tailTrace_2796788 : CollatzResearch.WordTrace tailWord_2796788 prefixEnd_2796788 1436096532726908787787813 := by
  unfold tailWord_2796788
  simp only [CollatzResearch.WordTrace]
  refine ⟨51003619295861102103791509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68004825727814802805055345 51003619295861102103791509)
  ·
    refine ⟨2390794654493489161115227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51003619295861102103791509 2390794654493489161115227)
    ·
      refine ⟨3586191981740233741672841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2390794654493489161115227 3586191981740233741672841)
      ·
        refine ⟨2689643986305175306254631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3586191981740233741672841 2689643986305175306254631)
        ·
          refine ⟨4034465979457762959381947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689643986305175306254631 4034465979457762959381947)
          ·
            refine ⟨6051698969186644439072921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034465979457762959381947 6051698969186644439072921)
            ·
              refine ⟨4538774226889983329304691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6051698969186644439072921 4538774226889983329304691)
              ·
                refine ⟨6808161340334974993957037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538774226889983329304691 6808161340334974993957037)
                ·
                  refine ⟨2553060502625615622733889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6808161340334974993957037 2553060502625615622733889)
                  ·
                    refine ⟨1914795376969211717050417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2553060502625615622733889 1914795376969211717050417)
                    ·
                      refine ⟨1436096532726908787787813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914795376969211717050417 1436096532726908787787813)
                      ·
                        rfl

theorem cell23_2796788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2796788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796788 prefixEnd_2796788 := by exact prefixLift 2796788
  have htrace : WordTrace (prefixWord ++ tailWord_2796788) baseStart_2796788 baseEnd_2796788 := by
    simpa [prefixWord, tailWord_2796788, baseEnd_2796788] using wordTrace_append hprefix tailTrace_2796788
  have hstable : (prefixWord ++ tailWord_2796788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796788).length < 2 ^ (prefixWord ++ tailWord_2796788).sum := by decide
  have hdescent : baseEnd_2796788 < baseStart_2796788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796804 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_2796804 : Nat := 118140960795 + 2796804 * 2 ^ 59
def prefixEnd_2796804 : Nat := 4983230072969 + 3 ^ 40 * 2796804 * 2
def baseEnd_2796804 : Nat := 1436104748417380725187739

theorem tailTrace_2796804 : CollatzResearch.WordTrace tailWord_2796804 prefixEnd_2796804 1436104748417380725187739 := by
  unfold tailWord_2796804
  simp only [CollatzResearch.WordTrace]
  refine ⟨51003911079832119470082733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68005214773109492626776977 51003911079832119470082733)
  ·
    refine ⟨19126466654937044801281025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51003911079832119470082733 19126466654937044801281025)
    ·
      refine ⟨14344849991202783600960769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19126466654937044801281025 14344849991202783600960769)
      ·
        refine ⟨10758637493402087700720577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14344849991202783600960769 10758637493402087700720577)
        ·
          refine ⟨8068978120051565775540433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10758637493402087700720577 8068978120051565775540433)
          ·
            refine ⟨6051733590038674331655325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8068978120051565775540433 6051733590038674331655325)
            ·
              refine ⟨2269400096264502874370747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6051733590038674331655325 2269400096264502874370747)
              ·
                refine ⟨3404100144396754311556121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269400096264502874370747 3404100144396754311556121)
                ·
                  refine ⟨2553075108297565733667091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404100144396754311556121 2553075108297565733667091)
                  ·
                    refine ⟨3829612662446348600500637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2553075108297565733667091 3829612662446348600500637)
                    ·
                      refine ⟨1436104748417380725187739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3829612662446348600500637 1436104748417380725187739)
                      ·
                        rfl

theorem cell23_2796804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_2796804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796804 prefixEnd_2796804 := by exact prefixLift 2796804
  have htrace : WordTrace (prefixWord ++ tailWord_2796804) baseStart_2796804 baseEnd_2796804 := by
    simpa [prefixWord, tailWord_2796804, baseEnd_2796804] using wordTrace_append hprefix tailTrace_2796804
  have hstable : (prefixWord ++ tailWord_2796804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796804).length < 2 ^ (prefixWord ++ tailWord_2796804).sum := by decide
  have hdescent : baseEnd_2796804 < baseStart_2796804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796850 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 7]
def baseStart_2796850 : Nat := 118140960795 + 2796850 * 2 ^ 59
def prefixEnd_2796850 : Nat := 4983230072969 + 3 ^ 40 * 2796850 * 2
def baseEnd_2796850 : Nat := 159569818725276393912503

theorem tailTrace_2796850 : CollatzResearch.WordTrace tailWord_2796850 prefixEnd_2796850 159569818725276393912503 := by
  unfold tailWord_2796850
  simp only [CollatzResearch.WordTrace]
  refine ⟨25502374979374397199085001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68006333278331725864226669 25502374979374397199085001)
  ·
    refine ⟨19126781234530797899313751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25502374979374397199085001 19126781234530797899313751)
    ·
      refine ⟨28690171851796196848970627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19126781234530797899313751 28690171851796196848970627)
      ·
        refine ⟨43035257777694295273455941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28690171851796196848970627 43035257777694295273455941)
        ·
          refine ⟨8069110833317680363772989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43035257777694295273455941 8069110833317680363772989)
          ·
            refine ⟨3025916562494130136414871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8069110833317680363772989 3025916562494130136414871)
            ·
              refine ⟨4538874843741195204622307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025916562494130136414871 4538874843741195204622307)
              ·
                refine ⟨6808312265611792806933461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538874843741195204622307 6808312265611792806933461)
                ·
                  refine ⟨159569818725276393912503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6808312265611792806933461 159569818725276393912503)
                  ·
                    rfl

theorem cell23_2796850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_2796850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796850 prefixEnd_2796850 := by exact prefixLift 2796850
  have htrace : WordTrace (prefixWord ++ tailWord_2796850) baseStart_2796850 baseEnd_2796850 := by
    simpa [prefixWord, tailWord_2796850, baseEnd_2796850] using wordTrace_append hprefix tailTrace_2796850
  have hstable : (prefixWord ++ tailWord_2796850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796850).length < 2 ^ (prefixWord ++ tailWord_2796850).sum := by decide
  have hdescent : baseEnd_2796850 < baseStart_2796850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796861 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2796861 : Nat := 118140960795 + 2796861 * 2 ^ 59
def prefixEnd_2796861 : Nat := 4983230072969 + 3 ^ 40 * 2796861 * 2
def baseEnd_2796861 : Nat := 1436134016814687002174977

theorem tailTrace_2796861 : CollatzResearch.WordTrace tailWord_2796861 prefixEnd_2796861 1436134016814687002174977 := by
  unfold tailWord_2796861
  simp only [CollatzResearch.WordTrace]
  refine ⟨102009901120457737674990437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68006600746971825116660291 102009901120457737674990437)
  ·
    refine ⟨19126856460085825814060707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102009901120457737674990437 19126856460085825814060707)
    ·
      refine ⟨28690284690128738721091061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19126856460085825814060707 28690284690128738721091061)
      ·
        refine ⟨2689714189699569255102287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28690284690128738721091061 2689714189699569255102287)
        ·
          refine ⟨4034571284549353882653431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689714189699569255102287 4034571284549353882653431)
          ·
            refine ⟨6051856926824030823980147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034571284549353882653431 6051856926824030823980147)
            ·
              refine ⟨9077785390236046235970221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051856926824030823980147 9077785390236046235970221)
              ·
                refine ⟨3404169521338517338488833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9077785390236046235970221 3404169521338517338488833)
                ·
                  refine ⟨2553127141003888003866625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404169521338517338488833 2553127141003888003866625)
                  ·
                    refine ⟨1914845355752916002899969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2553127141003888003866625 1914845355752916002899969)
                    ·
                      refine ⟨1436134016814687002174977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914845355752916002899969 1436134016814687002174977)
                      ·
                        rfl

theorem cell23_2796861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2796861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796861 prefixEnd_2796861 := by exact prefixLift 2796861
  have htrace : WordTrace (prefixWord ++ tailWord_2796861) baseStart_2796861 baseEnd_2796861 := by
    simpa [prefixWord, tailWord_2796861, baseEnd_2796861] using wordTrace_append hprefix tailTrace_2796861
  have hstable : (prefixWord ++ tailWord_2796861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796861).length < 2 ^ (prefixWord ++ tailWord_2796861).sum := by decide
  have hdescent : baseEnd_2796861 < baseStart_2796861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796900 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_2796900 : Nat := 118140960795 + 2796900 * 2 ^ 59
def prefixEnd_2796900 : Nat := 4983230072969 + 3 ^ 40 * 2796900 * 2
def baseEnd_2796900 : Nat := 1436154042560212349587297

theorem tailTrace_2796900 : CollatzResearch.WordTrace tailWord_2796900 prefixEnd_2796900 1436154042560212349587297 := by
  unfold tailWord_2796900
  simp only [CollatzResearch.WordTrace]
  refine ⟨51005661783658223667830077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68007549044877631557106769 51005661783658223667830077)
  ·
    refine ⟨19127123168871833875436279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51005661783658223667830077 19127123168871833875436279)
    ·
      refine ⟨28690684753307750813154419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19127123168871833875436279 28690684753307750813154419)
      ·
        refine ⟨43036027129961626219731629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28690684753307750813154419 43036027129961626219731629)
        ·
          refine ⟨16138510173735609832399361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43036027129961626219731629 16138510173735609832399361)
          ·
            refine ⟨12103882630301707374299521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16138510173735609832399361 12103882630301707374299521)
            ·
              refine ⟨9077911972726280530724641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12103882630301707374299521 9077911972726280530724641)
              ·
                refine ⟨6808433979544710398043481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9077911972726280530724641 6808433979544710398043481)
                ·
                  refine ⟨5106325484658532798532611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6808433979544710398043481 5106325484658532798532611)
                  ·
                    refine ⟨7659488226987799197798917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5106325484658532798532611 7659488226987799197798917)
                    ·
                      refine ⟨1436154042560212349587297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7659488226987799197798917 1436154042560212349587297)
                      ·
                        rfl

theorem cell23_2796900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_2796900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796900 prefixEnd_2796900 := by exact prefixLift 2796900
  have htrace : WordTrace (prefixWord ++ tailWord_2796900) baseStart_2796900 baseEnd_2796900 := by
    simpa [prefixWord, tailWord_2796900, baseEnd_2796900] using wordTrace_append hprefix tailTrace_2796900
  have hstable : (prefixWord ++ tailWord_2796900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796900).length < 2 ^ (prefixWord ++ tailWord_2796900).sum := by decide
  have hdescent : baseEnd_2796900 < baseStart_2796900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796923 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 6]
def baseStart_2796923 : Nat := 118140960795 + 2796923 * 2 ^ 59
def prefixEnd_2796923 : Nat := 4983230072969 + 3 ^ 40 * 2796923 * 2
def baseEnd_2796923 : Nat := 159573983623918417733299

theorem tailTrace_2796923 : CollatzResearch.WordTrace tailWord_2796923 prefixEnd_2796923 159573983623918417733299 := by
  unfold tailWord_2796923
  simp only [CollatzResearch.WordTrace]
  refine ⟨102012162446233122263747423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68008108297488748175831615 102012162446233122263747423)
  ·
    refine ⟨153018243669349683395621135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102012162446233122263747423 153018243669349683395621135)
    ·
      refine ⟨229527365504024525093431703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153018243669349683395621135 229527365504024525093431703)
      ·
        refine ⟨344291048256036787640147555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229527365504024525093431703 344291048256036787640147555)
        ·
          refine ⟨516436572384055181460221333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344291048256036787640147555 516436572384055181460221333)
          ·
            refine ⟨24207964330502586630947875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 516436572384055181460221333 24207964330502586630947875)
            ·
              refine ⟨36311946495753879946421813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24207964330502586630947875 36311946495753879946421813)
              ·
                refine ⟨3404244983976926244977045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36311946495753879946421813 3404244983976926244977045)
                ·
                  refine ⟨159573983623918417733299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3404244983976926244977045 159573983623918417733299)
                  ·
                    rfl

theorem cell23_2796923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 6].length) (baseStart_2796923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796923 prefixEnd_2796923 := by exact prefixLift 2796923
  have htrace : WordTrace (prefixWord ++ tailWord_2796923) baseStart_2796923 baseEnd_2796923 := by
    simpa [prefixWord, tailWord_2796923, baseEnd_2796923] using wordTrace_append hprefix tailTrace_2796923
  have hstable : (prefixWord ++ tailWord_2796923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796923).length < 2 ^ (prefixWord ++ tailWord_2796923).sum := by decide
  have hdescent : baseEnd_2796923 < baseStart_2796923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796957 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 6]
def baseStart_2796957 : Nat := 118140960795 + 2796957 * 2 ^ 59
def prefixEnd_2796957 : Nat := 4983230072969 + 3 ^ 40 * 2796957 * 2
def baseEnd_2796957 : Nat := 159575923439724291841615

theorem tailTrace_2796957 : CollatzResearch.WordTrace tailWord_2796957 prefixEnd_2796957 159575923439724291841615 := by
  unfold tailWord_2796957
  simp only [CollatzResearch.WordTrace]
  refine ⟨102013402528109946070485125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68008935018739964046990083 102013402528109946070485125)
  ·
    refine ⟨19127512974020614888215961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102013402528109946070485125 19127512974020614888215961)
    ·
      refine ⟨14345634730515461166161971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19127512974020614888215961 14345634730515461166161971)
      ·
        refine ⟨21518452095773191749242957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14345634730515461166161971 21518452095773191749242957)
        ·
          refine ⟨8069419535914946905966109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21518452095773191749242957 8069419535914946905966109)
          ·
            refine ⟨3026032325968105089737291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8069419535914946905966109 3026032325968105089737291)
            ·
              refine ⟨4539048488952157634605937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3026032325968105089737291 4539048488952157634605937)
              ·
                refine ⟨3404286366714118225954453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4539048488952157634605937 3404286366714118225954453)
                ·
                  refine ⟨159575923439724291841615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3404286366714118225954453 159575923439724291841615)
                  ·
                    rfl

theorem cell23_2796957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_2796957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2796957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2796957 prefixEnd_2796957 := by exact prefixLift 2796957
  have htrace : WordTrace (prefixWord ++ tailWord_2796957) baseStart_2796957 baseEnd_2796957 := by
    simpa [prefixWord, tailWord_2796957, baseEnd_2796957] using wordTrace_append hprefix tailTrace_2796957
  have hstable : (prefixWord ++ tailWord_2796957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796957).length < 2 ^ (prefixWord ++ tailWord_2796957).sum := by decide
  have hdescent : baseEnd_2796957 < baseStart_2796957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797000 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 6, 4]
def baseStart_2797000 : Nat := 118140960795 + 2797000 * 2 ^ 59
def prefixEnd_2797000 : Nat := 4983230072969 + 3 ^ 40 * 2797000 * 2
def baseEnd_2797000 : Nat := 478735130208553986112279

theorem tailTrace_2797000 : CollatzResearch.WordTrace tailWord_2797000 prefixEnd_2797000 478735130208553986112279 := by
  unfold tailWord_2797000
  simp only [CollatzResearch.WordTrace]
  refine ⟨51007485433477082207150227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68009980577969442942866969 51007485433477082207150227)
  ·
    refine ⟨76511228150215623310725341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51007485433477082207150227 76511228150215623310725341)
    ·
      refine ⟨28691710556330858741522003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76511228150215623310725341 28691710556330858741522003)
      ·
        refine ⟨43037565834496288112283005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28691710556330858741522003 43037565834496288112283005)
        ·
          refine ⟨16139087187936108042106127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43037565834496288112283005 16139087187936108042106127)
          ·
            refine ⟨24208630781904162063159191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16139087187936108042106127 24208630781904162063159191)
            ·
              refine ⟨36312946172856243094738787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24208630781904162063159191 36312946172856243094738787)
              ·
                refine ⟨54469419259284364642108181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36312946172856243094738787 54469419259284364642108181)
                ·
                  refine ⟨2553254027778954592598821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54469419259284364642108181 2553254027778954592598821)
                  ·
                    refine ⟨478735130208553986112279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2553254027778954592598821 478735130208553986112279)
                    ·
                      rfl

theorem cell23_2797000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_2797000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797000 prefixEnd_2797000 := by exact prefixLift 2797000
  have htrace : WordTrace (prefixWord ++ tailWord_2797000) baseStart_2797000 baseEnd_2797000 := by
    simpa [prefixWord, tailWord_2797000, baseEnd_2797000] using wordTrace_append hprefix tailTrace_2797000
  have hstable : (prefixWord ++ tailWord_2797000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797000).length < 2 ^ (prefixWord ++ tailWord_2797000).sum := by decide
  have hdescent : baseEnd_2797000 < baseStart_2797000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797007 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 5, 2, 2]
def baseStart_2797007 : Nat := 118140960795 + 2797007 * 2 ^ 59
def prefixEnd_2797007 : Nat := 4983230072969 + 3 ^ 40 * 2797007 * 2
def baseEnd_2797007 : Nat := 1436208984990243430949305

theorem tailTrace_2797007 : CollatzResearch.WordTrace tailWord_2797007 prefixEnd_2797007 1436208984990243430949305 := by
  unfold tailWord_2797007
  simp only [CollatzResearch.WordTrace]
  refine ⟨102015226177928804609805275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68010150785285869739870183 102015226177928804609805275)
  ·
    refine ⟨153022839266893206914707913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102015226177928804609805275 153022839266893206914707913)
    ·
      refine ⟨114767129450169905186030935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153022839266893206914707913 114767129450169905186030935)
      ·
        refine ⟨172150694175254857779046403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114767129450169905186030935 172150694175254857779046403)
        ·
          refine ⟨258226041262882286668569605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172150694175254857779046403 258226041262882286668569605)
          ·
            refine ⟨48417382736790428750356801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258226041262882286668569605 48417382736790428750356801)
            ·
              refine ⟨36313037052592821562767601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48417382736790428750356801 36313037052592821562767601)
              ·
                refine ⟨27234777789444616172075701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36313037052592821562767601 27234777789444616172075701)
                ·
                  refine ⟨2553260417760432766132097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27234777789444616172075701 2553260417760432766132097)
                  ·
                    refine ⟨1914945313320324574599073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2553260417760432766132097 1914945313320324574599073)
                    ·
                      refine ⟨1436208984990243430949305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1914945313320324574599073 1436208984990243430949305)
                      ·
                        rfl

theorem cell23_2797007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 2, 2].length) (baseStart_2797007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797007 prefixEnd_2797007 := by exact prefixLift 2797007
  have htrace : WordTrace (prefixWord ++ tailWord_2797007) baseStart_2797007 baseEnd_2797007 := by
    simpa [prefixWord, tailWord_2797007, baseEnd_2797007] using wordTrace_append hprefix tailTrace_2797007
  have hstable : (prefixWord ++ tailWord_2797007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797007).length < 2 ^ (prefixWord ++ tailWord_2797007).sum := by decide
  have hdescent : baseEnd_2797007 < baseStart_2797007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797034 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_2797034 : Nat := 118140960795 + 2797034 * 2 ^ 59
def prefixEnd_2797034 : Nat := 4983230072969 + 3 ^ 40 * 2797034 * 2
def baseEnd_2797034 : Nat := 478740949655971608437227

theorem tailTrace_2797034 : CollatzResearch.WordTrace tailWord_2797034 prefixEnd_2797034 478740949655971608437227 := by
  unfold tailWord_2797034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25504052737207747055259539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68010807299220658814025437 25504052737207747055259539)
  ·
    refine ⟨38256079105811620582889309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25504052737207747055259539 38256079105811620582889309)
    ·
      refine ⟨14346029664679357718583491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38256079105811620582889309 14346029664679357718583491)
      ·
        refine ⟨21519044497019036577875237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14346029664679357718583491 21519044497019036577875237)
        ·
          refine ⟨4034820843191069358351607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21519044497019036577875237 4034820843191069358351607)
          ·
            refine ⟨6052231264786604037527411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034820843191069358351607 6052231264786604037527411)
            ·
              refine ⟨9078346897179906056291117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6052231264786604037527411 9078346897179906056291117)
              ·
                refine ⟨3404380086442464771109169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9078346897179906056291117 3404380086442464771109169)
                ·
                  refine ⟨2553285064831848578331877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404380086442464771109169 2553285064831848578331877)
                  ·
                    refine ⟨478740949655971608437227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2553285064831848578331877 478740949655971608437227)
                    ·
                      rfl

theorem cell23_2797034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_2797034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797034 prefixEnd_2797034 := by exact prefixLift 2797034
  have htrace : WordTrace (prefixWord ++ tailWord_2797034) baseStart_2797034 baseEnd_2797034 := by
    simpa [prefixWord, tailWord_2797034, baseEnd_2797034] using wordTrace_append hprefix tailTrace_2797034
  have hstable : (prefixWord ++ tailWord_2797034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797034).length < 2 ^ (prefixWord ++ tailWord_2797034).sum := by decide
  have hdescent : baseEnd_2797034 < baseStart_2797034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797043 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 4, 7]
def baseStart_2797043 : Nat := 118140960795 + 2797043 * 2 ^ 59
def prefixEnd_2797043 : Nat := 4983230072969 + 3 ^ 40 * 2797043 * 2
def baseEnd_2797043 : Nat := 478742490097935096699713

theorem tailTrace_2797043 : CollatzResearch.WordTrace tailWord_2797043 prefixEnd_2797043 478742490097935096699713 := by
  unfold tailWord_2797043
  simp only [CollatzResearch.WordTrace]
  refine ⟨102016539205798382758115783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68011026137198921838743855 102016539205798382758115783)
  ·
    refine ⟨153024808808697574137173675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102016539205798382758115783 153024808808697574137173675)
    ·
      refine ⟨229537213213046361205760513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153024808808697574137173675 229537213213046361205760513)
      ·
        refine ⟨172152909909784770904320385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229537213213046361205760513 172152909909784770904320385)
        ·
          refine ⟨129114682432338578178240289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172152909909784770904320385 129114682432338578178240289)
          ·
            refine ⟨96836011824253933633680217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129114682432338578178240289 96836011824253933633680217)
            ·
              refine ⟨72627008868190450225260163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96836011824253933633680217 72627008868190450225260163)
              ·
                refine ⟨108940513302285675337890245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72627008868190450225260163 108940513302285675337890245)
                ·
                  refine ⟨20426346244178564125854421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108940513302285675337890245 20426346244178564125854421)
                  ·
                    refine ⟨478742490097935096699713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20426346244178564125854421 478742490097935096699713)
                    ·
                      rfl

theorem cell23_2797043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 7].length) (baseStart_2797043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797043 prefixEnd_2797043 := by exact prefixLift 2797043
  have htrace : WordTrace (prefixWord ++ tailWord_2797043) baseStart_2797043 baseEnd_2797043 := by
    simpa [prefixWord, tailWord_2797043, baseEnd_2797043] using wordTrace_append hprefix tailTrace_2797043
  have hstable : (prefixWord ++ tailWord_2797043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797043).length < 2 ^ (prefixWord ++ tailWord_2797043).sum := by decide
  have hdescent : baseEnd_2797043 < baseStart_2797043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797069 : List Nat := [1, 7, 1, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2797069 : Nat := 118140960795 + 2797069 * 2 ^ 59
def prefixEnd_2797069 : Nat := 4983230072969 + 3 ^ 40 * 2797069 * 2
def baseEnd_2797069 : Nat := 1436240820790822188374021

theorem tailTrace_2797069 : CollatzResearch.WordTrace tailWord_2797069 prefixEnd_2797069 1436240820790822188374021 := by
  unfold tailWord_2797069
  simp only [CollatzResearch.WordTrace]
  refine ⟨102017487503704189198562261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68011658335802792799041507 102017487503704189198562261)
  ·
    refine ⟨2391034863368066934341303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 102017487503704189198562261 2391034863368066934341303)
    ·
      refine ⟨3586552295052100401511955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2391034863368066934341303 3586552295052100401511955)
      ·
        refine ⟨5379828442578150602267933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3586552295052100401511955 5379828442578150602267933)
        ·
          refine ⟨2017435665966806475850475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5379828442578150602267933 2017435665966806475850475)
          ·
            refine ⟨3026153498950209713775713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017435665966806475850475 3026153498950209713775713)
            ·
              refine ⟨2269615124212657285331785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026153498950209713775713 2269615124212657285331785)
              ·
                refine ⟨1702211343159492963998839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269615124212657285331785 1702211343159492963998839)
                ·
                  refine ⟨2553317014739239445998259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702211343159492963998839 2553317014739239445998259)
                  ·
                    refine ⟨3829975522108859168997389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2553317014739239445998259 3829975522108859168997389)
                    ·
                      refine ⟨1436240820790822188374021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3829975522108859168997389 1436240820790822188374021)
                      ·
                        rfl

theorem cell23_2797069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2797069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797069 prefixEnd_2797069 := by exact prefixLift 2797069
  have htrace : WordTrace (prefixWord ++ tailWord_2797069) baseStart_2797069 baseEnd_2797069 := by
    simpa [prefixWord, tailWord_2797069, baseEnd_2797069] using wordTrace_append hprefix tailTrace_2797069
  have hstable : (prefixWord ++ tailWord_2797069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797069).length < 2 ^ (prefixWord ++ tailWord_2797069).sum := by decide
  have hdescent : baseEnd_2797069 < baseStart_2797069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797090 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2797090 : Nat := 118140960795 + 2797090 * 2 ^ 59
def prefixEnd_2797090 : Nat := 4983230072969 + 3 ^ 40 * 2797090 * 2
def baseEnd_2797090 : Nat := 478750534628188868737141

theorem tailTrace_2797090 : CollatzResearch.WordTrace tailWord_2797090 prefixEnd_2797090 478750534628188868737141 := by
  unfold tailWord_2797090
  simp only [CollatzResearch.WordTrace]
  refine ⟨25504563359157027446269181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68012168957752073190051149 25504563359157027446269181)
  ·
    refine ⟨9564211259683885292350943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25504563359157027446269181 9564211259683885292350943)
    ·
      refine ⟨14346316889525827938526415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9564211259683885292350943 14346316889525827938526415)
      ·
        refine ⟨21519475334288741907789623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14346316889525827938526415 21519475334288741907789623)
        ·
          refine ⟨32279213001433112861684435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21519475334288741907789623 32279213001433112861684435)
          ·
            refine ⟨48418819502149669292526653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32279213001433112861684435 48418819502149669292526653)
            ·
              refine ⟨18157057313306125984697495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48418819502149669292526653 18157057313306125984697495)
              ·
                refine ⟨27235585969959188977046243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18157057313306125984697495 27235585969959188977046243)
                ·
                  refine ⟨40853378954938783465569365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27235585969959188977046243 40853378954938783465569365)
                  ·
                    refine ⟨478750534628188868737141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40853378954938783465569365 478750534628188868737141)
                    ·
                      rfl

theorem cell23_2797090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2797090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797090 prefixEnd_2797090 := by exact prefixLift 2797090
  have htrace : WordTrace (prefixWord ++ tailWord_2797090) baseStart_2797090 baseEnd_2797090 := by
    simpa [prefixWord, tailWord_2797090, baseEnd_2797090] using wordTrace_append hprefix tailTrace_2797090
  have hstable : (prefixWord ++ tailWord_2797090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797090).length < 2 ^ (prefixWord ++ tailWord_2797090).sum := by decide
  have hdescent : baseEnd_2797090 < baseStart_2797090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797114 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2]
def baseStart_2797114 : Nat := 118140960795 + 2797114 * 2 ^ 59
def prefixEnd_2797114 : Nat := 4983230072969 + 3 ^ 40 * 2797114 * 2
def baseEnd_2797114 : Nat := 1436263927420274512311313

theorem tailTrace_2797114 : CollatzResearch.WordTrace tailWord_2797114 prefixEnd_2797114 1436263927420274512311313 := by
  unfold tailWord_2797114
  simp only [CollatzResearch.WordTrace]
  refine ⟨25504782197135290470987599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68012752525694107922633597 25504782197135290470987599)
  ·
    refine ⟨38257173295702935706481399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25504782197135290470987599 38257173295702935706481399)
    ·
      refine ⟨57385759943554403559722099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38257173295702935706481399 57385759943554403559722099)
      ·
        refine ⟨86078639915331605339583149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57385759943554403559722099 86078639915331605339583149)
        ·
          refine ⟨32279489968249352002343681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86078639915331605339583149 32279489968249352002343681)
          ·
            refine ⟨24209617476187014001757761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32279489968249352002343681 24209617476187014001757761)
            ·
              refine ⟨18157213107140260501318321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24209617476187014001757761 18157213107140260501318321)
              ·
                refine ⟨13617909830355195375988741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18157213107140260501318321 13617909830355195375988741)
                ·
                  refine ⟨2553358093191599132997889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13617909830355195375988741 2553358093191599132997889)
                  ·
                    refine ⟨1915018569893699349748417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2553358093191599132997889 1915018569893699349748417)
                    ·
                      refine ⟨1436263927420274512311313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915018569893699349748417 1436263927420274512311313)
                      ·
                        rfl

theorem cell23_2797114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_2797114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797114 prefixEnd_2797114 := by exact prefixLift 2797114
  have htrace : WordTrace (prefixWord ++ tailWord_2797114) baseStart_2797114 baseEnd_2797114 := by
    simpa [prefixWord, tailWord_2797114, baseEnd_2797114] using wordTrace_append hprefix tailTrace_2797114
  have hstable : (prefixWord ++ tailWord_2797114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797114).length < 2 ^ (prefixWord ++ tailWord_2797114).sum := by decide
  have hdescent : baseEnd_2797114 < baseStart_2797114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797137 : List Nat := [1, 2, 2, 1, 3, 2, 1, 6, 5]
def baseStart_2797137 : Nat := 118140960795 + 2797137 * 2 ^ 59
def prefixEnd_2797137 : Nat := 4983230072969 + 3 ^ 40 * 2797137 * 2
def baseEnd_2797137 : Nat := 159586193052814213591523

theorem tailTrace_2797137 : CollatzResearch.WordTrace tailWord_2797137 prefixEnd_2797137 159586193052814213591523 := by
  unfold tailWord_2797137
  simp only [CollatzResearch.WordTrace]
  refine ⟨102019967667457836812037665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68013311778305224541358443 102019967667457836812037665)
  ·
    refine ⟨76514975750593377609028249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102019967667457836812037665 76514975750593377609028249)
    ·
      refine ⟨57386231812945033206771187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76514975750593377609028249 57386231812945033206771187)
      ·
        refine ⟨86079347719417549810156781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57386231812945033206771187 86079347719417549810156781)
        ·
          refine ⟨32279755394781581178808793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86079347719417549810156781 32279755394781581178808793)
          ·
            refine ⟨24209816546086185884106595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32279755394781581178808793 24209816546086185884106595)
            ·
              refine ⟨36314724819129278826159893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24209816546086185884106595 36314724819129278826159893)
              ·
                refine ⟨1702252725896684944976245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36314724819129278826159893 1702252725896684944976245)
                ·
                  refine ⟨159586193052814213591523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1702252725896684944976245 159586193052814213591523)
                  ·
                    rfl

theorem cell23_2797137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 5].length) (baseStart_2797137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797137 prefixEnd_2797137 := by exact prefixLift 2797137
  have htrace : WordTrace (prefixWord ++ tailWord_2797137) baseStart_2797137 baseEnd_2797137 := by
    simpa [prefixWord, tailWord_2797137, baseEnd_2797137] using wordTrace_append hprefix tailTrace_2797137
  have hstable : (prefixWord ++ tailWord_2797137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797137).length < 2 ^ (prefixWord ++ tailWord_2797137).sum := by decide
  have hdescent : baseEnd_2797137 < baseStart_2797137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797142 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2797142 : Nat := 118140960795 + 2797142 * 2 ^ 59
def prefixEnd_2797142 : Nat := 4983230072969 + 3 ^ 40 * 2797142 * 2
def baseEnd_2797142 : Nat := 1436278304878600402761185

theorem tailTrace_2797142 : CollatzResearch.WordTrace tailWord_2797142 prefixEnd_2797142 1436278304878600402761185 := by
  unfold tailWord_2797142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376259377027482666623105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68013433354959815110646453 6376259377027482666623105)
  ·
    refine ⟨4782194532770611999967329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6376259377027482666623105 4782194532770611999967329)
    ·
      refine ⟨3586645899577958999975497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4782194532770611999967329 3586645899577958999975497)
      ·
        refine ⟨2689984424683469249981623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3586645899577958999975497 2689984424683469249981623)
        ·
          refine ⟨4034976637025203874972435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689984424683469249981623 4034976637025203874972435)
          ·
            refine ⟨6052464955537805812458653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034976637025203874972435 6052464955537805812458653)
            ·
              refine ⟨2269674358326677179671995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6052464955537805812458653 2269674358326677179671995)
              ·
                refine ⟨3404511537490015769507993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269674358326677179671995 3404511537490015769507993)
                ·
                  refine ⟨2553383653117511827130995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404511537490015769507993 2553383653117511827130995)
                  ·
                    refine ⟨3830075479676267740696493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2553383653117511827130995 3830075479676267740696493)
                    ·
                      refine ⟨1436278304878600402761185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3830075479676267740696493 1436278304878600402761185)
                      ·
                        rfl

theorem cell23_2797142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2797142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797142 prefixEnd_2797142 := by exact prefixLift 2797142
  have htrace : WordTrace (prefixWord ++ tailWord_2797142) baseStart_2797142 baseEnd_2797142 := by
    simpa [prefixWord, tailWord_2797142, baseEnd_2797142] using wordTrace_append hprefix tailTrace_2797142
  have hstable : (prefixWord ++ tailWord_2797142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797142).length < 2 ^ (prefixWord ++ tailWord_2797142).sum := by decide
  have hdescent : baseEnd_2797142 < baseStart_2797142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797200 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_2797200 : Nat := 118140960795 + 2797200 * 2 ^ 59
def prefixEnd_2797200 : Nat := 4983230072969 + 3 ^ 40 * 2797200 * 2
def baseEnd_2797200 : Nat := 1436308086756561175835917

theorem tailTrace_2797200 : CollatzResearch.WordTrace tailWord_2797200 prefixEnd_2797200 1436308086756561175835917 := by
  unfold tailWord_2797200
  simp only [CollatzResearch.WordTrace]
  refine ⟨51011132733114799285790527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68014843644153065714387369 51011132733114799285790527)
  ·
    refine ⟨76516699099672198928685791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51011132733114799285790527 76516699099672198928685791)
    ·
      refine ⟨114775048649508298393028687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76516699099672198928685791 114775048649508298393028687)
      ·
        refine ⟨172162572974262447589543031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114775048649508298393028687 172162572974262447589543031)
        ·
          refine ⟨258243859461393671384314547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172162572974262447589543031 258243859461393671384314547)
          ·
            refine ⟨387365789192090507076471821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258243859461393671384314547 387365789192090507076471821)
            ·
              refine ⟨145262170947033940153676933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 387365789192090507076471821 145262170947033940153676933)
              ·
                refine ⟨27236657052568863778814425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145262170947033940153676933 27236657052568863778814425)
                ·
                  refine ⟨20427492789426647834110819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27236657052568863778814425 20427492789426647834110819)
                  ·
                    refine ⟨30641239184139971751166229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20427492789426647834110819 30641239184139971751166229)
                    ·
                      refine ⟨1436308086756561175835917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30641239184139971751166229 1436308086756561175835917)
                      ·
                        rfl

theorem cell23_2797200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_2797200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797200 prefixEnd_2797200 := by exact prefixLift 2797200
  have htrace : WordTrace (prefixWord ++ tailWord_2797200) baseStart_2797200 baseEnd_2797200 := by
    simpa [prefixWord, tailWord_2797200, baseEnd_2797200] using wordTrace_append hprefix tailTrace_2797200
  have hstable : (prefixWord ++ tailWord_2797200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797200).length < 2 ^ (prefixWord ++ tailWord_2797200).sum := by decide
  have hdescent : baseEnd_2797200 < baseStart_2797200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797244 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 6]
def baseStart_2797244 : Nat := 118140960795 + 2797244 * 2 ^ 59
def prefixEnd_2797244 : Nat := 4983230072969 + 3 ^ 40 * 2797244 * 2
def baseEnd_2797244 : Nat := 159592297767262111520635

theorem tailTrace_2797244 : CollatzResearch.WordTrace tailWord_2797244 prefixEnd_2797244 159592297767262111520635 := by
  unfold tailWord_2797244
  simp only [CollatzResearch.WordTrace]
  refine ⟨51011935139035097043091393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68015913518713462724121857 51011935139035097043091393)
  ·
    refine ⟨38258951354276322782318545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51011935139035097043091393 38258951354276322782318545)
    ·
      refine ⟨28694213515707242086738909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38258951354276322782318545 28694213515707242086738909)
      ·
        refine ⟨10760330068390215782527091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28694213515707242086738909 10760330068390215782527091)
        ·
          refine ⟨16140495102585323673790637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10760330068390215782527091 16140495102585323673790637)
          ·
            refine ⟨6052685663469496377671489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16140495102585323673790637 6052685663469496377671489)
            ·
              refine ⟨4539514247602122283253617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6052685663469496377671489 4539514247602122283253617)
              ·
                refine ⟨3404635685701591712440213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4539514247602122283253617 3404635685701591712440213)
                ·
                  refine ⟨159592297767262111520635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3404635685701591712440213 159592297767262111520635)
                  ·
                    rfl

theorem cell23_2797244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_2797244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797244 prefixEnd_2797244 := by exact prefixLift 2797244
  have htrace : WordTrace (prefixWord ++ tailWord_2797244) baseStart_2797244 baseEnd_2797244 := by
    simpa [prefixWord, tailWord_2797244, baseEnd_2797244] using wordTrace_append hprefix tailTrace_2797244
  have hstable : (prefixWord ++ tailWord_2797244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797244).length < 2 ^ (prefixWord ++ tailWord_2797244).sum := by decide
  have hdescent : baseEnd_2797244 < baseStart_2797244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797261 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 6]
def baseStart_2797261 : Nat := 118140960795 + 2797261 * 2 ^ 59
def prefixEnd_2797261 : Nat := 4983230072969 + 3 ^ 40 * 2797261 * 2
def baseEnd_2797261 : Nat := 159593267675165048574793

theorem tailTrace_2797261 : CollatzResearch.WordTrace tailWord_2797261 prefixEnd_2797261 159593267675165048574793 := by
  unfold tailWord_2797261
  simp only [CollatzResearch.WordTrace]
  refine ⟨102024490319008605989551637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68016326879339070659701091 102024490319008605989551637)
  ·
    refine ⟨4782397983703528405760233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102024490319008605989551637 4782397983703528405760233)
    ·
      refine ⟨3586798487777646304320175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4782397983703528405760233 3586798487777646304320175)
      ·
        refine ⟨5380197731666469456480263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3586798487777646304320175 5380197731666469456480263)
        ·
          refine ⟨8070296597499704184720395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5380197731666469456480263 8070296597499704184720395)
          ·
            refine ⟨12105444896249556277080593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8070296597499704184720395 12105444896249556277080593)
            ·
              refine ⟨9079083672187167207810445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12105444896249556277080593 9079083672187167207810445)
              ·
                refine ⟨3404656377070187702928917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9079083672187167207810445 3404656377070187702928917)
                ·
                  refine ⟨159593267675165048574793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3404656377070187702928917 159593267675165048574793)
                  ·
                    rfl

theorem cell23_2797261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_2797261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797261 prefixEnd_2797261 := by exact prefixLift 2797261
  have htrace : WordTrace (prefixWord ++ tailWord_2797261) baseStart_2797261 baseEnd_2797261 := by
    simpa [prefixWord, tailWord_2797261, baseEnd_2797261] using wordTrace_append hprefix tailTrace_2797261
  have hstable : (prefixWord ++ tailWord_2797261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797261).length < 2 ^ (prefixWord ++ tailWord_2797261).sum := by decide
  have hdescent : baseEnd_2797261 < baseStart_2797261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797281 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_2797281 : Nat := 118140960795 + 2797281 * 2 ^ 59
def prefixEnd_2797281 : Nat := 4983230072969 + 3 ^ 40 * 2797281 * 2
def baseEnd_2797281 : Nat := 1436349678689575358923045

theorem tailTrace_2797281 : CollatzResearch.WordTrace tailWord_2797281 prefixEnd_2797281 1436349678689575358923045 := by
  unfold tailWord_2797281
  simp only [CollatzResearch.WordTrace]
  refine ⟨102025219778936149405279697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68016813185957432936853131 102025219778936149405279697)
  ·
    refine ⟨76518914834202112053959773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102025219778936149405279697 76518914834202112053959773)
    ·
      refine ⟨28694593062825792020234915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76518914834202112053959773 28694593062825792020234915)
      ·
        refine ⟨43041889594238688030352373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28694593062825792020234915 43041889594238688030352373)
        ·
          refine ⟨4035177149459877002845535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43041889594238688030352373 4035177149459877002845535)
          ·
            refine ⟨6052765724189815504268303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035177149459877002845535 6052765724189815504268303)
            ·
              refine ⟨9079148586284723256402455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6052765724189815504268303 9079148586284723256402455)
              ·
                refine ⟨13618722879427084884603683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9079148586284723256402455 13618722879427084884603683)
                ·
                  refine ⟨20428084319140627326905525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13618722879427084884603683 20428084319140627326905525)
                  ·
                    refine ⟨1915132904919433811897393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20428084319140627326905525 1915132904919433811897393)
                    ·
                      refine ⟨1436349678689575358923045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915132904919433811897393 1436349678689575358923045)
                      ·
                        rfl

theorem cell23_2797281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_2797281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797281 prefixEnd_2797281 := by exact prefixLift 2797281
  have htrace : WordTrace (prefixWord ++ tailWord_2797281) baseStart_2797281 baseEnd_2797281 := by
    simpa [prefixWord, tailWord_2797281, baseEnd_2797281] using wordTrace_append hprefix tailTrace_2797281
  have hstable : (prefixWord ++ tailWord_2797281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797281).length < 2 ^ (prefixWord ++ tailWord_2797281).sum := by decide
  have hdescent : baseEnd_2797281 < baseStart_2797281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797288 : List Nat := [2, 1, 4, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_2797288 : Nat := 118140960795 + 2797288 * 2 ^ 59
def prefixEnd_2797288 : Nat := 4983230072969 + 3 ^ 40 * 2797288 * 2
def baseEnd_2797288 : Nat := 1436353273054156831535513

theorem tailTrace_2797288 : CollatzResearch.WordTrace tailWord_2797288 prefixEnd_2797288 1436353273054156831535513 := by
  unfold tailWord_2797288
  simp only [CollatzResearch.WordTrace]
  refine ⟨51012737544955394800392259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68016983393273859733856345 51012737544955394800392259)
  ·
    refine ⟨76519106317433092200588389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51012737544955394800392259 76519106317433092200588389)
    ·
      refine ⟨14347332434518704787610323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76519106317433092200588389 14347332434518704787610323)
      ·
        refine ⟨21520998651778057181415485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14347332434518704787610323 21520998651778057181415485)
        ·
          refine ⟨8070374494416771443030807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21520998651778057181415485 8070374494416771443030807)
          ·
            refine ⟨12105561741625157164546211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8070374494416771443030807 12105561741625157164546211)
            ·
              refine ⟨18158342612437735746819317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12105561741625157164546211 18158342612437735746819317)
              ·
                refine ⟨1702344619916037726264311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18158342612437735746819317 1702344619916037726264311)
                ·
                  refine ⟨2553516929874056589396467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702344619916037726264311 2553516929874056589396467)
                  ·
                    refine ⟨3830275394811084884094701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2553516929874056589396467 3830275394811084884094701)
                    ·
                      refine ⟨1436353273054156831535513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3830275394811084884094701 1436353273054156831535513)
                      ·
                        rfl

theorem cell23_2797288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_2797288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797288 prefixEnd_2797288 := by exact prefixLift 2797288
  have htrace : WordTrace (prefixWord ++ tailWord_2797288) baseStart_2797288 baseEnd_2797288 := by
    simpa [prefixWord, tailWord_2797288, baseEnd_2797288] using wordTrace_append hprefix tailTrace_2797288
  have hstable : (prefixWord ++ tailWord_2797288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797288).length < 2 ^ (prefixWord ++ tailWord_2797288).sum := by decide
  have hdescent : baseEnd_2797288 < baseStart_2797288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797304 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 2, 4]
def baseStart_2797304 : Nat := 118140960795 + 2797304 * 2 ^ 59
def prefixEnd_2797304 : Nat := 4983230072969 + 3 ^ 40 * 2797304 * 2
def baseEnd_2797304 : Nat := 478787162914876256311813

theorem tailTrace_2797304 : CollatzResearch.WordTrace tailWord_2797304 prefixEnd_2797304 478787162914876256311813 := by
  unfold tailWord_2797304
  simp only [CollatzResearch.WordTrace]
  refine ⟨51013029328926412166683483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68017372438568549555577977 51013029328926412166683483)
  ·
    refine ⟨76519543993389618250025225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51013029328926412166683483 76519543993389618250025225)
    ·
      refine ⟨57389657995042213687518919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76519543993389618250025225 57389657995042213687518919)
      ·
        refine ⟨86084486992563320531278379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57389657995042213687518919 86084486992563320531278379)
        ·
          refine ⟨129126730488844980796917569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86084486992563320531278379 129126730488844980796917569)
          ·
            refine ⟨96845047866633735597688177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129126730488844980796917569 96845047866633735597688177)
            ·
              refine ⟨72633785899975301698266133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96845047866633735597688177 72633785899975301698266133)
              ·
                refine ⟨3404708714061342267106225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72633785899975301698266133 3404708714061342267106225)
                ·
                  refine ⟨2553531535546006700329669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404708714061342267106225 2553531535546006700329669)
                  ·
                    refine ⟨478787162914876256311813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2553531535546006700329669 478787162914876256311813)
                    ·
                      rfl

theorem cell23_2797304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_2797304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797304 prefixEnd_2797304 := by exact prefixLift 2797304
  have htrace : WordTrace (prefixWord ++ tailWord_2797304) baseStart_2797304 baseEnd_2797304 := by
    simpa [prefixWord, tailWord_2797304, baseEnd_2797304] using wordTrace_append hprefix tailTrace_2797304
  have hstable : (prefixWord ++ tailWord_2797304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797304).length < 2 ^ (prefixWord ++ tailWord_2797304).sum := by decide
  have hdescent : baseEnd_2797304 < baseStart_2797304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797311 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 3, 2, 2]
def baseStart_2797311 : Nat := 118140960795 + 2797311 * 2 ^ 59
def prefixEnd_2797311 : Nat := 4983230072969 + 3 ^ 40 * 2797311 * 2
def baseEnd_2797311 : Nat := 1436365083109210241547907

theorem tailTrace_2797311 : CollatzResearch.WordTrace tailWord_2797311 prefixEnd_2797311 1436365083109210241547907 := by
  unfold tailWord_2797311
  simp only [CollatzResearch.WordTrace]
  refine ⟨102026313968827464528871787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68017542645884976352581191 102026313968827464528871787)
  ·
    refine ⟨153039470953241196793307681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102026313968827464528871787 153039470953241196793307681)
    ·
      refine ⟨114779603214930897594980761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153039470953241196793307681 114779603214930897594980761)
      ·
        refine ⟨86084702411198173196235571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114779603214930897594980761 86084702411198173196235571)
        ·
          refine ⟨129127053616797259794353357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86084702411198173196235571 129127053616797259794353357)
          ·
            refine ⟨48422645106298972422882509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129127053616797259794353357 48422645106298972422882509)
            ·
              refine ⟨18158491914862114658580941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48422645106298972422882509 18158491914862114658580941)
              ·
                refine ⟨6809434468073292996967853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18158491914862114658580941 6809434468073292996967853)
                ·
                  refine ⟨2553537925527484873862945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6809434468073292996967853 2553537925527484873862945)
                  ·
                    refine ⟨1915153444145613655397209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2553537925527484873862945 1915153444145613655397209)
                    ·
                      refine ⟨1436365083109210241547907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915153444145613655397209 1436365083109210241547907)
                      ·
                        rfl

theorem cell23_2797311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_2797311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797311 prefixEnd_2797311 := by exact prefixLift 2797311
  have htrace : WordTrace (prefixWord ++ tailWord_2797311) baseStart_2797311 baseEnd_2797311 := by
    simpa [prefixWord, tailWord_2797311, baseEnd_2797311] using wordTrace_append hprefix tailTrace_2797311
  have hstable : (prefixWord ++ tailWord_2797311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797311).length < 2 ^ (prefixWord ++ tailWord_2797311).sum := by decide
  have hdescent : baseEnd_2797311 < baseStart_2797311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797324 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_2797324 : Nat := 118140960795 + 2797324 * 2 ^ 59
def prefixEnd_2797324 : Nat := 4983230072969 + 3 ^ 40 * 2797324 * 2
def baseEnd_2797324 : Nat := 1436371758357718690685347

theorem tailTrace_2797324 : CollatzResearch.WordTrace tailWord_2797324 prefixEnd_2797324 1436371758357718690685347 := by
  unfold tailWord_2797324
  simp only [CollatzResearch.WordTrace]
  refine ⟨51013394058890183874547513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68017858745186911832730017 51013394058890183874547513)
  ·
    refine ⟨38260045544167637905910635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51013394058890183874547513 38260045544167637905910635)
    ·
      refine ⟨57390068316251456858865953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38260045544167637905910635 57390068316251456858865953)
      ·
        refine ⟨43042551237188592644149465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57390068316251456858865953 43042551237188592644149465)
        ·
          refine ⟨32281913427891444483112099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43042551237188592644149465 32281913427891444483112099)
          ·
            refine ⟨48422870141837166724668149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32281913427891444483112099 48422870141837166724668149)
            ·
              refine ⟨4539644075797234380437639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48422870141837166724668149 4539644075797234380437639)
              ·
                refine ⟨6809466113695851570656459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4539644075797234380437639 6809466113695851570656459)
                ·
                  refine ⟨10214199170543777355984689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6809466113695851570656459 10214199170543777355984689)
                  ·
                    refine ⟨7660649377907833016988517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10214199170543777355984689 7660649377907833016988517)
                    ·
                      refine ⟨1436371758357718690685347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7660649377907833016988517 1436371758357718690685347)
                      ·
                        rfl

theorem cell23_2797324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_2797324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797324 prefixEnd_2797324 := by exact prefixLift 2797324
  have htrace : WordTrace (prefixWord ++ tailWord_2797324) baseStart_2797324 baseEnd_2797324 := by
    simpa [prefixWord, tailWord_2797324, baseEnd_2797324] using wordTrace_append hprefix tailTrace_2797324
  have hstable : (prefixWord ++ tailWord_2797324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797324).length < 2 ^ (prefixWord ++ tailWord_2797324).sum := by decide
  have hdescent : baseEnd_2797324 < baseStart_2797324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797344 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2797344 : Nat := 118140960795 + 2797344 * 2 ^ 59
def prefixEnd_2797344 : Nat := 4983230072969 + 3 ^ 40 * 2797344 * 2
def baseEnd_2797344 : Nat := 1436382027970808612435255

theorem tailTrace_2797344 : CollatzResearch.WordTrace tailWord_2797344 prefixEnd_2797344 1436382027970808612435255 := by
  unfold tailWord_2797344
  simp only [CollatzResearch.WordTrace]
  refine ⟨51013758788853955582411543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68018345051805274109882057 51013758788853955582411543)
  ·
    refine ⟨76520638183280933373617315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51013758788853955582411543 76520638183280933373617315)
    ·
      refine ⟨114780957274921400060425973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76520638183280933373617315 114780957274921400060425973)
      ·
        refine ⟨10760714744523881255664935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114780957274921400060425973 10760714744523881255664935)
        ·
          refine ⟨16141072116785821883497403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10760714744523881255664935 16141072116785821883497403)
          ·
            refine ⟨24211608175178732825246105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16141072116785821883497403 24211608175178732825246105)
            ·
              refine ⟨18158706131384049618934579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24211608175178732825246105 18158706131384049618934579)
              ·
                refine ⟨27238059197076074428401869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18158706131384049618934579 27238059197076074428401869)
                ·
                  refine ⟨10214272198903527910650701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27238059197076074428401869 10214272198903527910650701)
                  ·
                    refine ⟨3830352074588822966494013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10214272198903527910650701 3830352074588822966494013)
                    ·
                      refine ⟨1436382027970808612435255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3830352074588822966494013 1436382027970808612435255)
                      ·
                        rfl

theorem cell23_2797344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2797344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797344 prefixEnd_2797344 := by exact prefixLift 2797344
  have htrace : WordTrace (prefixWord ++ tailWord_2797344) baseStart_2797344 baseEnd_2797344 := by
    simpa [prefixWord, tailWord_2797344, baseEnd_2797344] using wordTrace_append hprefix tailTrace_2797344
  have hstable : (prefixWord ++ tailWord_2797344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797344).length < 2 ^ (prefixWord ++ tailWord_2797344).sum := by decide
  have hdescent : baseEnd_2797344 < baseStart_2797344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797345 : List Nat := [1, 2, 3, 2, 1, 3, 3, 3, 1, 2, 2]
def baseStart_2797345 : Nat := 118140960795 + 2797345 * 2 ^ 59
def prefixEnd_2797345 : Nat := 4983230072969 + 3 ^ 40 * 2797345 * 2
def baseEnd_2797345 : Nat := 1436382541451463108522751

theorem tailTrace_2797345 : CollatzResearch.WordTrace tailWord_2797345 prefixEnd_2797345 1436382541451463108522751 := by
  unfold tailWord_2797345
  simp only [CollatzResearch.WordTrace]
  refine ⟨102027554050704288335609489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68018369367136192223739659 102027554050704288335609489)
  ·
    refine ⟨76520665538028216251707117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102027554050704288335609489 76520665538028216251707117)
    ·
      refine ⟨28695249576760581094390169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76520665538028216251707117 28695249576760581094390169)
      ·
        refine ⟨21521437182570435820792627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28695249576760581094390169 21521437182570435820792627)
        ·
          refine ⟨32282155773855653731188941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21521437182570435820792627 32282155773855653731188941)
          ·
            refine ⟨12105808415195870149195853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32282155773855653731188941 12105808415195870149195853)
            ·
              refine ⟨4539678155698451305948445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12105808415195870149195853 4539678155698451305948445)
              ·
                refine ⟨1702379308386919239730667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4539678155698451305948445 1702379308386919239730667)
                ·
                  refine ⟨2553568962580378859596001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702379308386919239730667 2553568962580378859596001)
                  ·
                    refine ⟨1915176721935284144697001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2553568962580378859596001 1915176721935284144697001)
                    ·
                      refine ⟨1436382541451463108522751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1915176721935284144697001 1436382541451463108522751)
                      ·
                        rfl

theorem cell23_2797345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_2797345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2797345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2797345 prefixEnd_2797345 := by exact prefixLift 2797345
  have htrace : WordTrace (prefixWord ++ tailWord_2797345) baseStart_2797345 baseEnd_2797345 := by
    simpa [prefixWord, tailWord_2797345, baseEnd_2797345] using wordTrace_append hprefix tailTrace_2797345
  have hstable : (prefixWord ++ tailWord_2797345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797345).length < 2 ^ (prefixWord ++ tailWord_2797345).sum := by decide
  have hdescent : baseEnd_2797345 < baseStart_2797345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
