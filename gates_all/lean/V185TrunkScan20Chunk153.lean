import V185TrunkScan20Chunk152

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_930919 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 3]
def baseStart_930919 : Nat := 118140960795 + 930919 * 2 ^ 59
def prefixEnd_930919 : Nat := 4983230072969 + 3 ^ 40 * 930919 * 2
def baseEnd_930919 : Nat := 424896797691509785627811

theorem tailTrace_930919 : CollatzResearch.WordTrace tailWord_930919 prefixEnd_930919 424896797691509785627811 := by
  unfold tailWord_930919
  simp only [CollatzResearch.WordTrace]
  refine ⟨33953405314446926152603811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22635603542964617435069207 33953405314446926152603811)
  ·
    refine ⟨50930107971670389228905717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33953405314446926152603811 50930107971670389228905717)
    ·
      refine ⟨4774697622344098990209911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50930107971670389228905717 4774697622344098990209911)
      ·
        refine ⟨7162046433516148485314867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774697622344098990209911 7162046433516148485314867)
        ·
          refine ⟨10743069650274222727972301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7162046433516148485314867 10743069650274222727972301)
          ·
            refine ⟨4028651118852833522989613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10743069650274222727972301 4028651118852833522989613)
            ·
              refine ⟨1510744169569812571121105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4028651118852833522989613 1510744169569812571121105)
              ·
                refine ⟨1133058127177359428340829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510744169569812571121105 1133058127177359428340829)
                ·
                  refine ⟨424896797691509785627811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133058127177359428340829 424896797691509785627811)
                  ·
                    rfl

theorem cell20_930919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_930919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930919 prefixEnd_930919 := by exact prefixLift 930919
  have htrace : WordTrace (prefixWord ++ tailWord_930919) baseStart_930919 baseEnd_930919 := by
    simpa [prefixWord, tailWord_930919, baseEnd_930919] using wordTrace_append hprefix tailTrace_930919
  have hstable : (prefixWord ++ tailWord_930919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930919).length < 2 ^ (prefixWord ++ tailWord_930919).sum := by decide
  have hdescent : baseEnd_930919 < baseStart_930919 := by decide
  rcases family_descends (prefixWord ++ tailWord_930919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930926 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_930926 : Nat := 118140960795 + 930926 * 2 ^ 59
def prefixEnd_930926 : Nat := 4983230072969 + 3 ^ 40 * 930926 * 2
def baseEnd_930926 : Nat := 424899992682248872394449

theorem tailTrace_930926 : CollatzResearch.WordTrace tailWord_930926 prefixEnd_930926 424899992682248872394449 := by
  unfold tailWord_930926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244207578177695793513579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22635773750281044232072421 4244207578177695793513579)
  ·
    refine ⟨6366311367266543690270369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4244207578177695793513579 6366311367266543690270369)
    ·
      refine ⟨4774733525449907767702777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6366311367266543690270369 4774733525449907767702777)
      ·
        refine ⟨3581050144087430825777083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4774733525449907767702777 3581050144087430825777083)
        ·
          refine ⟨5371575216131146238665625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581050144087430825777083 5371575216131146238665625)
          ·
            refine ⟨4028681412098359678999219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5371575216131146238665625 4028681412098359678999219)
            ·
              refine ⟨6043022118147539518498829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028681412098359678999219 6043022118147539518498829)
              ·
                refine ⟨2266133294305327319437061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6043022118147539518498829 2266133294305327319437061)
                ·
                  refine ⟨424899992682248872394449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266133294305327319437061 424899992682248872394449)
                  ·
                    rfl

theorem cell20_930926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_930926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930926 prefixEnd_930926 := by exact prefixLift 930926
  have htrace : WordTrace (prefixWord ++ tailWord_930926) baseStart_930926 baseEnd_930926 := by
    simpa [prefixWord, tailWord_930926, baseEnd_930926] using wordTrace_append hprefix tailTrace_930926
  have hstable : (prefixWord ++ tailWord_930926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930926).length < 2 ^ (prefixWord ++ tailWord_930926).sum := by decide
  have hdescent : baseEnd_930926 < baseStart_930926 := by decide
  rcases family_descends (prefixWord ++ tailWord_930926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930942 : List Nat := [4, 2, 4, 1, 2, 1, 2, 4]
def baseStart_930942 : Nat := 118140960795 + 930942 * 2 ^ 59
def prefixEnd_930942 : Nat := 4983230072969 + 3 ^ 40 * 930942 * 2
def baseEnd_930942 : Nat := 141635765172741309287017

theorem tailTrace_930942 : CollatzResearch.WordTrace tailWord_930942 prefixEnd_930942 141635765172741309287017 := by
  unfold tailWord_930942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244280524170450135086385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22636162795575734053794053 4244280524170450135086385)
  ·
    refine ⟨3183210393127837601314789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4244280524170450135086385 3183210393127837601314789)
    ·
      refine ⟨596851948711469550246523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3183210393127837601314789 596851948711469550246523)
      ·
        refine ⟨895277923067204325369785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596851948711469550246523 895277923067204325369785)
        ·
          refine ⟨671458442300403244027339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895277923067204325369785 671458442300403244027339)
          ·
            refine ⟨1007187663450604866041009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671458442300403244027339 1007187663450604866041009)
            ·
              refine ⟨755390747587953649530757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007187663450604866041009 755390747587953649530757)
              ·
                refine ⟨141635765172741309287017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 755390747587953649530757 141635765172741309287017)
                ·
                  rfl

theorem cell20_930942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_930942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930942 prefixEnd_930942 := by exact prefixLift 930942
  have htrace : WordTrace (prefixWord ++ tailWord_930942) baseStart_930942 baseEnd_930942 := by
    simpa [prefixWord, tailWord_930942, baseEnd_930942] using wordTrace_append hprefix tailTrace_930942
  have hstable : (prefixWord ++ tailWord_930942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930942).length < 2 ^ (prefixWord ++ tailWord_930942).sum := by decide
  have hdescent : baseEnd_930942 < baseStart_930942 := by decide
  rcases family_descends (prefixWord ++ tailWord_930942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930947 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_930947 : Nat := 118140960795 + 930947 * 2 ^ 59
def prefixEnd_930947 : Nat := 4983230072969 + 3 ^ 40 * 930947 * 2
def baseEnd_930947 : Nat := 424909577654466132694363

theorem tailTrace_930947 : CollatzResearch.WordTrace tailWord_930947 prefixEnd_930947 424909577654466132694363 := by
  unfold tailWord_930947
  simp only [CollatzResearch.WordTrace]
  refine ⟨33954426558345486934623095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22636284372230324623082063 33954426558345486934623095)
  ·
    refine ⟨50931639837518230401934643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33954426558345486934623095 50931639837518230401934643)
    ·
      refine ⟨76397459756277345602901965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50931639837518230401934643 76397459756277345602901965)
      ·
        refine ⟨28649047408604004601088237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76397459756277345602901965 28649047408604004601088237)
        ·
          refine ⟨10743392778226501725408089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28649047408604004601088237 10743392778226501725408089)
          ·
            refine ⟨8057544583669876294056067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10743392778226501725408089 8057544583669876294056067)
            ·
              refine ⟨12086316875504814441084101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8057544583669876294056067 12086316875504814441084101)
              ·
                refine ⟨2266184414157152707703269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12086316875504814441084101 2266184414157152707703269)
                ·
                  refine ⟨424909577654466132694363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266184414157152707703269 424909577654466132694363)
                  ·
                    rfl

theorem cell20_930947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_930947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930947 prefixEnd_930947 := by exact prefixLift 930947
  have htrace : WordTrace (prefixWord ++ tailWord_930947) baseStart_930947 baseEnd_930947 := by
    simpa [prefixWord, tailWord_930947, baseEnd_930947] using wordTrace_append hprefix tailTrace_930947
  have hstable : (prefixWord ++ tailWord_930947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930947).length < 2 ^ (prefixWord ++ tailWord_930947).sum := by decide
  have hdescent : baseEnd_930947 < baseStart_930947 := by decide
  rcases family_descends (prefixWord ++ tailWord_930947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930995 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 3]
def baseStart_930995 : Nat := 118140960795 + 930995 * 2 ^ 59
def prefixEnd_930995 : Nat := 4983230072969 + 3 ^ 40 * 930995 * 2
def baseEnd_930995 : Nat := 424931486162391299094167

theorem tailTrace_930995 : CollatzResearch.WordTrace tailWord_930995 prefixEnd_930995 424931486162391299094167 := by
  unfold tailWord_930995
  simp only [CollatzResearch.WordTrace]
  refine ⟨33956177262171591132370439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22637451508114394088246959 33956177262171591132370439)
  ·
    refine ⟨50934265893257386698555659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33956177262171591132370439 50934265893257386698555659)
    ·
      refine ⟨76401398839886080047833489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50934265893257386698555659 76401398839886080047833489)
      ·
        refine ⟨57301049129914560035875117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76401398839886080047833489 57301049129914560035875117)
        ·
          refine ⟨21487893423717960013453169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57301049129914560035875117 21487893423717960013453169)
          ·
            refine ⟨16115920067788470010089877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21487893423717960013453169 16115920067788470010089877)
            ·
              refine ⟨755433753177584531722963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16115920067788470010089877 755433753177584531722963)
              ·
                refine ⟨1133150629766376797584445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755433753177584531722963 1133150629766376797584445)
                ·
                  refine ⟨424931486162391299094167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133150629766376797584445 424931486162391299094167)
                  ·
                    rfl

theorem cell20_930995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 3].length) (baseStart_930995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930995 prefixEnd_930995 := by exact prefixLift 930995
  have htrace : WordTrace (prefixWord ++ tailWord_930995) baseStart_930995 baseEnd_930995 := by
    simpa [prefixWord, tailWord_930995, baseEnd_930995] using wordTrace_append hprefix tailTrace_930995
  have hstable : (prefixWord ++ tailWord_930995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930995).length < 2 ^ (prefixWord ++ tailWord_930995).sum := by decide
  have hdescent : baseEnd_930995 < baseStart_930995 := by decide
  rcases family_descends (prefixWord ++ tailWord_930995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931123 : List Nat := [1, 1, 1, 2, 5, 2, 4, 4]
def baseStart_931123 : Nat := 118140960795 + 931123 * 2 ^ 59
def prefixEnd_931123 : Nat := 4983230072969 + 3 ^ 40 * 931123 * 2
def baseEnd_931123 : Nat := 141663302950063914275659

theorem tailTrace_931123 : CollatzResearch.WordTrace tailWord_931123 prefixEnd_931123 141663302950063914275659 := by
  unfold tailWord_931123
  simp only [CollatzResearch.WordTrace]
  refine ⟨33960845805707868993030023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22640563870471912662020015 33960845805707868993030023)
  ·
    refine ⟨50941268708561803489545035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33960845805707868993030023 50941268708561803489545035)
    ·
      refine ⟨76411903062842705234317553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50941268708561803489545035 76411903062842705234317553)
      ·
        refine ⟨57308927297132028925738165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76411903062842705234317553 57308927297132028925738165)
        ·
          refine ⟨5372711934106127711787953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57308927297132028925738165 5372711934106127711787953)
          ·
            refine ⟨4029533950579595783840965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5372711934106127711787953 4029533950579595783840965)
            ·
              refine ⟨755537615733674209470181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4029533950579595783840965 755537615733674209470181)
              ·
                refine ⟨141663302950063914275659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 755537615733674209470181 141663302950063914275659)
                ·
                  rfl

theorem cell20_931123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 4].length) (baseStart_931123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931123 prefixEnd_931123 := by exact prefixLift 931123
  have htrace : WordTrace (prefixWord ++ tailWord_931123) baseStart_931123 baseEnd_931123 := by
    simpa [prefixWord, tailWord_931123, baseEnd_931123] using wordTrace_append hprefix tailTrace_931123
  have hstable : (prefixWord ++ tailWord_931123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931123).length < 2 ^ (prefixWord ++ tailWord_931123).sum := by decide
  have hdescent : baseEnd_931123 < baseStart_931123 := by decide
  rcases family_descends (prefixWord ++ tailWord_931123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931129 : List Nat := [1, 2, 1, 6, 3, 1, 1, 3, 2]
def baseStart_931129 : Nat := 118140960795 + 931129 * 2 ^ 59
def prefixEnd_931129 : Nat := 4983230072969 + 3 ^ 40 * 931129 * 2
def baseEnd_931129 : Nat := 424992647413682388626953

theorem tailTrace_931129 : CollatzResearch.WordTrace tailWord_931129 prefixEnd_931129 424992647413682388626953 := by
  unfold tailWord_931129
  simp only [CollatzResearch.WordTrace]
  refine ⟨33961064643686132017748441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22640709762457421345165627 33961064643686132017748441)
  ·
    refine ⟨25470798482764599013311331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33961064643686132017748441 25470798482764599013311331)
    ·
      refine ⟨38206197724146898519966997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25470798482764599013311331 38206197724146898519966997)
      ·
        refine ⟨1790915518319385868123453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38206197724146898519966997 1790915518319385868123453)
        ·
          refine ⟨671593319369769700546295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1790915518319385868123453 671593319369769700546295)
          ·
            refine ⟨1007389979054654550819443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671593319369769700546295 1007389979054654550819443)
            ·
              refine ⟨1511084968581981826229165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007389979054654550819443 1511084968581981826229165)
              ·
                refine ⟨566656863218243184835937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1511084968581981826229165 566656863218243184835937)
                ·
                  refine ⟨424992647413682388626953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566656863218243184835937 424992647413682388626953)
                  ·
                    rfl

theorem cell20_931129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_931129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931129 prefixEnd_931129 := by exact prefixLift 931129
  have htrace : WordTrace (prefixWord ++ tailWord_931129) baseStart_931129 baseEnd_931129 := by
    simpa [prefixWord, tailWord_931129, baseEnd_931129] using wordTrace_append hprefix tailTrace_931129
  have hstable : (prefixWord ++ tailWord_931129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931129).length < 2 ^ (prefixWord ++ tailWord_931129).sum := by decide
  have hdescent : baseEnd_931129 < baseStart_931129 := by decide
  rcases family_descends (prefixWord ++ tailWord_931129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931140 : List Nat := [2, 3, 4, 1, 1, 3, 6]
def baseStart_931140 : Nat := 118140960795 + 931140 * 2 ^ 59
def prefixEnd_931140 : Nat := 4983230072969 + 3 ^ 40 * 931140 * 2
def baseEnd_931140 : Nat := 47221963123712804362249

theorem tailTrace_931140 : CollatzResearch.WordTrace tailWord_931140 prefixEnd_931140 47221963123712804362249 := by
  unfold tailWord_931140
  simp only [CollatzResearch.WordTrace]
  refine ⟨16980732923323140448199437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22640977231097520597599249 16980732923323140448199437)
  ·
    refine ⟨6367774846246177668074789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16980732923323140448199437 6367774846246177668074789)
    ·
      refine ⟨1193957783671158312764023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6367774846246177668074789 1193957783671158312764023)
      ·
        refine ⟨1790936675506737469146035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193957783671158312764023 1790936675506737469146035)
        ·
          refine ⟨2686405013260106203719053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790936675506737469146035 2686405013260106203719053)
          ·
            refine ⟨1007401879972539826394645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2686405013260106203719053 1007401879972539826394645)
            ·
              refine ⟨47221963123712804362249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1007401879972539826394645 47221963123712804362249)
              ·
                rfl

theorem cell20_931140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 6].length) (baseStart_931140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931140 prefixEnd_931140 := by exact prefixLift 931140
  have htrace : WordTrace (prefixWord ++ tailWord_931140) baseStart_931140 baseEnd_931140 := by
    simpa [prefixWord, tailWord_931140, baseEnd_931140] using wordTrace_append hprefix tailTrace_931140
  have hstable : (prefixWord ++ tailWord_931140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931140).length < 2 ^ (prefixWord ++ tailWord_931140).sum := by decide
  have hdescent : baseEnd_931140 < baseStart_931140 := by decide
  rcases family_descends (prefixWord ++ tailWord_931140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931202 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_931202 : Nat := 118140960795 + 931202 * 2 ^ 59
def prefixEnd_931202 : Nat := 4983230072969 + 3 ^ 40 * 931202 * 2
def baseEnd_931202 : Nat := 425025966602818579193321

theorem tailTrace_931202 : CollatzResearch.WordTrace tailWord_931202 prefixEnd_931202 425025966602818579193321 := by
  unfold tailWord_931202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490931793105416371288965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22642484781614443656770573 8490931793105416371288965)
  ·
    refine ⟨1592049711207265569616681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8490931793105416371288965 1592049711207265569616681)
    ·
      refine ⟨1194037283405449177212511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1592049711207265569616681 1194037283405449177212511)
      ·
        refine ⟨1791055925108173765818767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194037283405449177212511 1791055925108173765818767)
        ·
          refine ⟨2686583887662260648728151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791055925108173765818767 2686583887662260648728151)
          ·
            refine ⟨4029875831493390973092227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686583887662260648728151 4029875831493390973092227)
            ·
              refine ⟨6044813747240086459638341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4029875831493390973092227 6044813747240086459638341)
              ·
                refine ⟨1133402577607516211182189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6044813747240086459638341 1133402577607516211182189)
                ·
                  refine ⟨425025966602818579193321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133402577607516211182189 425025966602818579193321)
                  ·
                    rfl

theorem cell20_931202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_931202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931202 prefixEnd_931202 := by exact prefixLift 931202
  have htrace : WordTrace (prefixWord ++ tailWord_931202) baseStart_931202 baseEnd_931202 := by
    simpa [prefixWord, tailWord_931202, baseEnd_931202] using wordTrace_append hprefix tailTrace_931202
  have hstable : (prefixWord ++ tailWord_931202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931202).length < 2 ^ (prefixWord ++ tailWord_931202).sum := by decide
  have hdescent : baseEnd_931202 < baseStart_931202 := by decide
  rcases family_descends (prefixWord ++ tailWord_931202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931209 : List Nat := [1, 2, 1, 1, 7, 1, 1, 4, 2]
def baseStart_931209 : Nat := 118140960795 + 931209 * 2 ^ 59
def prefixEnd_931209 : Nat := 4983230072969 + 3 ^ 40 * 931209 * 2
def baseEnd_931209 : Nat := 425029161593557665959959

theorem tailTrace_931209 : CollatzResearch.WordTrace tailWord_931209 prefixEnd_931209 425029161593557665959959 := by
  unfold tailWord_931209
  simp only [CollatzResearch.WordTrace]
  refine ⟨33963982483396305680660681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22642654988930870453773787 33963982483396305680660681)
  ·
    refine ⟨25472986862547229260495511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33963982483396305680660681 25472986862547229260495511)
    ·
      refine ⟨38209480293820843890743267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25472986862547229260495511 38209480293820843890743267)
      ·
        refine ⟨57314220440731265836114901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38209480293820843890743267 57314220440731265836114901)
        ·
          refine ⟨1343302041579639043033943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 57314220440731265836114901 1343302041579639043033943)
          ·
            refine ⟨2014953062369458564550915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343302041579639043033943 2014953062369458564550915)
            ·
              refine ⟨3022429593554187846826373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014953062369458564550915 3022429593554187846826373)
              ·
                refine ⟨566705548791410221279945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3022429593554187846826373 566705548791410221279945)
                ·
                  refine ⟨425029161593557665959959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566705548791410221279945 425029161593557665959959)
                  ·
                    rfl

theorem cell20_931209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_931209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931209 prefixEnd_931209 := by exact prefixLift 931209
  have htrace : WordTrace (prefixWord ++ tailWord_931209) baseStart_931209 baseEnd_931209 := by
    simpa [prefixWord, tailWord_931209, baseEnd_931209] using wordTrace_append hprefix tailTrace_931209
  have hstable : (prefixWord ++ tailWord_931209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931209).length < 2 ^ (prefixWord ++ tailWord_931209).sum := by decide
  have hdescent : baseEnd_931209 < baseStart_931209 := by decide
  rcases family_descends (prefixWord ++ tailWord_931209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931268 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_931268 : Nat := 118140960795 + 931268 * 2 ^ 59
def prefixEnd_931268 : Nat := 4983230072969 + 3 ^ 40 * 931268 * 2
def baseEnd_931268 : Nat := 425056090801215682993051

theorem tailTrace_931268 : CollatzResearch.WordTrace tailWord_931268 prefixEnd_931268 425056090801215682993051 := by
  unfold tailWord_931268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16983067195091279378529229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22644089593455039171372305 16983067195091279378529229)
  ·
    refine ⟨6368650198159229766948461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16983067195091279378529229 6368650198159229766948461)
    ·
      refine ⟨2388243824309711162605673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6368650198159229766948461 2388243824309711162605673)
      ·
        refine ⟨1791182868232283371954255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2388243824309711162605673 1791182868232283371954255)
        ·
          refine ⟨2686774302348425057931383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791182868232283371954255 2686774302348425057931383)
          ·
            refine ⟨4030161453522637586897075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686774302348425057931383 4030161453522637586897075)
            ·
              refine ⟨6045242180283956380345613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030161453522637586897075 6045242180283956380345613)
              ·
                refine ⟨2266965817606483642629605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6045242180283956380345613 2266965817606483642629605)
                ·
                  refine ⟨425056090801215682993051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266965817606483642629605 425056090801215682993051)
                  ·
                    rfl

theorem cell20_931268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_931268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931268 prefixEnd_931268 := by exact prefixLift 931268
  have htrace : WordTrace (prefixWord ++ tailWord_931268) baseStart_931268 baseEnd_931268 := by
    simpa [prefixWord, tailWord_931268, baseEnd_931268] using wordTrace_append hprefix tailTrace_931268
  have hstable : (prefixWord ++ tailWord_931268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931268).length < 2 ^ (prefixWord ++ tailWord_931268).sum := by decide
  have hdescent : baseEnd_931268 < baseStart_931268 := by decide
  rcases family_descends (prefixWord ++ tailWord_931268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931289 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_931289 : Nat := 118140960795 + 931289 * 2 ^ 59
def prefixEnd_931289 : Nat := 4983230072969 + 3 ^ 40 * 931289 * 2
def baseEnd_931289 : Nat := 425065675773432943292965

theorem tailTrace_931289 : CollatzResearch.WordTrace tailWord_931289 prefixEnd_931289 425065675773432943292965 := by
  unfold tailWord_931289
  simp only [CollatzResearch.WordTrace]
  refine ⟨33966900323106479343572921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22644600215404319562381947 33966900323106479343572921)
  ·
    refine ⟨25475175242329859507679691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33966900323106479343572921 25475175242329859507679691)
    ·
      refine ⟨38212762863494789261519537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25475175242329859507679691 38212762863494789261519537)
      ·
        refine ⟨28659572147621091946139653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38212762863494789261519537 28659572147621091946139653)
        ·
          refine ⟨5373669777678954739901185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28659572147621091946139653 5373669777678954739901185)
          ·
            refine ⟨4030252333259216054925889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5373669777678954739901185 4030252333259216054925889)
            ·
              refine ⟨3022689249944412041194417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4030252333259216054925889 3022689249944412041194417)
              ·
                refine ⟨2267016937458309030895813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022689249944412041194417 2267016937458309030895813)
                ·
                  refine ⟨425065675773432943292965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2267016937458309030895813 425065675773432943292965)
                  ·
                    rfl

theorem cell20_931289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_931289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931289 prefixEnd_931289 := by exact prefixLift 931289
  have htrace : WordTrace (prefixWord ++ tailWord_931289) baseStart_931289 baseEnd_931289 := by
    simpa [prefixWord, tailWord_931289, baseEnd_931289] using wordTrace_append hprefix tailTrace_931289
  have hstable : (prefixWord ++ tailWord_931289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931289).length < 2 ^ (prefixWord ++ tailWord_931289).sum := by decide
  have hdescent : baseEnd_931289 < baseStart_931289 := by decide
  rcases family_descends (prefixWord ++ tailWord_931289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931330 : List Nat := [3, 4, 1, 2, 1, 2, 2, 5]
def baseStart_931330 : Nat := 118140960795 + 931330 * 2 ^ 59
def prefixEnd_931330 : Nat := 4983230072969 + 3 ^ 40 * 931330 * 2
def baseEnd_931330 : Nat := 141694796430206340975377

theorem tailTrace_931330 : CollatzResearch.WordTrace tailWord_931330 prefixEnd_931330 141694796430206340975377 := by
  unfold tailWord_931330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492098928989485836453861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22645597143971962230543629 8492098928989485836453861)
  ·
    refine ⟨1592268549185528594335099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8492098928989485836453861 1592268549185528594335099)
    ·
      refine ⟨2388402823778292891502649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592268549185528594335099 2388402823778292891502649)
      ·
        refine ⟨1791302117833719668626987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2388402823778292891502649 1791302117833719668626987)
        ·
          refine ⟨2686953176750579502940481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791302117833719668626987 2686953176750579502940481)
          ·
            refine ⟨2015214882562934627205361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2686953176750579502940481 2015214882562934627205361)
            ·
              refine ⟨1511411161922200970404021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015214882562934627205361 1511411161922200970404021)
              ·
                refine ⟨141694796430206340975377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1511411161922200970404021 141694796430206340975377)
                ·
                  rfl

theorem cell20_931330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_931330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931330 prefixEnd_931330 := by exact prefixLift 931330
  have htrace : WordTrace (prefixWord ++ tailWord_931330) baseStart_931330 baseEnd_931330 := by
    simpa [prefixWord, tailWord_931330, baseEnd_931330] using wordTrace_append hprefix tailTrace_931330
  have hstable : (prefixWord ++ tailWord_931330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931330).length < 2 ^ (prefixWord ++ tailWord_931330).sum := by decide
  have hdescent : baseEnd_931330 < baseStart_931330 := by decide
  rcases family_descends (prefixWord ++ tailWord_931330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931424 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_931424 : Nat := 118140960795 + 931424 * 2 ^ 59
def prefixEnd_931424 : Nat := 4983230072969 + 3 ^ 40 * 931424 * 2
def baseEnd_931424 : Nat := 425127293451972473792413

theorem tailTrace_931424 : CollatzResearch.WordTrace tailWord_931424 prefixEnd_931424 425127293451972473792413 := by
  unfold tailWord_931424
  simp only [CollatzResearch.WordTrace]
  refine ⟨16985912088808698699868663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22647882785078264933158217 16985912088808698699868663)
  ·
    refine ⟨25478868133213048049802995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16985912088808698699868663 25478868133213048049802995)
    ·
      refine ⟨38218302199819572074704493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25478868133213048049802995 38218302199819572074704493)
      ·
        refine ⟨14331863324932339528014185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38218302199819572074704493 14331863324932339528014185)
        ·
          refine ⟨10748897493699254646010639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14331863324932339528014185 10748897493699254646010639)
          ·
            refine ⟨16123346240548881969015959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748897493699254646010639 16123346240548881969015959)
            ·
              refine ⟨24185019360823322953523939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16123346240548881969015959 24185019360823322953523939)
              ·
                refine ⟨36277529041234984430285909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24185019360823322953523939 36277529041234984430285909)
                ·
                  refine ⟨425127293451972473792413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36277529041234984430285909 425127293451972473792413)
                  ·
                    rfl

theorem cell20_931424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_931424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931424 prefixEnd_931424 := by exact prefixLift 931424
  have htrace : WordTrace (prefixWord ++ tailWord_931424) baseStart_931424 baseEnd_931424 := by
    simpa [prefixWord, tailWord_931424, baseEnd_931424] using wordTrace_append hprefix tailTrace_931424
  have hstable : (prefixWord ++ tailWord_931424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931424).length < 2 ^ (prefixWord ++ tailWord_931424).sum := by decide
  have hdescent : baseEnd_931424 < baseStart_931424 := by decide
  rcases family_descends (prefixWord ++ tailWord_931424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931434 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_931434 : Nat := 118140960795 + 931434 * 2 ^ 59
def prefixEnd_931434 : Nat := 4983230072969 + 3 ^ 40 * 931434 * 2
def baseEnd_931434 : Nat := 425131857724456883459039

theorem tailTrace_931434 : CollatzResearch.WordTrace tailWord_931434 prefixEnd_931434 425131857724456883459039 := by
  unfold tailWord_931434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493047226895292276900339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22648125938387446071734237 8493047226895292276900339)
  ·
    refine ⟨12739570840342938415350509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8493047226895292276900339 12739570840342938415350509)
    ·
      refine ⟨4777339065128601905756441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12739570840342938415350509 4777339065128601905756441)
      ·
        refine ⟨3583004298846451429317331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4777339065128601905756441 3583004298846451429317331)
        ·
          refine ⟨5374506448269677143975997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583004298846451429317331 5374506448269677143975997)
          ·
            refine ⟨2015439918101128928990999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5374506448269677143975997 2015439918101128928990999)
            ·
              refine ⟨3023159877151693393486499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2015439918101128928990999 3023159877151693393486499)
              ·
                refine ⟨4534739815727540090229749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023159877151693393486499 4534739815727540090229749)
                ·
                  refine ⟨425131857724456883459039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4534739815727540090229749 425131857724456883459039)
                  ·
                    rfl

theorem cell20_931434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_931434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931434 prefixEnd_931434 := by exact prefixLift 931434
  have htrace : WordTrace (prefixWord ++ tailWord_931434) baseStart_931434 baseEnd_931434 := by
    simpa [prefixWord, tailWord_931434, baseEnd_931434] using wordTrace_append hprefix tailTrace_931434
  have hstable : (prefixWord ++ tailWord_931434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931434).length < 2 ^ (prefixWord ++ tailWord_931434).sum := by decide
  have hdescent : baseEnd_931434 < baseStart_931434 := by decide
  rcases family_descends (prefixWord ++ tailWord_931434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931493 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_931493 : Nat := 118140960795 + 931493 * 2 ^ 59
def prefixEnd_931493 : Nat := 4983230072969 + 3 ^ 40 * 931493 * 2
def baseEnd_931493 : Nat := 425158786932114900492131

theorem tailTrace_931493 : CollatzResearch.WordTrace tailWord_931493 prefixEnd_931493 425158786932114900492131 := by
  unfold tailWord_931493
  simp only [CollatzResearch.WordTrace]
  refine ⟨33974340814367422183999133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22649560542911614789332755 33974340814367422183999133)
  ·
    refine ⟨12740377805387783318999675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33974340814367422183999133 12740377805387783318999675)
    ·
      refine ⟨19110566708081674978499513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12740377805387783318999675 19110566708081674978499513)
      ·
        refine ⟨14332925031061256233874635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19110566708081674978499513 14332925031061256233874635)
        ·
          refine ⟨21499387546591884350811953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14332925031061256233874635 21499387546591884350811953)
          ·
            refine ⟨16124540659943913263108965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21499387546591884350811953 16124540659943913263108965)
            ·
              refine ⟨3023351373739483736832931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16124540659943913263108965 3023351373739483736832931)
              ·
                refine ⟨4535027060609225605249397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023351373739483736832931 4535027060609225605249397)
                ·
                  refine ⟨425158786932114900492131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4535027060609225605249397 425158786932114900492131)
                  ·
                    rfl

theorem cell20_931493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_931493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931493 prefixEnd_931493 := by exact prefixLift 931493
  have htrace : WordTrace (prefixWord ++ tailWord_931493) baseStart_931493 baseEnd_931493 := by
    simpa [prefixWord, tailWord_931493, baseEnd_931493] using wordTrace_append hprefix tailTrace_931493
  have hstable : (prefixWord ++ tailWord_931493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931493).length < 2 ^ (prefixWord ++ tailWord_931493).sum := by decide
  have hdescent : baseEnd_931493 < baseStart_931493 := by decide
  rcases family_descends (prefixWord ++ tailWord_931493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931502 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_931502 : Nat := 118140960795 + 931502 * 2 ^ 59
def prefixEnd_931502 : Nat := 4983230072969 + 3 ^ 40 * 931502 * 2
def baseEnd_931502 : Nat := 425162894777350869192095

theorem tailTrace_931502 : CollatzResearch.WordTrace tailWord_931502 prefixEnd_931502 425162894777350869192095 := by
  unfold tailWord_931502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246833633916852090134595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22649779380889877814051173 4246833633916852090134595)
  ·
    refine ⟨6370250450875278135201893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4246833633916852090134595 6370250450875278135201893)
    ·
      refine ⟨1194421959539114650350355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6370250450875278135201893 1194421959539114650350355)
      ·
        refine ⟨1791632939308671975525533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194421959539114650350355 1791632939308671975525533)
        ·
          refine ⟨671862352240751990822075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1791632939308671975525533 671862352240751990822075)
          ·
            refine ⟨1007793528361127986233113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671862352240751990822075 1007793528361127986233113)
            ·
              refine ⟨755845146270845989674835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007793528361127986233113 755845146270845989674835)
              ·
                refine ⟨1133767719406268984512253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755845146270845989674835 1133767719406268984512253)
                ·
                  refine ⟨425162894777350869192095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133767719406268984512253 425162894777350869192095)
                  ·
                    rfl

theorem cell20_931502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_931502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931502 prefixEnd_931502 := by exact prefixLift 931502
  have htrace : WordTrace (prefixWord ++ tailWord_931502) baseStart_931502 baseEnd_931502 := by
    simpa [prefixWord, tailWord_931502, baseEnd_931502] using wordTrace_append hprefix tailTrace_931502
  have hstable : (prefixWord ++ tailWord_931502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931502).length < 2 ^ (prefixWord ++ tailWord_931502).sum := by decide
  have hdescent : baseEnd_931502 < baseStart_931502 := by decide
  rcases family_descends (prefixWord ++ tailWord_931502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931524 : List Nat := [2, 3, 3, 1, 1, 1, 1, 8]
def baseStart_931524 : Nat := 118140960795 + 931524 * 2 ^ 59
def prefixEnd_931524 : Nat := 4983230072969 + 3 ^ 40 * 931524 * 2
def baseEnd_931524 : Nat := 141724312058938856819557

theorem tailTrace_931524 : CollatzResearch.WordTrace tailWord_931524 prefixEnd_931524 141724312058938856819557 := by
  unfold tailWord_931524
  simp only [CollatzResearch.WordTrace]
  refine ⟨16987735738627557239188813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22650314318170076318918417 16987735738627557239188813)
  ·
    refine ⟨6370400901985333964695805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16987735738627557239188813 6370400901985333964695805)
    ·
      refine ⟨2388900338244500236760927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6370400901985333964695805 2388900338244500236760927)
      ·
        refine ⟨3583350507366750355141391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2388900338244500236760927 3583350507366750355141391)
        ·
          refine ⟨5375025761050125532712087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583350507366750355141391 5375025761050125532712087)
          ·
            refine ⟨8062538641575188299068131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375025761050125532712087 8062538641575188299068131)
            ·
              refine ⟨12093807962362782448602197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8062538641575188299068131 12093807962362782448602197)
              ·
                refine ⟨141724312058938856819557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12093807962362782448602197 141724312058938856819557)
                ·
                  rfl

theorem cell20_931524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_931524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931524 prefixEnd_931524 := by exact prefixLift 931524
  have htrace : WordTrace (prefixWord ++ tailWord_931524) baseStart_931524 baseEnd_931524 := by
    simpa [prefixWord, tailWord_931524, baseEnd_931524] using wordTrace_append hprefix tailTrace_931524
  have hstable : (prefixWord ++ tailWord_931524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931524).length < 2 ^ (prefixWord ++ tailWord_931524).sum := by decide
  have hdescent : baseEnd_931524 < baseStart_931524 := by decide
  rcases family_descends (prefixWord ++ tailWord_931524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931534 : List Nat := [4, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_931534 : Nat := 118140960795 + 931534 * 2 ^ 59
def prefixEnd_931534 : Nat := 4983230072969 + 3 ^ 40 * 931534 * 2
def baseEnd_931534 : Nat := 425177500449300980125297

theorem tailTrace_931534 : CollatzResearch.WordTrace tailWord_931534 prefixEnd_931534 425177500449300980125297 := by
  unfold tailWord_931534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246979525902360773280207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22650557471479257457494437 4246979525902360773280207)
  ·
    refine ⟨6370469288853541159920311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4246979525902360773280207 6370469288853541159920311)
    ·
      refine ⟨9555703933280311739880467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6370469288853541159920311 9555703933280311739880467)
      ·
        refine ⟨14333555899920467609820701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9555703933280311739880467 14333555899920467609820701)
        ·
          refine ⟨5375083462470175353682763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14333555899920467609820701 5375083462470175353682763)
          ·
            refine ⟨8062625193705263030524145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375083462470175353682763 8062625193705263030524145)
            ·
              refine ⟨6046968895278947272893109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8062625193705263030524145 6046968895278947272893109)
              ·
                refine ⟨566903333932401306833729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6046968895278947272893109 566903333932401306833729)
                ·
                  refine ⟨425177500449300980125297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566903333932401306833729 425177500449300980125297)
                  ·
                    rfl

theorem cell20_931534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_931534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931534 prefixEnd_931534 := by exact prefixLift 931534
  have htrace : WordTrace (prefixWord ++ tailWord_931534) baseStart_931534 baseEnd_931534 := by
    simpa [prefixWord, tailWord_931534, baseEnd_931534] using wordTrace_append hprefix tailTrace_931534
  have hstable : (prefixWord ++ tailWord_931534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931534).length < 2 ^ (prefixWord ++ tailWord_931534).sum := by decide
  have hdescent : baseEnd_931534 < baseStart_931534 := by decide
  rcases family_descends (prefixWord ++ tailWord_931534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931545 : List Nat := [1, 2, 1, 2, 3, 11]
def baseStart_931545 : Nat := 118140960795 + 931545 * 2 ^ 59
def prefixEnd_931545 : Nat := 4983230072969 + 3 ^ 40 * 931545 * 2
def baseEnd_931545 : Nat := 15747500783297549287355

theorem tailTrace_931545 : CollatzResearch.WordTrace tailWord_931545 prefixEnd_931545 15747500783297549287355 := by
  unfold tailWord_931545
  simp only [CollatzResearch.WordTrace]
  refine ⟨33976237410179035064892089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22650824940119356709928059 33976237410179035064892089)
  ·
    refine ⟨25482178057634276298669067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33976237410179035064892089 25482178057634276298669067)
    ·
      refine ⟨38223267086451414448003601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25482178057634276298669067 38223267086451414448003601)
      ·
        refine ⟨28667450314838560836002701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38223267086451414448003601 28667450314838560836002701)
        ·
          refine ⟨10750293868064460313501013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28667450314838560836002701 10750293868064460313501013)
          ·
            refine ⟨15747500783297549287355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10750293868064460313501013 15747500783297549287355)
            ·
              rfl

theorem cell20_931545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 11].length) (baseStart_931545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931545 prefixEnd_931545 := by exact prefixLift 931545
  have htrace : WordTrace (prefixWord ++ tailWord_931545) baseStart_931545 baseEnd_931545 := by
    simpa [prefixWord, tailWord_931545, baseEnd_931545] using wordTrace_append hprefix tailTrace_931545
  have hstable : (prefixWord ++ tailWord_931545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931545).length < 2 ^ (prefixWord ++ tailWord_931545).sum := by decide
  have hdescent : baseEnd_931545 < baseStart_931545 := by decide
  rcases family_descends (prefixWord ++ tailWord_931545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931562 : List Nat := [3, 1, 3, 1, 1, 1, 5, 5]
def baseStart_931562 : Nat := 118140960795 + 931562 * 2 ^ 59
def prefixEnd_931562 : Nat := 4983230072969 + 3 ^ 40 * 931562 * 2
def baseEnd_931562 : Nat := 141730093470752442397283

theorem tailTrace_931562 : CollatzResearch.WordTrace tailWord_931562 prefixEnd_931562 141730093470752442397283 := by
  unfold tailWord_931562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494214362779361742065235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22651238300744964645507293 8494214362779361742065235)
  ·
    refine ⟨12741321544169042613097853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8494214362779361742065235 12741321544169042613097853)
    ·
      refine ⟨4777995579063390979911695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12741321544169042613097853 4777995579063390979911695)
      ·
        refine ⟨7166993368595086469867543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4777995579063390979911695 7166993368595086469867543)
        ·
          refine ⟨10750490052892629704801315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7166993368595086469867543 10750490052892629704801315)
          ·
            refine ⟨16125735079338944557201973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10750490052892629704801315 16125735079338944557201973)
            ·
              refine ⟨1511787663688026052237685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16125735079338944557201973 1511787663688026052237685)
              ·
                refine ⟨141730093470752442397283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1511787663688026052237685 141730093470752442397283)
                ·
                  rfl

theorem cell20_931562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_931562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931562 prefixEnd_931562 := by exact prefixLift 931562
  have htrace : WordTrace (prefixWord ++ tailWord_931562) baseStart_931562 baseEnd_931562 := by
    simpa [prefixWord, tailWord_931562, baseEnd_931562] using wordTrace_append hprefix tailTrace_931562
  have hstable : (prefixWord ++ tailWord_931562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931562).length < 2 ^ (prefixWord ++ tailWord_931562).sum := by decide
  have hdescent : baseEnd_931562 < baseStart_931562 := by decide
  rcases family_descends (prefixWord ++ tailWord_931562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931583 : List Nat := [1, 1, 2, 2, 1, 3, 2, 8]
def baseStart_931583 : Nat := 118140960795 + 931583 * 2 ^ 59
def prefixEnd_931583 : Nat := 4983230072969 + 3 ^ 40 * 931583 * 2
def baseEnd_931583 : Nat := 141733288461491529163921

theorem tailTrace_931583 : CollatzResearch.WordTrace tailWord_931583 prefixEnd_931583 141733288461491529163921 := by
  unfold tailWord_931583
  simp only [CollatzResearch.WordTrace]
  refine ⟨33977623384041367554775403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22651748922694245036516935 33977623384041367554775403)
  ·
    refine ⟨50966435076062051332163105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33977623384041367554775403 50966435076062051332163105)
    ·
      refine ⟨38224826307046538499122329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50966435076062051332163105 38224826307046538499122329)
      ·
        refine ⟨28668619730284903874341747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38224826307046538499122329 28668619730284903874341747)
        ·
          refine ⟨43002929595427355811512621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28668619730284903874341747 43002929595427355811512621)
          ·
            refine ⟨16126098598285258429317233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43002929595427355811512621 16126098598285258429317233)
            ·
              refine ⟨12094573948713943821987925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16126098598285258429317233 12094573948713943821987925)
              ·
                refine ⟨141733288461491529163921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12094573948713943821987925 141733288461491529163921)
                ·
                  rfl

theorem cell20_931583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_931583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931583 prefixEnd_931583 := by exact prefixLift 931583
  have htrace : WordTrace (prefixWord ++ tailWord_931583) baseStart_931583 baseEnd_931583 := by
    simpa [prefixWord, tailWord_931583, baseEnd_931583] using wordTrace_append hprefix tailTrace_931583
  have hstable : (prefixWord ++ tailWord_931583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931583).length < 2 ^ (prefixWord ++ tailWord_931583).sum := by decide
  have hdescent : baseEnd_931583 < baseStart_931583 := by decide
  rcases family_descends (prefixWord ++ tailWord_931583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931586 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_931586 : Nat := 118140960795 + 931586 * 2 ^ 59
def prefixEnd_931586 : Nat := 4983230072969 + 3 ^ 40 * 931586 * 2
def baseEnd_931586 : Nat := 425201234666219910391751

theorem tailTrace_931586 : CollatzResearch.WordTrace tailWord_931586 prefixEnd_931586 425201234666219910391751 := by
  unfold tailWord_931586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494433200757624766783653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22651821868686999378089741 8494433200757624766783653)
  ·
    refine ⟨1592706225142054643771935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8494433200757624766783653 1592706225142054643771935)
    ·
      refine ⟨2389059337713081965657903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592706225142054643771935 2389059337713081965657903)
      ·
        refine ⟨3583589006569622948486855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389059337713081965657903 3583589006569622948486855)
        ·
          refine ⟨5375383509854434422730283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583589006569622948486855 5375383509854434422730283)
          ·
            refine ⟨8063075264781651634095425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375383509854434422730283 8063075264781651634095425)
            ·
              refine ⟨6047306448586238725571569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8063075264781651634095425 6047306448586238725571569)
              ·
                refine ⟨4535479836439679044178677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6047306448586238725571569 4535479836439679044178677)
                ·
                  refine ⟨425201234666219910391751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4535479836439679044178677 425201234666219910391751)
                  ·
                    rfl

theorem cell20_931586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_931586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931586 prefixEnd_931586 := by exact prefixLift 931586
  have htrace : WordTrace (prefixWord ++ tailWord_931586) baseStart_931586 baseEnd_931586 := by
    simpa [prefixWord, tailWord_931586, baseEnd_931586] using wordTrace_append hprefix tailTrace_931586
  have hstable : (prefixWord ++ tailWord_931586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931586).length < 2 ^ (prefixWord ++ tailWord_931586).sum := by decide
  have hdescent : baseEnd_931586 < baseStart_931586 := by decide
  rcases family_descends (prefixWord ++ tailWord_931586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931610 : List Nat := [3, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_931610 : Nat := 118140960795 + 931610 * 2 ^ 59
def prefixEnd_931610 : Nat := 4983230072969 + 3 ^ 40 * 931610 * 2
def baseEnd_931610 : Nat := 425212188920182493591653

theorem tailTrace_931610 : CollatzResearch.WordTrace tailWord_931610 prefixEnd_931610 425212188920182493591653 := by
  unfold tailWord_931610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494652038735887791502071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22652405436629034110672189 8494652038735887791502071)
  ·
    refine ⟨12741978058103831687253107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8494652038735887791502071 12741978058103831687253107)
    ·
      refine ⟨19112967087155747530879661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12741978058103831687253107 19112967087155747530879661)
      ·
        refine ⟨7167362657683405324079873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19112967087155747530879661 7167362657683405324079873)
        ·
          refine ⟨5375521993262553993059905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7167362657683405324079873 5375521993262553993059905)
          ·
            refine ⟨4031641494946915494794929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5375521993262553993059905 4031641494946915494794929)
            ·
              refine ⟨3023731121210186621096197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4031641494946915494794929 3023731121210186621096197)
              ·
                refine ⟨566949585226909991455537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3023731121210186621096197 566949585226909991455537)
                ·
                  refine ⟨425212188920182493591653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566949585226909991455537 425212188920182493591653)
                  ·
                    rfl

theorem cell20_931610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_931610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931610 prefixEnd_931610 := by exact prefixLift 931610
  have htrace : WordTrace (prefixWord ++ tailWord_931610) baseStart_931610 baseEnd_931610 := by
    simpa [prefixWord, tailWord_931610, baseEnd_931610] using wordTrace_append hprefix tailTrace_931610
  have hstable : (prefixWord ++ tailWord_931610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931610).length < 2 ^ (prefixWord ++ tailWord_931610).sum := by decide
  have hdescent : baseEnd_931610 < baseStart_931610 := by decide
  rcases family_descends (prefixWord ++ tailWord_931610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931665 : List Nat := [1, 2, 2, 1, 5, 2, 3, 2, 2]
def baseStart_931665 : Nat := 118140960795 + 931665 * 2 ^ 59
def prefixEnd_931665 : Nat := 4983230072969 + 3 ^ 40 * 931665 * 2
def baseEnd_931665 : Nat := 425237292418846746758095

theorem tailTrace_931665 : CollatzResearch.WordTrace tailWord_931665 prefixEnd_931665 425237292418846746758095 := by
  unfold tailWord_931665
  simp only [CollatzResearch.WordTrace]
  refine ⟨33980614169744295559260449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22653742779829530372840299 33980614169744295559260449)
  ·
    refine ⟨25485460627308221669445337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33980614169744295559260449 25485460627308221669445337)
    ·
      refine ⟨19114095470481166252084003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25485460627308221669445337 19114095470481166252084003)
      ·
        refine ⟨28671143205721749378126005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19114095470481166252084003 28671143205721749378126005)
        ·
          refine ⟨2687919675536414004199313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28671143205721749378126005 2687919675536414004199313)
          ·
            refine ⟨2015939756652310503149485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2687919675536414004199313 2015939756652310503149485)
            ·
              refine ⟨755977408744616438681057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2015939756652310503149485 755977408744616438681057)
              ·
                refine ⟨566983056558462329010793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755977408744616438681057 566983056558462329010793)
                ·
                  refine ⟨425237292418846746758095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566983056558462329010793 425237292418846746758095)
                  ·
                    rfl

theorem cell20_931665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_931665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931665 prefixEnd_931665 := by exact prefixLift 931665
  have htrace : WordTrace (prefixWord ++ tailWord_931665) baseStart_931665 baseEnd_931665 := by
    simpa [prefixWord, tailWord_931665, baseEnd_931665] using wordTrace_append hprefix tailTrace_931665
  have hstable : (prefixWord ++ tailWord_931665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931665).length < 2 ^ (prefixWord ++ tailWord_931665).sum := by decide
  have hdescent : baseEnd_931665 < baseStart_931665 := by decide
  rcases family_descends (prefixWord ++ tailWord_931665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931669 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_931669 : Nat := 118140960795 + 931669 * 2 ^ 59
def prefixEnd_931669 : Nat := 4983230072969 + 3 ^ 40 * 931669 * 2
def baseEnd_931669 : Nat := 425239118127840510624745

theorem tailTrace_931669 : CollatzResearch.WordTrace tailWord_931669 prefixEnd_931669 425239118127840510624745 := by
  unfold tailWord_931669
  simp only [CollatzResearch.WordTrace]
  refine ⟨33980760061729804242406061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22653840041153202828270707 33980760061729804242406061)
  ·
    refine ⟨12742785023148676590902273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33980760061729804242406061 12742785023148676590902273)
    ·
      refine ⟨9557088767361507443176705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12742785023148676590902273 9557088767361507443176705)
      ·
        refine ⟨7167816575521130582382529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9557088767361507443176705 7167816575521130582382529)
        ·
          refine ⟨5375862431640847936786897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7167816575521130582382529 5375862431640847936786897)
          ·
            refine ⟨4031896823730635952590173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5375862431640847936786897 4031896823730635952590173)
            ·
              refine ⟨1511961308898988482221315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4031896823730635952590173 1511961308898988482221315)
              ·
                refine ⟨2267941963348482723331973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511961308898988482221315 2267941963348482723331973)
                ·
                  refine ⟨425239118127840510624745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2267941963348482723331973 425239118127840510624745)
                  ·
                    rfl

theorem cell20_931669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_931669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931669 prefixEnd_931669 := by exact prefixLift 931669
  have htrace : WordTrace (prefixWord ++ tailWord_931669) baseStart_931669 baseEnd_931669 := by
    simpa [prefixWord, tailWord_931669, baseEnd_931669] using wordTrace_append hprefix tailTrace_931669
  have hstable : (prefixWord ++ tailWord_931669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931669).length < 2 ^ (prefixWord ++ tailWord_931669).sum := by decide
  have hdescent : baseEnd_931669 < baseStart_931669 := by decide
  rcases family_descends (prefixWord ++ tailWord_931669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931679 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 3]
def baseStart_931679 : Nat := 118140960795 + 931679 * 2 ^ 59
def prefixEnd_931679 : Nat := 4983230072969 + 3 ^ 40 * 931679 * 2
def baseEnd_931679 : Nat := 425243682400324920291371

theorem tailTrace_931679 : CollatzResearch.WordTrace tailWord_931679 prefixEnd_931679 425243682400324920291371 := by
  unfold tailWord_931679
  simp only [CollatzResearch.WordTrace]
  refine ⟨33981124791693575950270091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22654083194462383966846727 33981124791693575950270091)
  ·
    refine ⟨50971687187540363925405137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33981124791693575950270091 50971687187540363925405137)
    ·
      refine ⟨38228765390655272944053853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50971687187540363925405137 38228765390655272944053853)
      ·
        refine ⟨14335787021495727354020195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38228765390655272944053853 14335787021495727354020195)
        ·
          refine ⟨21503680532243591031030293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14335787021495727354020195 21503680532243591031030293)
          ·
            refine ⟨1007985024948918329579545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21503680532243591031030293 1007985024948918329579545)
            ·
              refine ⟨755988768711688747184659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007985024948918329579545 755988768711688747184659)
              ·
                refine ⟨1133983153067533120776989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755988768711688747184659 1133983153067533120776989)
                ·
                  refine ⟨425243682400324920291371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133983153067533120776989 425243682400324920291371)
                  ·
                    rfl

theorem cell20_931679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 3].length) (baseStart_931679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931679 prefixEnd_931679 := by exact prefixLift 931679
  have htrace : WordTrace (prefixWord ++ tailWord_931679) baseStart_931679 baseEnd_931679 := by
    simpa [prefixWord, tailWord_931679, baseEnd_931679] using wordTrace_append hprefix tailTrace_931679
  have hstable : (prefixWord ++ tailWord_931679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931679).length < 2 ^ (prefixWord ++ tailWord_931679).sum := by decide
  have hdescent : baseEnd_931679 < baseStart_931679 := by decide
  rcases family_descends (prefixWord ++ tailWord_931679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931697 : List Nat := [1, 2, 2, 2, 1, 3, 1, 8]
def baseStart_931697 : Nat := 118140960795 + 931697 * 2 ^ 59
def prefixEnd_931697 : Nat := 4983230072969 + 3 ^ 40 * 931697 * 2
def baseEnd_931697 : Nat := 141750632696932285897099

theorem tailTrace_931697 : CollatzResearch.WordTrace tailWord_931697 prefixEnd_931697 141750632696932285897099 := by
  unfold tailWord_931697
  simp only [CollatzResearch.WordTrace]
  refine ⟨33981781305628365024425345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22654520870418910016283563 33981781305628365024425345)
  ·
    refine ⟨25486335979221273768319009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33981781305628365024425345 25486335979221273768319009)
    ·
      refine ⟨19114751984415955326239257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25486335979221273768319009 19114751984415955326239257)
      ·
        refine ⟨14336063988311966494679443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19114751984415955326239257 14336063988311966494679443)
        ·
          refine ⟨21504095982467949742019165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14336063988311966494679443 21504095982467949742019165)
          ·
            refine ⟨8064035993425481153257187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21504095982467949742019165 8064035993425481153257187)
            ·
              refine ⟨12096053990138221729885781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8064035993425481153257187 12096053990138221729885781)
              ·
                refine ⟨141750632696932285897099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12096053990138221729885781 141750632696932285897099)
                ·
                  rfl

theorem cell20_931697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_931697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931697 prefixEnd_931697 := by exact prefixLift 931697
  have htrace : WordTrace (prefixWord ++ tailWord_931697) baseStart_931697 baseEnd_931697 := by
    simpa [prefixWord, tailWord_931697, baseEnd_931697] using wordTrace_append hprefix tailTrace_931697
  have hstable : (prefixWord ++ tailWord_931697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931697).length < 2 ^ (prefixWord ++ tailWord_931697).sum := by decide
  have hdescent : baseEnd_931697 < baseStart_931697 := by decide
  rcases family_descends (prefixWord ++ tailWord_931697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931707 : List Nat := [1, 1, 1, 1, 1, 5, 1, 7, 2]
def baseStart_931707 : Nat := 118140960795 + 931707 * 2 ^ 59
def prefixEnd_931707 : Nat := 4983230072969 + 3 ^ 40 * 931707 * 2
def baseEnd_931707 : Nat := 425256462363281267357923

theorem tailTrace_931707 : CollatzResearch.WordTrace tailWord_931707 prefixEnd_931707 425256462363281267357923 := by
  unfold tailWord_931707
  simp only [CollatzResearch.WordTrace]
  refine ⟨33982146035592136732289375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22654764023728091154859583 33982146035592136732289375)
  ·
    refine ⟨50973219053388205098434063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33982146035592136732289375 50973219053388205098434063)
    ·
      refine ⟨76459828580082307647651095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50973219053388205098434063 76459828580082307647651095)
      ·
        refine ⟨114689742870123461471476643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76459828580082307647651095 114689742870123461471476643)
        ·
          refine ⟨172034614305185192207214965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114689742870123461471476643 172034614305185192207214965)
          ·
            refine ⟨16128245091111111769426403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172034614305185192207214965 16128245091111111769426403)
            ·
              refine ⟨24192367636666667654139605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16128245091111111769426403 24192367636666667654139605)
              ·
                refine ⟨567008616484375023143897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24192367636666667654139605 567008616484375023143897)
                ·
                  refine ⟨425256462363281267357923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567008616484375023143897 425256462363281267357923)
                  ·
                    rfl

theorem cell20_931707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 2].length) (baseStart_931707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931707 prefixEnd_931707 := by exact prefixLift 931707
  have htrace : WordTrace (prefixWord ++ tailWord_931707) baseStart_931707 baseEnd_931707 := by
    simpa [prefixWord, tailWord_931707, baseEnd_931707] using wordTrace_append hprefix tailTrace_931707
  have hstable : (prefixWord ++ tailWord_931707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931707).length < 2 ^ (prefixWord ++ tailWord_931707).sum := by decide
  have hdescent : baseEnd_931707 < baseStart_931707 := by decide
  rcases family_descends (prefixWord ++ tailWord_931707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931714 : List Nat := [3, 4, 2, 11]
def baseStart_931714 : Nat := 118140960795 + 931714 * 2 ^ 59
def prefixEnd_931714 : Nat := 4983230072969 + 3 ^ 40 * 931714 * 2
def baseEnd_931714 : Nat := 1750039742197614626027

theorem tailTrace_931714 : CollatzResearch.WordTrace tailWord_931714 prefixEnd_931714 1750039742197614626027 := by
  unfold tailWord_931714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8495600336641694231948549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22654934231044517951862797 8495600336641694231948549)
  ·
    refine ⟨1592925063120317668490353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8495600336641694231948549 1592925063120317668490353)
    ·
      refine ⟨1194693797340238251367765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1592925063120317668490353 1194693797340238251367765)
      ·
        refine ⟨1750039742197614626027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1194693797340238251367765 1750039742197614626027)
        ·
          rfl

theorem cell20_931714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 11].length) (baseStart_931714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931714 prefixEnd_931714 := by exact prefixLift 931714
  have htrace : WordTrace (prefixWord ++ tailWord_931714) baseStart_931714 baseEnd_931714 := by
    simpa [prefixWord, tailWord_931714, baseEnd_931714] using wordTrace_append hprefix tailTrace_931714
  have hstable : (prefixWord ++ tailWord_931714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931714).length < 2 ^ (prefixWord ++ tailWord_931714).sum := by decide
  have hdescent : baseEnd_931714 < baseStart_931714 := by decide
  rcases family_descends (prefixWord ++ tailWord_931714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931720 : List Nat := [2, 1, 3, 3, 3, 2, 2, 2, 2]
def baseStart_931720 : Nat := 118140960795 + 931720 * 2 ^ 59
def prefixEnd_931720 : Nat := 4983230072969 + 3 ^ 40 * 931720 * 2
def baseEnd_931720 : Nat := 425262395917510999924537

theorem tailTrace_931720 : CollatzResearch.WordTrace tailWord_931720 prefixEnd_931720 425262395917510999924537 := by
  unfold tailWord_931720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16991310092272519976256307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22655080123030026635008409 16991310092272519976256307)
  ·
    refine ⟨25486965138408779964384461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16991310092272519976256307 25486965138408779964384461)
    ·
      refine ⟨9557611926903292486644173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25486965138408779964384461 9557611926903292486644173)
      ·
        refine ⟨3584104472588734682491565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9557611926903292486644173 3584104472588734682491565)
        ·
          refine ⟨1344039177220775505934337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3584104472588734682491565 1344039177220775505934337)
          ·
            refine ⟨1008029382915581629450753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344039177220775505934337 1008029382915581629450753)
            ·
              refine ⟨756022037186686222088065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008029382915581629450753 756022037186686222088065)
              ·
                refine ⟨567016527890014666566049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756022037186686222088065 567016527890014666566049)
                ·
                  refine ⟨425262395917510999924537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567016527890014666566049 425262395917510999924537)
                  ·
                    rfl

theorem cell20_931720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_931720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931720 prefixEnd_931720 := by exact prefixLift 931720
  have htrace : WordTrace (prefixWord ++ tailWord_931720) baseStart_931720 baseEnd_931720 := by
    simpa [prefixWord, tailWord_931720, baseEnd_931720] using wordTrace_append hprefix tailTrace_931720
  have hstable : (prefixWord ++ tailWord_931720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931720).length < 2 ^ (prefixWord ++ tailWord_931720).sum := by decide
  have hdescent : baseEnd_931720 < baseStart_931720 := by decide
  rcases family_descends (prefixWord ++ tailWord_931720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931738 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_931738 : Nat := 118140960795 + 931738 * 2 ^ 59
def prefixEnd_931738 : Nat := 4983230072969 + 3 ^ 40 * 931738 * 2
def baseEnd_931738 : Nat := 425270611607982937324463

theorem tailTrace_931738 : CollatzResearch.WordTrace tailWord_931738 prefixEnd_931738 425270611607982937324463 := by
  unfold tailWord_931738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8495819174619957256666967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22655517798986552684445245 8495819174619957256666967)
  ·
    refine ⟨12743728761929935885000451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8495819174619957256666967 12743728761929935885000451)
    ·
      refine ⟨19115593142894903827500677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12743728761929935885000451 19115593142894903827500677)
      ·
        refine ⟨3584173714292794467656377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19115593142894903827500677 3584173714292794467656377)
        ·
          refine ⟨2688130285719595850742283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3584173714292794467656377 2688130285719595850742283)
          ·
            refine ⟨4032195428579393776113425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688130285719595850742283 4032195428579393776113425)
            ·
              refine ⟨3024146571434545332085069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4032195428579393776113425 3024146571434545332085069)
              ·
                refine ⟨1134054964287954499531901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3024146571434545332085069 1134054964287954499531901)
                ·
                  refine ⟨425270611607982937324463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134054964287954499531901 425270611607982937324463)
                  ·
                    rfl

theorem cell20_931738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_931738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931738 prefixEnd_931738 := by exact prefixLift 931738
  have htrace : WordTrace (prefixWord ++ tailWord_931738) baseStart_931738 baseEnd_931738 := by
    simpa [prefixWord, tailWord_931738, baseEnd_931738] using wordTrace_append hprefix tailTrace_931738
  have hstable : (prefixWord ++ tailWord_931738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931738).length < 2 ^ (prefixWord ++ tailWord_931738).sum := by decide
  have hdescent : baseEnd_931738 < baseStart_931738 := by decide
  rcases family_descends (prefixWord ++ tailWord_931738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931772 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 3]
def baseStart_931772 : Nat := 118140960795 + 931772 * 2 ^ 59
def prefixEnd_931772 : Nat := 4983230072969 + 3 ^ 40 * 931772 * 2
def baseEnd_931772 : Nat := 425286130134429930190991

theorem tailTrace_931772 : CollatzResearch.WordTrace tailWord_931772 prefixEnd_931772 425286130134429930190991 := by
  unfold tailWord_931772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16992258390178326416702785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22656344520237768555603713 16992258390178326416702785)
  ·
    refine ⟨12744193792633744812527089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16992258390178326416702785 12744193792633744812527089)
    ·
      refine ⟨9558145344475308609395317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12744193792633744812527089 9558145344475308609395317)
      ·
        refine ⟨896076126044560182130811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9558145344475308609395317 896076126044560182130811)
        ·
          refine ⟨1344114189066840273196217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896076126044560182130811 1344114189066840273196217)
          ·
            refine ⟨1008085641800130204897163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344114189066840273196217 1008085641800130204897163)
            ·
              refine ⟨1512128462700195307345745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008085641800130204897163 1512128462700195307345745)
              ·
                refine ⟨1134096347025146480509309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512128462700195307345745 1134096347025146480509309)
                ·
                  refine ⟨425286130134429930190991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134096347025146480509309 425286130134429930190991)
                  ·
                    rfl

theorem cell20_931772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_931772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931772 prefixEnd_931772 := by exact prefixLift 931772
  have htrace : WordTrace (prefixWord ++ tailWord_931772) baseStart_931772 baseEnd_931772 := by
    simpa [prefixWord, tailWord_931772, baseEnd_931772] using wordTrace_append hprefix tailTrace_931772
  have hstable : (prefixWord ++ tailWord_931772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931772).length < 2 ^ (prefixWord ++ tailWord_931772).sum := by decide
  have hdescent : baseEnd_931772 < baseStart_931772 := by decide
  rcases family_descends (prefixWord ++ tailWord_931772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931807 : List Nat := [1, 1, 2, 3, 4, 3, 2, 4]
def baseStart_931807 : Nat := 118140960795 + 931807 * 2 ^ 59
def prefixEnd_931807 : Nat := 4983230072969 + 3 ^ 40 * 931807 * 2
def baseEnd_931807 : Nat := 141767368362708454674727

theorem tailTrace_931807 : CollatzResearch.WordTrace tailWord_931807 prefixEnd_931807 141767368362708454674727 := by
  unfold tailWord_931807
  simp only [CollatzResearch.WordTrace]
  refine ⟨33985793335229853810929675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22657195556819902540619783 33985793335229853810929675)
  ·
    refine ⟨50978690002844780716394513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33985793335229853810929675 50978690002844780716394513)
    ·
      refine ⟨38234017502133585537295885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50978690002844780716394513 38234017502133585537295885)
      ·
        refine ⟨14337756563300094576485957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38234017502133585537295885 14337756563300094576485957)
        ·
          refine ⟨2688329355618767733091117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14337756563300094576485957 2688329355618767733091117)
          ·
            refine ⟨1008123508357037899909169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2688329355618767733091117 1008123508357037899909169)
            ·
              refine ⟨756092631267778424931877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008123508357037899909169 756092631267778424931877)
              ·
                refine ⟨141767368362708454674727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 756092631267778424931877 141767368362708454674727)
                ·
                  rfl

theorem cell20_931807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 4].length) (baseStart_931807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931807 prefixEnd_931807 := by exact prefixLift 931807
  have htrace : WordTrace (prefixWord ++ tailWord_931807) baseStart_931807 baseEnd_931807 := by
    simpa [prefixWord, tailWord_931807, baseEnd_931807] using wordTrace_append hprefix tailTrace_931807
  have hstable : (prefixWord ++ tailWord_931807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931807).length < 2 ^ (prefixWord ++ tailWord_931807).sum := by decide
  have hdescent : baseEnd_931807 < baseStart_931807 := by decide
  rcases family_descends (prefixWord ++ tailWord_931807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931838 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_931838 : Nat := 118140960795 + 931838 * 2 ^ 59
def prefixEnd_931838 : Nat := 4983230072969 + 3 ^ 40 * 931838 * 2
def baseEnd_931838 : Nat := 425316254332827033990721

theorem tailTrace_931838 : CollatzResearch.WordTrace tailWord_931838 prefixEnd_931838 425316254332827033990721 := by
  unfold tailWord_931838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248365499764693263163521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22657949332078364070205445 4248365499764693263163521)
  ·
    refine ⟨3186274124823519947372641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4248365499764693263163521 3186274124823519947372641)
    ·
      refine ⟨2389705593617639960529481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3186274124823519947372641 2389705593617639960529481)
      ·
        refine ⟨1792279195213229970397111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2389705593617639960529481 1792279195213229970397111)
        ·
          refine ⟨2688418792819844955595667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1792279195213229970397111 2688418792819844955595667)
          ·
            refine ⟨4032628189229767433393501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688418792819844955595667 4032628189229767433393501)
            ·
              refine ⟨1512235570961162787522563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4032628189229767433393501 1512235570961162787522563)
              ·
                refine ⟨2268353356441744181283845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512235570961162787522563 2268353356441744181283845)
                ·
                  refine ⟨425316254332827033990721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2268353356441744181283845 425316254332827033990721)
                  ·
                    rfl

theorem cell20_931838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_931838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931838 prefixEnd_931838 := by exact prefixLift 931838
  have htrace : WordTrace (prefixWord ++ tailWord_931838) baseStart_931838 baseEnd_931838 := by
    simpa [prefixWord, tailWord_931838, baseEnd_931838] using wordTrace_append hprefix tailTrace_931838
  have hstable : (prefixWord ++ tailWord_931838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931838).length < 2 ^ (prefixWord ++ tailWord_931838).sum := by decide
  have hdescent : baseEnd_931838 < baseStart_931838 := by decide
  rcases family_descends (prefixWord ++ tailWord_931838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931890 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_931890 : Nat := 118140960795 + 931890 * 2 ^ 59
def prefixEnd_931890 : Nat := 4983230072969 + 3 ^ 40 * 931890 * 2
def baseEnd_931890 : Nat := 425339988549745964257175

theorem tailTrace_931890 : CollatzResearch.WordTrace tailWord_931890 prefixEnd_931890 425339988549745964257175 := by
  unfold tailWord_931890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8497205148482289746550281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22659213729286105990800749 8497205148482289746550281)
  ·
    refine ⟨6372903861361717309912711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8497205148482289746550281 6372903861361717309912711)
    ·
      refine ⟨9559355792042575964869067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6372903861361717309912711 9559355792042575964869067)
      ·
        refine ⟨14339033688063863947303601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9559355792042575964869067 14339033688063863947303601)
        ·
          refine ⟨10754275266047897960477701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14339033688063863947303601 10754275266047897960477701)
          ·
            refine ⟨2016426612383980867589569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10754275266047897960477701 2016426612383980867589569)
            ·
              refine ⟨1512319959287985650692177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016426612383980867589569 1512319959287985650692177)
              ·
                refine ⟨1134239969465989238019133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512319959287985650692177 1134239969465989238019133)
                ·
                  refine ⟨425339988549745964257175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134239969465989238019133 425339988549745964257175)
                  ·
                    rfl

theorem cell20_931890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_931890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931890 prefixEnd_931890 := by exact prefixLift 931890
  have htrace : WordTrace (prefixWord ++ tailWord_931890) baseStart_931890 baseEnd_931890 := by
    simpa [prefixWord, tailWord_931890, baseEnd_931890] using wordTrace_append hprefix tailTrace_931890
  have hstable : (prefixWord ++ tailWord_931890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931890).length < 2 ^ (prefixWord ++ tailWord_931890).sum := by decide
  have hdescent : baseEnd_931890 < baseStart_931890 := by decide
  rcases family_descends (prefixWord ++ tailWord_931890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931904 : List Nat := [2, 1, 1, 2, 2, 6, 1, 5]
def baseStart_931904 : Nat := 118140960795 + 931904 * 2 ^ 59
def prefixEnd_931904 : Nat := 4983230072969 + 3 ^ 40 * 931904 * 2
def baseEnd_931904 : Nat := 141782126177074712596817

theorem tailTrace_931904 : CollatzResearch.WordTrace tailWord_931904 prefixEnd_931904 141782126177074712596817 := by
  unfold tailWord_931904
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994665607939219688605383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22659554143918959584807177 16994665607939219688605383)
  ·
    refine ⟨25491998411908829532908075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16994665607939219688605383 25491998411908829532908075)
    ·
      refine ⟨38237997617863244299362113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25491998411908829532908075 38237997617863244299362113)
      ·
        refine ⟨28678498213397433224521585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38237997617863244299362113 28678498213397433224521585)
        ·
          refine ⟨21508873660048074918391189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28678498213397433224521585 21508873660048074918391189)
          ·
            refine ⟨1008228452814753511799587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21508873660048074918391189 1008228452814753511799587)
            ·
              refine ⟨1512342679222130267699381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008228452814753511799587 1512342679222130267699381)
              ·
                refine ⟨141782126177074712596817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1512342679222130267699381 141782126177074712596817)
                ·
                  rfl

theorem cell20_931904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_931904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931904 prefixEnd_931904 := by exact prefixLift 931904
  have htrace : WordTrace (prefixWord ++ tailWord_931904) baseStart_931904 baseEnd_931904 := by
    simpa [prefixWord, tailWord_931904, baseEnd_931904] using wordTrace_append hprefix tailTrace_931904
  have hstable : (prefixWord ++ tailWord_931904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931904).length < 2 ^ (prefixWord ++ tailWord_931904).sum := by decide
  have hdescent : baseEnd_931904 < baseStart_931904 := by decide
  rcases family_descends (prefixWord ++ tailWord_931904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931911 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 3]
def baseStart_931911 : Nat := 118140960795 + 931911 * 2 ^ 59
def prefixEnd_931911 : Nat := 4983230072969 + 3 ^ 40 * 931911 * 2
def baseEnd_931911 : Nat := 425349573521963224557089

theorem tailTrace_931911 : CollatzResearch.WordTrace tailWord_931911 prefixEnd_931911 425349573521963224557089 := by
  unfold tailWord_931911
  simp only [CollatzResearch.WordTrace]
  refine ⟨33989586526853079572715587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22659724351235386381810391 33989586526853079572715587)
  ·
    refine ⟨50984379790279619359073381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33989586526853079572715587 50984379790279619359073381)
    ·
      refine ⟨9559571210677428629826259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50984379790279619359073381 9559571210677428629826259)
      ·
        refine ⟨14339356816016142944739389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9559571210677428629826259 14339356816016142944739389)
        ·
          refine ⟨5377258806006053604277271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14339356816016142944739389 5377258806006053604277271)
          ·
            refine ⟨8065888209009080406415907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5377258806006053604277271 8065888209009080406415907)
            ·
              refine ⟨12098832313513620609623861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065888209009080406415907 12098832313513620609623861)
              ·
                refine ⟨1134265529391901932152237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12098832313513620609623861 1134265529391901932152237)
                ·
                  refine ⟨425349573521963224557089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134265529391901932152237 425349573521963224557089)
                  ·
                    rfl

theorem cell20_931911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_931911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931911 prefixEnd_931911 := by exact prefixLift 931911
  have htrace : WordTrace (prefixWord ++ tailWord_931911) baseStart_931911 baseEnd_931911 := by
    simpa [prefixWord, tailWord_931911, baseEnd_931911] using wordTrace_append hprefix tailTrace_931911
  have hstable : (prefixWord ++ tailWord_931911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931911).length < 2 ^ (prefixWord ++ tailWord_931911).sum := by decide
  have hdescent : baseEnd_931911 < baseStart_931911 := by decide
  rcases family_descends (prefixWord ++ tailWord_931911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931918 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_931918 : Nat := 118140960795 + 931918 * 2 ^ 59
def prefixEnd_931918 : Nat := 4983230072969 + 3 ^ 40 * 931918 * 2
def baseEnd_931918 : Nat := 425352768512702311323727

theorem tailTrace_931918 : CollatzResearch.WordTrace tailWord_931918 prefixEnd_931918 425352768512702311323727 := by
  unfold tailWord_931918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248730229728464971027551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22659894558551813178813605 4248730229728464971027551)
  ·
    refine ⟨6373095344592697456541327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4248730229728464971027551 6373095344592697456541327)
    ·
      refine ⟨9559643016889046184811991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6373095344592697456541327 9559643016889046184811991)
      ·
        refine ⟨14339464525333569277217987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9559643016889046184811991 14339464525333569277217987)
        ·
          refine ⟨21509196788000353915826981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14339464525333569277217987 21509196788000353915826981)
          ·
            refine ⟨4032974397750066359217559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21509196788000353915826981 4032974397750066359217559)
            ·
              refine ⟨6049461596625099538826339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032974397750066359217559 6049461596625099538826339)
              ·
                refine ⟨9074192394937649308239509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049461596625099538826339 9074192394937649308239509)
                ·
                  refine ⟨425352768512702311323727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9074192394937649308239509 425352768512702311323727)
                  ·
                    rfl

theorem cell20_931918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_931918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931918 prefixEnd_931918 := by exact prefixLift 931918
  have htrace : WordTrace (prefixWord ++ tailWord_931918) baseStart_931918 baseEnd_931918 := by
    simpa [prefixWord, tailWord_931918, baseEnd_931918] using wordTrace_append hprefix tailTrace_931918
  have hstable : (prefixWord ++ tailWord_931918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931918).length < 2 ^ (prefixWord ++ tailWord_931918).sum := by decide
  have hdescent : baseEnd_931918 < baseStart_931918 := by decide
  rcases family_descends (prefixWord ++ tailWord_931918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931949 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_931949 : Nat := 118140960795 + 931949 * 2 ^ 59
def prefixEnd_931949 : Nat := 4983230072969 + 3 ^ 40 * 931949 * 2
def baseEnd_931949 : Nat := 425366917757403981290267

theorem tailTrace_931949 : CollatzResearch.WordTrace tailWord_931949 prefixEnd_931949 425366917757403981290267 := by
  unfold tailWord_931949
  simp only [CollatzResearch.WordTrace]
  refine ⟨33990972500715412062598901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22660648333810274708399267 33990972500715412062598901)
  ·
    refine ⟨3186653671942069880868647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33990972500715412062598901 3186653671942069880868647)
    ·
      refine ⟨4779980507913104821302971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3186653671942069880868647 4779980507913104821302971)
      ·
        refine ⟨7169970761869657231954457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779980507913104821302971 7169970761869657231954457)
        ·
          refine ⟨5377478071402242923965843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7169970761869657231954457 5377478071402242923965843)
          ·
            refine ⟨8066217107103364385948765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5377478071402242923965843 8066217107103364385948765)
            ·
              refine ⟨3024831415163761644730787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8066217107103364385948765 3024831415163761644730787)
              ·
                refine ⟨4537247122745642467096181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024831415163761644730787 4537247122745642467096181)
                ·
                  refine ⟨425366917757403981290267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4537247122745642467096181 425366917757403981290267)
                  ·
                    rfl

theorem cell20_931949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_931949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_931949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_931949 prefixEnd_931949 := by exact prefixLift 931949
  have htrace : WordTrace (prefixWord ++ tailWord_931949) baseStart_931949 baseEnd_931949 := by
    simpa [prefixWord, tailWord_931949, baseEnd_931949] using wordTrace_append hprefix tailTrace_931949
  have hstable : (prefixWord ++ tailWord_931949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931949).length < 2 ^ (prefixWord ++ tailWord_931949).sum := by decide
  have hdescent : baseEnd_931949 < baseStart_931949 := by decide
  rcases family_descends (prefixWord ++ tailWord_931949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932001 : List Nat := [1, 2, 3, 3, 1, 2, 8]
def baseStart_932001 : Nat := 118140960795 + 932001 * 2 ^ 59
def prefixEnd_932001 : Nat := 4983230072969 + 3 ^ 40 * 932001 * 2
def baseEnd_932001 : Nat := 47265627997146990172969

theorem tailTrace_932001 : CollatzResearch.WordTrace tailWord_932001 prefixEnd_932001 47265627997146990172969 := by
  unfold tailWord_932001
  simp only [CollatzResearch.WordTrace]
  refine ⟨33992869096527024943491857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22661912731018016628994571 33992869096527024943491857)
  ·
    refine ⟨25494651822395268707618893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33992869096527024943491857 25494651822395268707618893)
    ·
      refine ⟨9560494433398225765357085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25494651822395268707618893 9560494433398225765357085)
      ·
        refine ⟨3585185412524334662008907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9560494433398225765357085 3585185412524334662008907)
        ·
          refine ⟨5377778118786501993013361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585185412524334662008907 5377778118786501993013361)
          ·
            refine ⟨4033333589089876494760021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5377778118786501993013361 4033333589089876494760021)
            ·
              refine ⟨47265627997146990172969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4033333589089876494760021 47265627997146990172969)
              ·
                rfl

theorem cell20_932001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 8].length) (baseStart_932001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932001 prefixEnd_932001 := by exact prefixLift 932001
  have htrace : WordTrace (prefixWord ++ tailWord_932001) baseStart_932001 baseEnd_932001 := by
    simpa [prefixWord, tailWord_932001, baseEnd_932001] using wordTrace_append hprefix tailTrace_932001
  have hstable : (prefixWord ++ tailWord_932001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932001).length < 2 ^ (prefixWord ++ tailWord_932001).sum := by decide
  have hdescent : baseEnd_932001 < baseStart_932001 := by decide
  rcases family_descends (prefixWord ++ tailWord_932001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932007 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 4]
def baseStart_932007 : Nat := 118140960795 + 932007 * 2 ^ 59
def prefixEnd_932007 : Nat := 4983230072969 + 3 ^ 40 * 932007 * 2
def baseEnd_932007 : Nat := 425393390537813557356697

theorem tailTrace_932007 : CollatzResearch.WordTrace tailWord_932007 prefixEnd_932007 425393390537813557356697 := by
  unfold tailWord_932007
  simp only [CollatzResearch.WordTrace]
  refine ⟨33993087934505287968210275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22662058623003525312140183 33993087934505287968210275)
  ·
    refine ⟨50989631901757931952315413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33993087934505287968210275 50989631901757931952315413)
    ·
      refine ⟨2390138995394903060264785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50989631901757931952315413 2390138995394903060264785)
      ·
        refine ⟨1792604246546177295198589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2390138995394903060264785 1792604246546177295198589)
        ·
          refine ⟨672226592454816485699471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1792604246546177295198589 672226592454816485699471)
          ·
            refine ⟨1008339888682224728549207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672226592454816485699471 1008339888682224728549207)
            ·
              refine ⟨1512509833023337092823811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008339888682224728549207 1512509833023337092823811)
              ·
                refine ⟨2268764749535005639235717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512509833023337092823811 2268764749535005639235717)
                ·
                  refine ⟨425393390537813557356697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2268764749535005639235717 425393390537813557356697)
                  ·
                    rfl

theorem cell20_932007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 4].length) (baseStart_932007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932007 prefixEnd_932007 := by exact prefixLift 932007
  have htrace : WordTrace (prefixWord ++ tailWord_932007) baseStart_932007 baseEnd_932007 := by
    simpa [prefixWord, tailWord_932007, baseEnd_932007] using wordTrace_append hprefix tailTrace_932007
  have hstable : (prefixWord ++ tailWord_932007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932007).length < 2 ^ (prefixWord ++ tailWord_932007).sum := by decide
  have hdescent : baseEnd_932007 < baseStart_932007 := by decide
  rcases family_descends (prefixWord ++ tailWord_932007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932014 : List Nat := [4, 1, 4, 2, 1, 1, 2, 5]
def baseStart_932014 : Nat := 118140960795 + 932014 * 2 ^ 59
def prefixEnd_932014 : Nat := 4983230072969 + 3 ^ 40 * 932014 * 2
def baseEnd_932014 : Nat := 141798861842850881374445

theorem tailTrace_932014 : CollatzResearch.WordTrace tailWord_932014 prefixEnd_932014 141798861842850881374445 := by
  unfold tailWord_932014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4249167905684991020464387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22662228830319952109143397 4249167905684991020464387)
  ·
    refine ⟨6373751858527486530696581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4249167905684991020464387 6373751858527486530696581)
    ·
      refine ⟨1195078473473903724505609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6373751858527486530696581 1195078473473903724505609)
      ·
        refine ⟨896308855105427793379207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1195078473473903724505609 896308855105427793379207)
        ·
          refine ⟨1344463282658141690068811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896308855105427793379207 1344463282658141690068811)
          ·
            refine ⟨2016694923987212535103217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344463282658141690068811 2016694923987212535103217)
            ·
              refine ⟨1512521192990409401327413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016694923987212535103217 1512521192990409401327413)
              ·
                refine ⟨141798861842850881374445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1512521192990409401327413 141798861842850881374445)
                ·
                  rfl

theorem cell20_932014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_932014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932014 prefixEnd_932014 := by exact prefixLift 932014
  have htrace : WordTrace (prefixWord ++ tailWord_932014) baseStart_932014 baseEnd_932014 := by
    simpa [prefixWord, tailWord_932014, baseEnd_932014] using wordTrace_append hprefix tailTrace_932014
  have hstable : (prefixWord ++ tailWord_932014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932014).length < 2 ^ (prefixWord ++ tailWord_932014).sum := by decide
  have hdescent : baseEnd_932014 < baseStart_932014 := by decide
  rcases family_descends (prefixWord ++ tailWord_932014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932021 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 3]
def baseStart_932021 : Nat := 118140960795 + 932021 * 2 ^ 59
def prefixEnd_932021 : Nat := 4983230072969 + 3 ^ 40 * 932021 * 2
def baseEnd_932021 : Nat := 425399780519291730889973

theorem tailTrace_932021 : CollatzResearch.WordTrace tailWord_932021 prefixEnd_932021 425399780519291730889973 := by
  unfold tailWord_932021
  simp only [CollatzResearch.WordTrace]
  refine ⟨33993598556454568359219917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22662399037636378906146611 33993598556454568359219917)
  ·
    refine ⟨12747599458670463134707469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33993598556454568359219917 12747599458670463134707469)
    ·
      refine ⟨4780349797001423675515301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12747599458670463134707469 4780349797001423675515301)
      ·
        refine ⟨896315586937766939159119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4780349797001423675515301 896315586937766939159119)
        ·
          refine ⟨1344473380406650408738679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896315586937766939159119 1344473380406650408738679)
          ·
            refine ⟨2016710070609975613108019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344473380406650408738679 2016710070609975613108019)
            ·
              refine ⟨3025065105914963419662029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016710070609975613108019 3025065105914963419662029)
              ·
                refine ⟨1134399414718111282373261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3025065105914963419662029 1134399414718111282373261)
                ·
                  refine ⟨425399780519291730889973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134399414718111282373261 425399780519291730889973)
                  ·
                    rfl

theorem cell20_932021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_932021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932021 prefixEnd_932021 := by exact prefixLift 932021
  have htrace : WordTrace (prefixWord ++ tailWord_932021) baseStart_932021 baseEnd_932021 := by
    simpa [prefixWord, tailWord_932021, baseEnd_932021] using wordTrace_append hprefix tailTrace_932021
  have hstable : (prefixWord ++ tailWord_932021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932021).length < 2 ^ (prefixWord ++ tailWord_932021).sum := by decide
  have hdescent : baseEnd_932021 < baseStart_932021 := by decide
  rcases family_descends (prefixWord ++ tailWord_932021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932025 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 3]
def baseStart_932025 : Nat := 118140960795 + 932025 * 2 ^ 59
def prefixEnd_932025 : Nat := 4983230072969 + 3 ^ 40 * 932025 * 2
def baseEnd_932025 : Nat := 425401606228285494756623

theorem tailTrace_932025 : CollatzResearch.WordTrace tailWord_932025 prefixEnd_932025 425401606228285494756623 := by
  unfold tailWord_932025
  simp only [CollatzResearch.WordTrace]
  refine ⟨33993744448440077042365529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22662496298960051361577019 33993744448440077042365529)
  ·
    refine ⟨25495308336330057781774147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33993744448440077042365529 25495308336330057781774147)
    ·
      refine ⟨38242962504495086672661221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25495308336330057781774147 38242962504495086672661221)
      ·
        refine ⟨7170555469592828751123979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38242962504495086672661221 7170555469592828751123979)
        ·
          refine ⟨10755833204389243126685969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170555469592828751123979 10755833204389243126685969)
          ·
            refine ⟨8066874903291932345014477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10755833204389243126685969 8066874903291932345014477)
            ·
              refine ⟨3025078088734474629380429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8066874903291932345014477 3025078088734474629380429)
              ·
                refine ⟨1134404283275427986017661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3025078088734474629380429 1134404283275427986017661)
                ·
                  refine ⟨425401606228285494756623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134404283275427986017661 425401606228285494756623)
                  ·
                    rfl

theorem cell20_932025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_932025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932025 prefixEnd_932025 := by exact prefixLift 932025
  have htrace : WordTrace (prefixWord ++ tailWord_932025) baseStart_932025 baseEnd_932025 := by
    simpa [prefixWord, tailWord_932025, baseEnd_932025] using wordTrace_append hprefix tailTrace_932025
  have hstable : (prefixWord ++ tailWord_932025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932025).length < 2 ^ (prefixWord ++ tailWord_932025).sum := by decide
  have hdescent : baseEnd_932025 < baseStart_932025 := by decide
  rcases family_descends (prefixWord ++ tailWord_932025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932104 : List Nat := [2, 1, 3, 2, 3, 2, 2, 3, 2]
def baseStart_932104 : Nat := 118140960795 + 932104 * 2 ^ 59
def prefixEnd_932104 : Nat := 4983230072969 + 3 ^ 40 * 932104 * 2
def baseEnd_932104 : Nat := 425437663980912331122967

theorem tailTrace_932104 : CollatzResearch.WordTrace tailWord_932104 prefixEnd_932104 425437663980912331122967 := by
  unfold tailWord_932104
  simp only [CollatzResearch.WordTrace]
  refine ⟨16998312907576936767245683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22664417210102582356327577 16998312907576936767245683)
  ·
    refine ⟨25497469361365405150868525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16998312907576936767245683 25497469361365405150868525)
    ·
      refine ⟨9561551010512026931575697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25497469361365405150868525 9561551010512026931575697)
      ·
        refine ⟨7171163257884020198681773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9561551010512026931575697 7171163257884020198681773)
        ·
          refine ⟨2689186221706507574505665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7171163257884020198681773 2689186221706507574505665)
          ·
            refine ⟨2016889666279880680879249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2689186221706507574505665 2016889666279880680879249)
            ·
              refine ⟨1512667249709910510659437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016889666279880680879249 1512667249709910510659437)
              ·
                refine ⟨567250218641216441497289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1512667249709910510659437 567250218641216441497289)
                ·
                  refine ⟨425437663980912331122967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567250218641216441497289 425437663980912331122967)
                  ·
                    rfl

theorem cell20_932104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_932104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932104 prefixEnd_932104 := by exact prefixLift 932104
  have htrace : WordTrace (prefixWord ++ tailWord_932104) baseStart_932104 baseEnd_932104 := by
    simpa [prefixWord, tailWord_932104, baseEnd_932104] using wordTrace_append hprefix tailTrace_932104
  have hstable : (prefixWord ++ tailWord_932104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932104).length < 2 ^ (prefixWord ++ tailWord_932104).sum := by decide
  have hdescent : baseEnd_932104 < baseStart_932104 := by decide
  rcases family_descends (prefixWord ++ tailWord_932104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932163 : List Nat := [1, 1, 1, 3, 1, 3, 5, 3, 2]
def baseStart_932163 : Nat := 118140960795 + 932163 * 2 ^ 59
def prefixEnd_932163 : Nat := 4983230072969 + 3 ^ 40 * 932163 * 2
def baseEnd_932163 : Nat := 425464593188570348156059

theorem tailTrace_932163 : CollatzResearch.WordTrace tailWord_932163 prefixEnd_932163 425464593188570348156059 := by
  unfold tailWord_932163
  simp only [CollatzResearch.WordTrace]
  refine ⟨33998777721940126610889143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22665851814626751073926095 33998777721940126610889143)
  ·
    refine ⟨50998166582910189916333715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33998777721940126610889143 50998166582910189916333715)
    ·
      refine ⟨76497249874365284874500573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50998166582910189916333715 76497249874365284874500573)
      ·
        refine ⟨28686468702886981827937715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76497249874365284874500573 28686468702886981827937715)
        ·
          refine ⟨43029703054330472741906573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28686468702886981827937715 43029703054330472741906573)
          ·
            refine ⟨16136138645373927278214965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43029703054330472741906573 16136138645373927278214965)
            ·
              refine ⟨1512762998003805682332653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16136138645373927278214965 1512762998003805682332653)
              ·
                refine ⟨567286124251427130874745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1512762998003805682332653 567286124251427130874745)
                ·
                  refine ⟨425464593188570348156059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567286124251427130874745 425464593188570348156059)
                  ·
                    rfl

theorem cell20_932163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 2].length) (baseStart_932163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932163 prefixEnd_932163 := by exact prefixLift 932163
  have htrace : WordTrace (prefixWord ++ tailWord_932163) baseStart_932163 baseEnd_932163 := by
    simpa [prefixWord, tailWord_932163, baseEnd_932163] using wordTrace_append hprefix tailTrace_932163
  have hstable : (prefixWord ++ tailWord_932163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932163).length < 2 ^ (prefixWord ++ tailWord_932163).sum := by decide
  have hdescent : baseEnd_932163 < baseStart_932163 := by decide
  rcases family_descends (prefixWord ++ tailWord_932163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932194 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_932194 : Nat := 118140960795 + 932194 * 2 ^ 59
def prefixEnd_932194 : Nat := 4983230072969 + 3 ^ 40 * 932194 * 2
def baseEnd_932194 : Nat := 425478742433272018122599

theorem tailTrace_932194 : CollatzResearch.WordTrace tailWord_932194 prefixEnd_932194 425478742433272018122599 := by
  unfold tailWord_932194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8499977096206954726316909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22666605589885212603511757 8499977096206954726316909)
  ·
    refine ⟨3187491411077608022368841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8499977096206954726316909 3187491411077608022368841)
    ·
      refine ⟨2390618558308206016776631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3187491411077608022368841 2390618558308206016776631)
      ·
        refine ⟨3585927837462309025164947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2390618558308206016776631 3585927837462309025164947)
        ·
          refine ⟨5378891756193463537747421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585927837462309025164947 5378891756193463537747421)
          ·
            refine ⟨2017084408572548826655283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5378891756193463537747421 2017084408572548826655283)
            ·
              refine ⟨3025626612858823239982925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017084408572548826655283 3025626612858823239982925)
              ·
                refine ⟨1134609979822058714993597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3025626612858823239982925 1134609979822058714993597)
                ·
                  refine ⟨425478742433272018122599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134609979822058714993597 425478742433272018122599)
                  ·
                    rfl

theorem cell20_932194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_932194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932194 prefixEnd_932194 := by exact prefixLift 932194
  have htrace : WordTrace (prefixWord ++ tailWord_932194) baseStart_932194 baseEnd_932194 := by
    simpa [prefixWord, tailWord_932194, baseEnd_932194] using wordTrace_append hprefix tailTrace_932194
  have hstable : (prefixWord ++ tailWord_932194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932194).length < 2 ^ (prefixWord ++ tailWord_932194).sum := by decide
  have hdescent : baseEnd_932194 < baseStart_932194 := by decide
  rcases family_descends (prefixWord ++ tailWord_932194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932274 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_932274 : Nat := 118140960795 + 932274 * 2 ^ 59
def prefixEnd_932274 : Nat := 4983230072969 + 3 ^ 40 * 932274 * 2
def baseEnd_932274 : Nat := 425515256613147295455605

theorem tailTrace_932274 : CollatzResearch.WordTrace tailWord_932274 prefixEnd_932274 425515256613147295455605 := by
  unfold tailWord_932274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8500706556134498142044969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22668550816358661712119917 8500706556134498142044969)
  ·
    refine ⟨6375529917100873606533727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8500706556134498142044969 6375529917100873606533727)
    ·
      refine ⟨9563294875651310409800591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6375529917100873606533727 9563294875651310409800591)
      ·
        refine ⟨14344942313476965614700887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9563294875651310409800591 14344942313476965614700887)
        ·
          refine ⟨21517413470215448422051331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14344942313476965614700887 21517413470215448422051331)
          ·
            refine ⟨32276120205323172633076997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21517413470215448422051331 32276120205323172633076997)
            ·
              refine ⟨6051772538498094868701937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32276120205323172633076997 6051772538498094868701937)
              ·
                refine ⟨4538829403873571151526453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6051772538498094868701937 4538829403873571151526453)
                ·
                  refine ⟨425515256613147295455605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4538829403873571151526453 425515256613147295455605)
                  ·
                    rfl

theorem cell20_932274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_932274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932274 prefixEnd_932274 := by exact prefixLift 932274
  have htrace : WordTrace (prefixWord ++ tailWord_932274) baseStart_932274 baseEnd_932274 := by
    simpa [prefixWord, tailWord_932274, baseEnd_932274] using wordTrace_append hprefix tailTrace_932274
  have hstable : (prefixWord ++ tailWord_932274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932274).length < 2 ^ (prefixWord ++ tailWord_932274).sum := by decide
  have hdescent : baseEnd_932274 < baseStart_932274 := by decide
  rcases family_descends (prefixWord ++ tailWord_932274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932298 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_932298 : Nat := 118140960795 + 932298 * 2 ^ 59
def prefixEnd_932298 : Nat := 4983230072969 + 3 ^ 40 * 932298 * 2
def baseEnd_932298 : Nat := 425526210867109878655507

theorem tailTrace_932298 : CollatzResearch.WordTrace tailWord_932298 prefixEnd_932298 425526210867109878655507 := by
  unfold tailWord_932298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8500925394112761166763387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22669134384300696444702365 8500925394112761166763387)
  ·
    refine ⟨12751388091169141750145081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8500925394112761166763387 12751388091169141750145081)
    ·
      refine ⟨9563541068376856312608811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12751388091169141750145081 9563541068376856312608811)
      ·
        refine ⟨14345311602565284468913217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9563541068376856312608811 14345311602565284468913217)
        ·
          refine ⟨10758983701923963351684913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14345311602565284468913217 10758983701923963351684913)
          ·
            refine ⟨8069237776442972513763685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10758983701923963351684913 8069237776442972513763685)
            ·
              refine ⟨1512982083083057346330691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8069237776442972513763685 1512982083083057346330691)
              ·
                refine ⟨2269473124624586019496037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512982083083057346330691 2269473124624586019496037)
                ·
                  refine ⟨425526210867109878655507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269473124624586019496037 425526210867109878655507)
                  ·
                    rfl

theorem cell20_932298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_932298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932298 prefixEnd_932298 := by exact prefixLift 932298
  have htrace : WordTrace (prefixWord ++ tailWord_932298) baseStart_932298 baseEnd_932298 := by
    simpa [prefixWord, tailWord_932298, baseEnd_932298] using wordTrace_append hprefix tailTrace_932298
  have hstable : (prefixWord ++ tailWord_932298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932298).length < 2 ^ (prefixWord ++ tailWord_932298).sum := by decide
  have hdescent : baseEnd_932298 < baseStart_932298 := by decide
  rcases family_descends (prefixWord ++ tailWord_932298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932353 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 4]
def baseStart_932353 : Nat := 118140960795 + 932353 * 2 ^ 59
def prefixEnd_932353 : Nat := 4983230072969 + 3 ^ 40 * 932353 * 2
def baseEnd_932353 : Nat := 425551314365774131821949

theorem tailTrace_932353 : CollatzResearch.WordTrace tailWord_932353 prefixEnd_932353 425551314365774131821949 := by
  unfold tailWord_932353
  simp only [CollatzResearch.WordTrace]
  refine ⟨34005707591251789060305713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22670471727501192706870475 34005707591251789060305713)
  ·
    refine ⟨25504280693438841795229285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34005707591251789060305713 25504280693438841795229285)
    ·
      refine ⟨4782052630019782836605491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25504280693438841795229285 4782052630019782836605491)
      ·
        refine ⟨7173078945029674254908237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4782052630019782836605491 7173078945029674254908237)
        ·
          refine ⟨2689904604386127845590589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7173078945029674254908237 2689904604386127845590589)
          ·
            refine ⟨1008714226644797942096471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2689904604386127845590589 1008714226644797942096471)
            ·
              refine ⟨1513071339967196913144707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008714226644797942096471 1513071339967196913144707)
              ·
                refine ⟨2269607009950795369717061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513071339967196913144707 2269607009950795369717061)
                ·
                  refine ⟨425551314365774131821949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269607009950795369717061 425551314365774131821949)
                  ·
                    rfl

theorem cell20_932353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_932353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932353 prefixEnd_932353 := by exact prefixLift 932353
  have htrace : WordTrace (prefixWord ++ tailWord_932353) baseStart_932353 baseEnd_932353 := by
    simpa [prefixWord, tailWord_932353, baseEnd_932353] using wordTrace_append hprefix tailTrace_932353
  have hstable : (prefixWord ++ tailWord_932353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932353).length < 2 ^ (prefixWord ++ tailWord_932353).sum := by decide
  have hdescent : baseEnd_932353 < baseStart_932353 := by decide
  rcases family_descends (prefixWord ++ tailWord_932353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932381 : List Nat := [1, 4, 2, 2, 1, 2, 2, 6]
def baseStart_932381 : Nat := 118140960795 + 932381 * 2 ^ 59
def prefixEnd_932381 : Nat := 4983230072969 + 3 ^ 40 * 932381 * 2
def baseEnd_932381 : Nat := 141854698109576826296167

theorem tailTrace_932381 : CollatzResearch.WordTrace tailWord_932381 prefixEnd_932381 141854698109576826296167 := by
  unfold tailWord_932381
  simp only [CollatzResearch.WordTrace]
  refine ⟨34006728835150349842324997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22671152556766899894883331 34006728835150349842324997)
  ·
    refine ⟨6376261656590690595435937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34006728835150349842324997 6376261656590690595435937)
    ·
      refine ⟨4782196242443017946576953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6376261656590690595435937 4782196242443017946576953)
      ·
        refine ⟨3586647181832263459932715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4782196242443017946576953 3586647181832263459932715)
        ·
          refine ⟨5379970772748395189899073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586647181832263459932715 5379970772748395189899073)
          ·
            refine ⟨4034978079561296392424305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5379970772748395189899073 4034978079561296392424305)
            ·
              refine ⟨3026233559670972294318229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4034978079561296392424305 3026233559670972294318229)
              ·
                refine ⟨141854698109576826296167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3026233559670972294318229 141854698109576826296167)
                ·
                  rfl

theorem cell20_932381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_932381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932381 prefixEnd_932381 := by exact prefixLift 932381
  have htrace : WordTrace (prefixWord ++ tailWord_932381) baseStart_932381 baseEnd_932381 := by
    simpa [prefixWord, tailWord_932381, baseEnd_932381] using wordTrace_append hprefix tailTrace_932381
  have hstable : (prefixWord ++ tailWord_932381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932381).length < 2 ^ (prefixWord ++ tailWord_932381).sum := by decide
  have hdescent : baseEnd_932381 < baseStart_932381 := by decide
  rcases family_descends (prefixWord ++ tailWord_932381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932398 : List Nat := [4, 1, 3, 1, 4, 7]
def baseStart_932398 : Nat := 118140960795 + 932398 * 2 ^ 59
def prefixEnd_932398 : Nat := 4983230072969 + 3 ^ 40 * 932398 * 2
def baseEnd_932398 : Nat := 15761920503405702789695

theorem tailTrace_932398 : CollatzResearch.WordTrace tailWord_932398 prefixEnd_932398 15761920503405702789695 := by
  unfold tailWord_932398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250918609511095218211731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22671565917392507830462565 4250918609511095218211731)
  ·
    refine ⟨6376377914266642827317597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4250918609511095218211731 6376377914266642827317597)
    ·
      refine ⟨2391141717849991060244099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6376377914266642827317597 2391141717849991060244099)
      ·
        refine ⟨3586712576774986590366149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391141717849991060244099 3586712576774986590366149)
        ·
          refine ⟨672508608145309985693653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3586712576774986590366149 672508608145309985693653)
          ·
            refine ⟨15761920503405702789695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 672508608145309985693653 15761920503405702789695)
            ·
              rfl

theorem cell20_932398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 7].length) (baseStart_932398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932398 prefixEnd_932398 := by exact prefixLift 932398
  have htrace : WordTrace (prefixWord ++ tailWord_932398) baseStart_932398 baseEnd_932398 := by
    simpa [prefixWord, tailWord_932398, baseEnd_932398] using wordTrace_append hprefix tailTrace_932398
  have hstable : (prefixWord ++ tailWord_932398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932398).length < 2 ^ (prefixWord ++ tailWord_932398).sum := by decide
  have hdescent : baseEnd_932398 < baseStart_932398 := by decide
  rcases family_descends (prefixWord ++ tailWord_932398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932405 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 3]
def baseStart_932405 : Nat := 118140960795 + 932405 * 2 ^ 59
def prefixEnd_932405 : Nat := 4983230072969 + 3 ^ 40 * 932405 * 2
def baseEnd_932405 : Nat := 425575048582693062088403

theorem tailTrace_932405 : CollatzResearch.WordTrace tailWord_932405 prefixEnd_932405 425575048582693062088403 := by
  unfold tailWord_932405
  simp only [CollatzResearch.WordTrace]
  refine ⟨34007604187063401941198669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22671736124708934627465779 34007604187063401941198669)
  ·
    refine ⟨12752851570148775727949501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34007604187063401941198669 12752851570148775727949501)
    ·
      refine ⟨4782319338805790897981063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12752851570148775727949501 4782319338805790897981063)
      ·
        refine ⟨7173479008208686346971595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4782319338805790897981063 7173479008208686346971595)
        ·
          refine ⟨10760218512313029520457393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173479008208686346971595 10760218512313029520457393)
          ·
            refine ⟨8070163884234772140343045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10760218512313029520457393 8070163884234772140343045)
            ·
              refine ⟨1513155728294019776314321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8070163884234772140343045 1513155728294019776314321)
              ·
                refine ⟨1134866796220514832235741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513155728294019776314321 1134866796220514832235741)
                ·
                  refine ⟨425575048582693062088403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134866796220514832235741 425575048582693062088403)
                  ·
                    rfl

theorem cell20_932405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_932405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932405 prefixEnd_932405 := by exact prefixLift 932405
  have htrace : WordTrace (prefixWord ++ tailWord_932405) baseStart_932405 baseEnd_932405 := by
    simpa [prefixWord, tailWord_932405, baseEnd_932405] using wordTrace_append hprefix tailTrace_932405
  have hstable : (prefixWord ++ tailWord_932405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932405).length < 2 ^ (prefixWord ++ tailWord_932405).sum := by decide
  have hdescent : baseEnd_932405 < baseStart_932405 := by decide
  rcases family_descends (prefixWord ++ tailWord_932405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932429 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_932429 : Nat := 118140960795 + 932429 * 2 ^ 59
def prefixEnd_932429 : Nat := 4983230072969 + 3 ^ 40 * 932429 * 2
def baseEnd_932429 : Nat := 425586002836655645288305

theorem tailTrace_932429 : CollatzResearch.WordTrace tailWord_932429 prefixEnd_932429 425586002836655645288305 := by
  unfold tailWord_932429
  simp only [CollatzResearch.WordTrace]
  refine ⟨34008479538976454040072341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22672319692650969360048227 34008479538976454040072341)
  ·
    refine ⟨1594147478389521283128391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34008479538976454040072341 1594147478389521283128391)
    ·
      refine ⟨2391221217584281924692587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1594147478389521283128391 2391221217584281924692587)
      ·
        refine ⟨3586831826376422887038881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391221217584281924692587 3586831826376422887038881)
        ·
          refine ⟨2690123869782317165279161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3586831826376422887038881 2690123869782317165279161)
          ·
            refine ⟨2017592902336737873959371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2690123869782317165279161 2017592902336737873959371)
            ·
              refine ⟨3026389353505106810939057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017592902336737873959371 3026389353505106810939057)
              ·
                refine ⟨2269792015128830108204293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026389353505106810939057 2269792015128830108204293)
                ·
                  refine ⟨425586002836655645288305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269792015128830108204293 425586002836655645288305)
                  ·
                    rfl

theorem cell20_932429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_932429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932429 prefixEnd_932429 := by exact prefixLift 932429
  have htrace : WordTrace (prefixWord ++ tailWord_932429) baseStart_932429 baseEnd_932429 := by
    simpa [prefixWord, tailWord_932429, baseEnd_932429] using wordTrace_append hprefix tailTrace_932429
  have hstable : (prefixWord ++ tailWord_932429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932429).length < 2 ^ (prefixWord ++ tailWord_932429).sum := by decide
  have hdescent : baseEnd_932429 < baseStart_932429 := by decide
  rcases family_descends (prefixWord ++ tailWord_932429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932433 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_932433 : Nat := 118140960795 + 932433 * 2 ^ 59
def prefixEnd_932433 : Nat := 4983230072969 + 3 ^ 40 * 932433 * 2
def baseEnd_932433 : Nat := 425587828545649409154955

theorem tailTrace_932433 : CollatzResearch.WordTrace tailWord_932433 prefixEnd_932433 425587828545649409154955 := by
  unfold tailWord_932433
  simp only [CollatzResearch.WordTrace]
  refine ⟨34008625430961962723217953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22672416953974641815478635 34008625430961962723217953)
  ·
    refine ⟨25506469073221472042413465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34008625430961962723217953 25506469073221472042413465)
    ·
      refine ⟨19129851804916104031810099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25506469073221472042413465 19129851804916104031810099)
      ·
        refine ⟨28694777707374156047715149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19129851804916104031810099 28694777707374156047715149)
        ·
          refine ⟨10760541640265308517893181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28694777707374156047715149 10760541640265308517893181)
          ·
            refine ⟨4035203115099490694209943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10760541640265308517893181 4035203115099490694209943)
            ·
              refine ⟨6052804672649236041314915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035203115099490694209943 6052804672649236041314915)
              ·
                refine ⟨9079207008973854061972373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052804672649236041314915 9079207008973854061972373)
                ·
                  refine ⟨425587828545649409154955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9079207008973854061972373 425587828545649409154955)
                  ·
                    rfl

theorem cell20_932433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_932433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932433 prefixEnd_932433 := by exact prefixLift 932433
  have htrace : WordTrace (prefixWord ++ tailWord_932433) baseStart_932433 baseEnd_932433 := by
    simpa [prefixWord, tailWord_932433, baseEnd_932433] using wordTrace_append hprefix tailTrace_932433
  have hstable : (prefixWord ++ tailWord_932433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932433).length < 2 ^ (prefixWord ++ tailWord_932433).sum := by decide
  have hdescent : baseEnd_932433 < baseStart_932433 := by decide
  rcases family_descends (prefixWord ++ tailWord_932433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932436 : List Nat := [2, 4, 1, 1, 1, 4, 3, 4]
def baseStart_932436 : Nat := 118140960795 + 932436 * 2 ^ 59
def prefixEnd_932436 : Nat := 4983230072969 + 3 ^ 40 * 932436 * 2
def baseEnd_932436 : Nat := 141863065942464910684981

theorem tailTrace_932436 : CollatzResearch.WordTrace tailWord_932436 prefixEnd_932436 141863065942464910684981 := by
  unfold tailWord_932436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004367424975547117788581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22672489899967396157051441 17004367424975547117788581)
  ·
    refine ⟨3188318892182915084585359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17004367424975547117788581 3188318892182915084585359)
    ·
      refine ⟨4782478338274372626878039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3188318892182915084585359 4782478338274372626878039)
      ·
        refine ⟨7173717507411558940317059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4782478338274372626878039 7173717507411558940317059)
        ·
          refine ⟨10760576261117338410475589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173717507411558940317059 10760576261117338410475589)
          ·
            refine ⟨2017608048959500951964173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10760576261117338410475589 2017608048959500951964173)
            ·
              refine ⟨756603018359812856986565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2017608048959500951964173 756603018359812856986565)
              ·
                refine ⟨141863065942464910684981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 756603018359812856986565 141863065942464910684981)
                ·
                  rfl

theorem cell20_932436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_932436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932436 prefixEnd_932436 := by exact prefixLift 932436
  have htrace : WordTrace (prefixWord ++ tailWord_932436) baseStart_932436 baseEnd_932436 := by
    simpa [prefixWord, tailWord_932436, baseEnd_932436] using wordTrace_append hprefix tailTrace_932436
  have hstable : (prefixWord ++ tailWord_932436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932436).length < 2 ^ (prefixWord ++ tailWord_932436).sum := by decide
  have hdescent : baseEnd_932436 < baseStart_932436 := by decide
  rcases family_descends (prefixWord ++ tailWord_932436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932440 : List Nat := [2, 1, 2, 2, 1, 2, 2, 8]
def baseStart_932440 : Nat := 118140960795 + 932440 * 2 ^ 59
def prefixEnd_932440 : Nat := 4983230072969 + 3 ^ 40 * 932440 * 2
def baseEnd_932440 : Nat := 141863674512129498640531

theorem tailTrace_932440 : CollatzResearch.WordTrace tailWord_932440 prefixEnd_932440 141863674512129498640531 := by
  unfold tailWord_932440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004440370968301459361387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22672587161291068612481849 17004440370968301459361387)
  ·
    refine ⟨25506660556452452189042081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17004440370968301459361387 25506660556452452189042081)
    ·
      refine ⟨19129995417339339141781561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25506660556452452189042081 19129995417339339141781561)
      ·
        refine ⟨14347496563004504356336171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19129995417339339141781561 14347496563004504356336171)
        ·
          refine ⟨21521244844506756534504257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14347496563004504356336171 21521244844506756534504257)
          ·
            refine ⟨16140933633380067400878193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21521244844506756534504257 16140933633380067400878193)
            ·
              refine ⟨12105700225035050550658645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16140933633380067400878193 12105700225035050550658645)
              ·
                refine ⟨141863674512129498640531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12105700225035050550658645 141863674512129498640531)
                ·
                  rfl

theorem cell20_932440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_932440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932440 prefixEnd_932440 := by exact prefixLift 932440
  have htrace : WordTrace (prefixWord ++ tailWord_932440) baseStart_932440 baseEnd_932440 := by
    simpa [prefixWord, tailWord_932440, baseEnd_932440] using wordTrace_append hprefix tailTrace_932440
  have hstable : (prefixWord ++ tailWord_932440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932440).length < 2 ^ (prefixWord ++ tailWord_932440).sum := by decide
  have hdescent : baseEnd_932440 < baseStart_932440 := by decide
  rcases family_descends (prefixWord ++ tailWord_932440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932471 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_932471 : Nat := 118140960795 + 932471 * 2 ^ 59
def prefixEnd_932471 : Nat := 4983230072969 + 3 ^ 40 * 932471 * 2
def baseEnd_932471 : Nat := 425605172781090165888133

theorem tailTrace_932471 : CollatzResearch.WordTrace tailWord_932471 prefixEnd_932471 425605172781090165888133 := by
  unfold tailWord_932471
  simp only [CollatzResearch.WordTrace]
  refine ⟨34010011404824295213101267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22673340936549530142067511 34010011404824295213101267)
  ·
    refine ⟨51015017107236442819651901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34010011404824295213101267 51015017107236442819651901)
    ·
      refine ⟨19130631415213666057369463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51015017107236442819651901 19130631415213666057369463)
      ·
        refine ⟨28695947122820499086054195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19130631415213666057369463 28695947122820499086054195)
        ·
          refine ⟨43043920684230748629081293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28695947122820499086054195 43043920684230748629081293)
          ·
            refine ⟨16141470256586530735905485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43043920684230748629081293 16141470256586530735905485)
            ·
              refine ⟨6053051346219949025964557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16141470256586530735905485 6053051346219949025964557)
              ·
                refine ⟨2269894254832480884736709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6053051346219949025964557 2269894254832480884736709)
                ·
                  refine ⟨425605172781090165888133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269894254832480884736709 425605172781090165888133)
                  ·
                    rfl

theorem cell20_932471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_932471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932471 prefixEnd_932471 := by exact prefixLift 932471
  have htrace : WordTrace (prefixWord ++ tailWord_932471) baseStart_932471 baseEnd_932471 := by
    simpa [prefixWord, tailWord_932471, baseEnd_932471] using wordTrace_append hprefix tailTrace_932471
  have hstable : (prefixWord ++ tailWord_932471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932471).length < 2 ^ (prefixWord ++ tailWord_932471).sum := by decide
  have hdescent : baseEnd_932471 < baseStart_932471 := by decide
  rcases family_descends (prefixWord ++ tailWord_932471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932509 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_932509 : Nat := 118140960795 + 932509 * 2 ^ 59
def prefixEnd_932509 : Nat := 4983230072969 + 3 ^ 40 * 932509 * 2
def baseEnd_932509 : Nat := 425622517016530922621311

theorem tailTrace_932509 : CollatzResearch.WordTrace tailWord_932509 prefixEnd_932509 425622517016530922621311 := by
  unfold tailWord_932509
  simp only [CollatzResearch.WordTrace]
  refine ⟨34011397378686627702984581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22674264919124418468656387 34011397378686627702984581)
  ·
    refine ⟨6377137008503742694309609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34011397378686627702984581 6377137008503742694309609)
    ·
      refine ⟨4782852756377807020732207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6377137008503742694309609 4782852756377807020732207)
      ·
        refine ⟨7174279134566710531098311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4782852756377807020732207 7174279134566710531098311)
        ·
          refine ⟨10761418701850065796647467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174279134566710531098311 10761418701850065796647467)
          ·
            refine ⟨16142128052775098694971201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10761418701850065796647467 16142128052775098694971201)
            ·
              refine ⟨12106596039581324021228401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16142128052775098694971201 12106596039581324021228401)
              ·
                refine ⟨9079947029685993015921301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12106596039581324021228401 9079947029685993015921301)
                ·
                  refine ⟨425622517016530922621311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9079947029685993015921301 425622517016530922621311)
                  ·
                    rfl

theorem cell20_932509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_932509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932509 prefixEnd_932509 := by exact prefixLift 932509
  have htrace : WordTrace (prefixWord ++ tailWord_932509) baseStart_932509 baseEnd_932509 := by
    simpa [prefixWord, tailWord_932509, baseEnd_932509] using wordTrace_append hprefix tailTrace_932509
  have hstable : (prefixWord ++ tailWord_932509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932509).length < 2 ^ (prefixWord ++ tailWord_932509).sum := by decide
  have hdescent : baseEnd_932509 < baseStart_932509 := by decide
  rcases family_descends (prefixWord ++ tailWord_932509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932512 : List Nat := [2, 1, 1, 4, 5, 1, 6]
def baseStart_932512 : Nat := 118140960795 + 932512 * 2 ^ 59
def prefixEnd_932512 : Nat := 4983230072969 + 3 ^ 40 * 932512 * 2
def baseEnd_932512 : Nat := 47291542922030693946811

theorem tailTrace_932512 : CollatzResearch.WordTrace tailWord_932512 prefixEnd_932512 47291542922030693946811 := by
  unfold tailWord_932512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005753398837879607671895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22674337865117172810229193 17005753398837879607671895)
  ·
    refine ⟨25508630098256819411507843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17005753398837879607671895 25508630098256819411507843)
    ·
      refine ⟨38262945147385229117261765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25508630098256819411507843 38262945147385229117261765)
      ·
        refine ⟨7174302215134730459486581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38262945147385229117261765 7174302215134730459486581)
        ·
          refine ⟨672590832668880980576867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7174302215134730459486581 672590832668880980576867)
          ·
            refine ⟨1008886249003321470865301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672590832668880980576867 1008886249003321470865301)
            ·
              refine ⟨47291542922030693946811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1008886249003321470865301 47291542922030693946811)
              ·
                rfl

theorem cell20_932512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 6].length) (baseStart_932512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932512 prefixEnd_932512 := by exact prefixLift 932512
  have htrace : WordTrace (prefixWord ++ tailWord_932512) baseStart_932512 baseEnd_932512 := by
    simpa [prefixWord, tailWord_932512, baseEnd_932512] using wordTrace_append hprefix tailTrace_932512
  have hstable : (prefixWord ++ tailWord_932512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932512).length < 2 ^ (prefixWord ++ tailWord_932512).sum := by decide
  have hdescent : baseEnd_932512 < baseStart_932512 := by decide
  rcases family_descends (prefixWord ++ tailWord_932512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932533 : List Nat := [1, 3, 3, 3, 1, 1, 1, 7]
def baseStart_932533 : Nat := 118140960795 + 932533 * 2 ^ 59
def prefixEnd_932533 : Nat := 4983230072969 + 3 ^ 40 * 932533 * 2
def baseEnd_932533 : Nat := 141877823756831168607071

theorem tailTrace_932533 : CollatzResearch.WordTrace tailWord_932533 prefixEnd_932533 141877823756831168607071 := by
  unfold tailWord_932533
  simp only [CollatzResearch.WordTrace]
  refine ⟨34012272730599679801858253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22674848487066453201238835 34012272730599679801858253)
  ·
    refine ⟨12754602273974879925696845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34012272730599679801858253 12754602273974879925696845)
    ·
      refine ⟨4782975852740579972136317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12754602273974879925696845 4782975852740579972136317)
      ·
        refine ⟨1793615944777717489551119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4782975852740579972136317 1793615944777717489551119)
        ·
          refine ⟨2690423917166576234326679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793615944777717489551119 2690423917166576234326679)
          ·
            refine ⟨4035635875749864351490019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690423917166576234326679 4035635875749864351490019)
            ·
              refine ⟨6053453813624796527235029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035635875749864351490019 6053453813624796527235029)
              ·
                refine ⟨141877823756831168607071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6053453813624796527235029 141877823756831168607071)
                ·
                  rfl

theorem cell20_932533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_932533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932533 prefixEnd_932533 := by exact prefixLift 932533
  have htrace : WordTrace (prefixWord ++ tailWord_932533) baseStart_932533 baseEnd_932533 := by
    simpa [prefixWord, tailWord_932533, baseEnd_932533] using wordTrace_append hprefix tailTrace_932533
  have hstable : (prefixWord ++ tailWord_932533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932533).length < 2 ^ (prefixWord ++ tailWord_932533).sum := by decide
  have hdescent : baseEnd_932533 < baseStart_932533 := by decide
  rcases family_descends (prefixWord ++ tailWord_932533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932581 : List Nat := [1, 3, 1, 4, 1, 3, 1, 4, 2]
def baseStart_932581 : Nat := 118140960795 + 932581 * 2 ^ 59
def prefixEnd_932581 : Nat := 4983230072969 + 3 ^ 40 * 932581 * 2
def baseEnd_932581 : Nat := 425655379778418672221017

theorem tailTrace_932581 : CollatzResearch.WordTrace tailWord_932581 prefixEnd_932581 425655379778418672221017 := by
  unfold tailWord_932581
  simp only [CollatzResearch.WordTrace]
  refine ⟨34014023434425783999605597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22676015622950522666403731 34014023434425783999605597)
  ·
    refine ⟨12755258787909668999852099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34014023434425783999605597 12755258787909668999852099)
    ·
      refine ⟨19132888181864503499778149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12755258787909668999852099 19132888181864503499778149)
      ·
        refine ⟨3587416534099594406208403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19132888181864503499778149 3587416534099594406208403)
        ·
          refine ⟨5381124801149391609312605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3587416534099594406208403 5381124801149391609312605)
          ·
            refine ⟨2017921800431021853492227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5381124801149391609312605 2017921800431021853492227)
            ·
              refine ⟨3026882700646532780238341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017921800431021853492227 3026882700646532780238341)
              ·
                refine ⟨567540506371224896294689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3026882700646532780238341 567540506371224896294689)
                ·
                  refine ⟨425655379778418672221017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567540506371224896294689 425655379778418672221017)
                  ·
                    rfl

theorem cell20_932581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_932581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932581 prefixEnd_932581 := by exact prefixLift 932581
  have htrace : WordTrace (prefixWord ++ tailWord_932581) baseStart_932581 baseEnd_932581 := by
    simpa [prefixWord, tailWord_932581, baseEnd_932581] using wordTrace_append hprefix tailTrace_932581
  have hstable : (prefixWord ++ tailWord_932581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932581).length < 2 ^ (prefixWord ++ tailWord_932581).sum := by decide
  have hdescent : baseEnd_932581 < baseStart_932581 := by decide
  rcases family_descends (prefixWord ++ tailWord_932581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932599 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_932599 : Nat := 118140960795 + 932599 * 2 ^ 59
def prefixEnd_932599 : Nat := 4983230072969 + 3 ^ 40 * 932599 * 2
def baseEnd_932599 : Nat := 425663595468890609620943

theorem tailTrace_932599 : CollatzResearch.WordTrace tailWord_932599 prefixEnd_932599 425663595468890609620943 := by
  unfold tailWord_932599
  simp only [CollatzResearch.WordTrace]
  refine ⟨34014679948360573073760851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22676453298907048715840567 34014679948360573073760851)
  ·
    refine ⟨51022019922540859610641277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34014679948360573073760851 51022019922540859610641277)
    ·
      refine ⟨19133257470952822353990479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51022019922540859610641277 19133257470952822353990479)
      ·
        refine ⟨28699886206429233530985719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19133257470952822353990479 28699886206429233530985719)
        ·
          refine ⟨43049829309643850296478579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28699886206429233530985719 43049829309643850296478579)
          ·
            refine ⟨64574743964465775444717869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43049829309643850296478579 64574743964465775444717869)
            ·
              refine ⟨24215528986674665791769201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64574743964465775444717869 24215528986674665791769201)
              ·
                refine ⟨18161646740005999343826901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24215528986674665791769201 18161646740005999343826901)
                ·
                  refine ⟨425663595468890609620943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18161646740005999343826901 425663595468890609620943)
                  ·
                    rfl

theorem cell20_932599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_932599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932599 prefixEnd_932599 := by exact prefixLift 932599
  have htrace : WordTrace (prefixWord ++ tailWord_932599) baseStart_932599 baseEnd_932599 := by
    simpa [prefixWord, tailWord_932599, baseEnd_932599] using wordTrace_append hprefix tailTrace_932599
  have hstable : (prefixWord ++ tailWord_932599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932599).length < 2 ^ (prefixWord ++ tailWord_932599).sum := by decide
  have hdescent : baseEnd_932599 < baseStart_932599 := by decide
  rcases family_descends (prefixWord ++ tailWord_932599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932626 : List Nat := [3, 2, 4, 1, 2, 1, 7]
def baseStart_932626 : Nat := 118140960795 + 932626 * 2 ^ 59
def prefixEnd_932626 : Nat := 4983230072969 + 3 ^ 40 * 932626 * 2
def baseEnd_932626 : Nat := 47297324333844279524537

theorem tailTrace_932626 : CollatzResearch.WordTrace tailWord_932626 prefixEnd_932626 47297324333844279524537 := by
  unfold tailWord_932626
  simp only [CollatzResearch.WordTrace]
  refine ⟨8503916179815689171248433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22677109812841837789995821 8503916179815689171248433)
  ·
    refine ⟨6377937134861766878436325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8503916179815689171248433 6377937134861766878436325)
    ·
      refine ⟨1195863212786581289706811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6377937134861766878436325 1195863212786581289706811)
      ·
        refine ⟨1793794819179871934560217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195863212786581289706811 1793794819179871934560217)
        ·
          refine ⟨1345346114384903950920163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1793794819179871934560217 1345346114384903950920163)
          ·
            refine ⟨2018019171577355926380245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345346114384903950920163 2018019171577355926380245)
            ·
              refine ⟨47297324333844279524537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2018019171577355926380245 47297324333844279524537)
              ·
                rfl

theorem cell20_932626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 7].length) (baseStart_932626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932626 prefixEnd_932626 := by exact prefixLift 932626
  have htrace : WordTrace (prefixWord ++ tailWord_932626) baseStart_932626 baseEnd_932626 := by
    simpa [prefixWord, tailWord_932626, baseEnd_932626] using wordTrace_append hprefix tailTrace_932626
  have hstable : (prefixWord ++ tailWord_932626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932626).length < 2 ^ (prefixWord ++ tailWord_932626).sum := by decide
  have hdescent : baseEnd_932626 < baseStart_932626 := by decide
  rcases family_descends (prefixWord ++ tailWord_932626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932640 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_932640 : Nat := 118140960795 + 932640 * 2 ^ 59
def prefixEnd_932640 : Nat := 4983230072969 + 3 ^ 40 * 932640 * 2
def baseEnd_932640 : Nat := 425682308986076689254109

theorem tailTrace_932640 : CollatzResearch.WordTrace tailWord_932640 prefixEnd_932640 425682308986076689254109 := by
  unfold tailWord_932640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17008087670606018538001687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22677450227474691384002249 17008087670606018538001687)
  ·
    refine ⟨25512131505909027807002531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17008087670606018538001687 25512131505909027807002531)
    ·
      refine ⟨38268197258863541710503797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25512131505909027807002531 38268197258863541710503797)
      ·
        refine ⟨3587643493018457035359731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38268197258863541710503797 3587643493018457035359731)
        ·
          refine ⟨5381465239527685553039597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3587643493018457035359731 5381465239527685553039597)
          ·
            refine ⟨2018049464822882082389849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5381465239527685553039597 2018049464822882082389849)
            ·
              refine ⟨1513537098617161561792387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2018049464822882082389849 1513537098617161561792387)
              ·
                refine ⟨2270305647925742342688581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513537098617161561792387 2270305647925742342688581)
                ·
                  refine ⟨425682308986076689254109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270305647925742342688581 425682308986076689254109)
                  ·
                    rfl

theorem cell20_932640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_932640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932640 prefixEnd_932640 := by exact prefixLift 932640
  have htrace : WordTrace (prefixWord ++ tailWord_932640) baseStart_932640 baseEnd_932640 := by
    simpa [prefixWord, tailWord_932640, baseEnd_932640] using wordTrace_append hprefix tailTrace_932640
  have hstable : (prefixWord ++ tailWord_932640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932640).length < 2 ^ (prefixWord ++ tailWord_932640).sum := by decide
  have hdescent : baseEnd_932640 < baseStart_932640 := by decide
  rcases family_descends (prefixWord ++ tailWord_932640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932660 : List Nat := [2, 5, 1, 1, 4, 1, 2, 4]
def baseStart_932660 : Nat := 118140960795 + 932660 * 2 ^ 59
def prefixEnd_932660 : Nat := 4983230072969 + 3 ^ 40 * 932660 * 2
def baseEnd_932660 : Nat := 141897145843681836195787

theorem tailTrace_932660 : CollatzResearch.WordTrace tailWord_932660 prefixEnd_932660 141897145843681836195787 := by
  unfold tailWord_932660
  simp only [CollatzResearch.WordTrace]
  refine ⟨17008452400569790245865717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22677936534093053661154289 17008452400569790245865717)
  ·
    refine ⟨1594542412553417835549911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17008452400569790245865717 1594542412553417835549911)
    ·
      refine ⟨2391813618830126753324867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1594542412553417835549911 2391813618830126753324867)
      ·
        refine ⟨3587720428245190129987301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391813618830126753324867 3587720428245190129987301)
        ·
          refine ⟨672697580295973149372619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3587720428245190129987301 672697580295973149372619)
          ·
            refine ⟨1009046370443959724058929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672697580295973149372619 1009046370443959724058929)
            ·
              refine ⟨756784777832969793044197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009046370443959724058929 756784777832969793044197)
              ·
                refine ⟨141897145843681836195787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 756784777832969793044197 141897145843681836195787)
                ·
                  rfl

theorem cell20_932660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_932660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932660 prefixEnd_932660 := by exact prefixLift 932660
  have htrace : WordTrace (prefixWord ++ tailWord_932660) baseStart_932660 baseEnd_932660 := by
    simpa [prefixWord, tailWord_932660, baseEnd_932660] using wordTrace_append hprefix tailTrace_932660
  have hstable : (prefixWord ++ tailWord_932660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932660).length < 2 ^ (prefixWord ++ tailWord_932660).sum := by decide
  have hdescent : baseEnd_932660 < baseStart_932660 := by decide
  rcases family_descends (prefixWord ++ tailWord_932660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932675 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_932675 : Nat := 118140960795 + 932675 * 2 ^ 59
def prefixEnd_932675 : Nat := 4983230072969 + 3 ^ 40 * 932675 * 2
def baseEnd_932675 : Nat := 425698283939772123087299

theorem tailTrace_932675 : CollatzResearch.WordTrace tailWord_932675 prefixEnd_932675 425698283939772123087299 := by
  unfold tailWord_932675
  simp only [CollatzResearch.WordTrace]
  refine ⟨34017451896085238053527479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22678301264056825369018319 34017451896085238053527479)
  ·
    refine ⟨51026177844127857080291219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34017451896085238053527479 51026177844127857080291219)
    ·
      refine ⟨76539266766191785620436829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51026177844127857080291219 76539266766191785620436829)
      ·
        refine ⟨28702225037321919607663811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76539266766191785620436829 28702225037321919607663811)
        ·
          refine ⟨43053337555982879411495717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28702225037321919607663811 43053337555982879411495717)
          ·
            refine ⟨8072500791746789889655447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43053337555982879411495717 8072500791746789889655447)
            ·
              refine ⟨12108751187620184834483171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8072500791746789889655447 12108751187620184834483171)
              ·
                refine ⟨18163126781430277251724757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12108751187620184834483171 18163126781430277251724757)
                ·
                  refine ⟨425698283939772123087299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18163126781430277251724757 425698283939772123087299)
                  ·
                    rfl

theorem cell20_932675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_932675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932675 prefixEnd_932675 := by exact prefixLift 932675
  have htrace : WordTrace (prefixWord ++ tailWord_932675) baseStart_932675 baseEnd_932675 := by
    simpa [prefixWord, tailWord_932675, baseEnd_932675] using wordTrace_append hprefix tailTrace_932675
  have hstable : (prefixWord ++ tailWord_932675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932675).length < 2 ^ (prefixWord ++ tailWord_932675).sum := by decide
  have hdescent : baseEnd_932675 < baseStart_932675 := by decide
  rcases family_descends (prefixWord ++ tailWord_932675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932709 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 3]
def baseStart_932709 : Nat := 118140960795 + 932709 * 2 ^ 59
def prefixEnd_932709 : Nat := 4983230072969 + 3 ^ 40 * 932709 * 2
def baseEnd_932709 : Nat := 425713802466219115953827

theorem tailTrace_932709 : CollatzResearch.WordTrace tailWord_932709 prefixEnd_932709 425713802466219115953827 := by
  unfold tailWord_932709
  simp only [CollatzResearch.WordTrace]
  refine ⟨34018691977962061860265181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22679127985308041240176787 34018691977962061860265181)
  ·
    refine ⟨12757009491735773197599443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34018691977962061860265181 12757009491735773197599443)
    ·
      refine ⟨19135514237603659796399165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12757009491735773197599443 19135514237603659796399165)
      ·
        refine ⟨7175817839101372423649687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19135514237603659796399165 7175817839101372423649687)
        ·
          refine ⟨10763726758652058635474531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7175817839101372423649687 10763726758652058635474531)
          ·
            refine ⟨16145590137978087953211797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10763726758652058635474531 16145590137978087953211797)
            ·
              refine ⟨756824537717722872806803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16145590137978087953211797 756824537717722872806803)
              ·
                refine ⟨1135236806576584309210205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756824537717722872806803 1135236806576584309210205)
                ·
                  refine ⟨425713802466219115953827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135236806576584309210205 425713802466219115953827)
                  ·
                    rfl

theorem cell20_932709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_932709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932709 prefixEnd_932709 := by exact prefixLift 932709
  have htrace : WordTrace (prefixWord ++ tailWord_932709) baseStart_932709 baseEnd_932709 := by
    simpa [prefixWord, tailWord_932709, baseEnd_932709] using wordTrace_append hprefix tailTrace_932709
  have hstable : (prefixWord ++ tailWord_932709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932709).length < 2 ^ (prefixWord ++ tailWord_932709).sum := by decide
  have hdescent : baseEnd_932709 < baseStart_932709 := by decide
  rcases family_descends (prefixWord ++ tailWord_932709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932744 : List Nat := [2, 1, 3, 3, 2, 9]
def baseStart_932744 : Nat := 118140960795 + 932744 * 2 ^ 59
def prefixEnd_932744 : Nat := 4983230072969 + 3 ^ 40 * 932744 * 2
def baseEnd_932744 : Nat := 15767769534070909251371

theorem tailTrace_932744 : CollatzResearch.WordTrace tailWord_932744 prefixEnd_932744 15767769534070909251371 := by
  unfold tailWord_932744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17009984266417631418894643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22679979021890175225192857 17009984266417631418894643)
  ·
    refine ⟨25514976399626447128341965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17009984266417631418894643 25514976399626447128341965)
    ·
      refine ⟨9568116149859917673128237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25514976399626447128341965 9568116149859917673128237)
      ·
        refine ⟨3588043556197469127423089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9568116149859917673128237 3588043556197469127423089)
        ·
          refine ⟨2691032667148101845567317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588043556197469127423089 2691032667148101845567317)
          ·
            refine ⟨15767769534070909251371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2691032667148101845567317 15767769534070909251371)
            ·
              rfl

theorem cell20_932744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 9].length) (baseStart_932744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932744 prefixEnd_932744 := by exact prefixLift 932744
  have htrace : WordTrace (prefixWord ++ tailWord_932744) baseStart_932744 baseEnd_932744 := by
    simpa [prefixWord, tailWord_932744, baseEnd_932744] using wordTrace_append hprefix tailTrace_932744
  have hstable : (prefixWord ++ tailWord_932744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932744).length < 2 ^ (prefixWord ++ tailWord_932744).sum := by decide
  have hdescent : baseEnd_932744 < baseStart_932744 := by decide
  rcases family_descends (prefixWord ++ tailWord_932744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932768 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_932768 : Nat := 118140960795 + 932768 * 2 ^ 59
def prefixEnd_932768 : Nat := 4983230072969 + 3 ^ 40 * 932768 * 2
def baseEnd_932768 : Nat := 425740731673877132986919

theorem tailTrace_932768 : CollatzResearch.WordTrace tailWord_932768 prefixEnd_932768 425740731673877132986919 := by
  unfold tailWord_932768
  simp only [CollatzResearch.WordTrace]
  refine ⟨17010421942374157468331479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22680562589832209957775305 17010421942374157468331479)
  ·
    refine ⟨25515632913561236202497219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17010421942374157468331479 25515632913561236202497219)
    ·
      refine ⟨38273449370341854303745829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25515632913561236202497219 38273449370341854303745829)
      ·
        refine ⟨7176271756939097681952343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38273449370341854303745829 7176271756939097681952343)
        ·
          refine ⟨10764407635408646522928515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7176271756939097681952343 10764407635408646522928515)
          ·
            refine ⟨16146611453112969784392773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10764407635408646522928515 16146611453112969784392773)
            ·
              refine ⟨3027489647458681834573645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16146611453112969784392773 3027489647458681834573645)
              ·
                refine ⟨1135308617797005687965117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3027489647458681834573645 1135308617797005687965117)
                ·
                  refine ⟨425740731673877132986919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135308617797005687965117 425740731673877132986919)
                  ·
                    rfl

theorem cell20_932768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_932768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932768 prefixEnd_932768 := by exact prefixLift 932768
  have htrace : WordTrace (prefixWord ++ tailWord_932768) baseStart_932768 baseEnd_932768 := by
    simpa [prefixWord, tailWord_932768, baseEnd_932768] using wordTrace_append hprefix tailTrace_932768
  have hstable : (prefixWord ++ tailWord_932768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932768).length < 2 ^ (prefixWord ++ tailWord_932768).sum := by decide
  have hdescent : baseEnd_932768 < baseStart_932768 := by decide
  rcases family_descends (prefixWord ++ tailWord_932768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932788 : List Nat := [2, 5, 2, 1, 1, 1, 1, 5, 2]
def baseStart_932788 : Nat := 118140960795 + 932788 * 2 ^ 59
def prefixEnd_932788 : Nat := 4983230072969 + 3 ^ 40 * 932788 * 2
def baseEnd_932788 : Nat := 425749860218845952320171

theorem tailTrace_932788 : CollatzResearch.WordTrace tailWord_932788 prefixEnd_932788 425749860218845952320171 := by
  unfold tailWord_932788
  simp only [CollatzResearch.WordTrace]
  refine ⟨17010786672337929176195509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22681048896450572234927345 17010786672337929176195509)
  ·
    refine ⟨1594761250531680860268329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17010786672337929176195509 1594761250531680860268329)
    ·
      refine ⟨1196070937898760645201247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1594761250531680860268329 1196070937898760645201247)
      ·
        refine ⟨1794106406848140967801871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196070937898760645201247 1794106406848140967801871)
        ·
          refine ⟨2691159610272211451702807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794106406848140967801871 2691159610272211451702807)
          ·
            refine ⟨4036739415408317177554211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691159610272211451702807 4036739415408317177554211)
            ·
              refine ⟨6055109123112475766331317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4036739415408317177554211 6055109123112475766331317)
              ·
                refine ⟨567666480291794603093561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6055109123112475766331317 567666480291794603093561)
                ·
                  refine ⟨425749860218845952320171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567666480291794603093561 425749860218845952320171)
                  ·
                    rfl

theorem cell20_932788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_932788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932788 prefixEnd_932788 := by exact prefixLift 932788
  have htrace : WordTrace (prefixWord ++ tailWord_932788) baseStart_932788 baseEnd_932788 := by
    simpa [prefixWord, tailWord_932788, baseEnd_932788] using wordTrace_append hprefix tailTrace_932788
  have hstable : (prefixWord ++ tailWord_932788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932788).length < 2 ^ (prefixWord ++ tailWord_932788).sum := by decide
  have hdescent : baseEnd_932788 < baseStart_932788 := by decide
  rcases family_descends (prefixWord ++ tailWord_932788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932792 : List Nat := [2, 1, 2, 1, 2, 4, 1, 5, 2]
def baseStart_932792 : Nat := 118140960795 + 932792 * 2 ^ 59
def prefixEnd_932792 : Nat := 4983230072969 + 3 ^ 40 * 932792 * 2
def baseEnd_932792 : Nat := 425751685927839716186821

theorem tailTrace_932792 : CollatzResearch.WordTrace tailWord_932792 prefixEnd_932792 425751685927839716186821 := by
  unfold tailWord_932792
  simp only [CollatzResearch.WordTrace]
  refine ⟨17010859618330683517768315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22681146157774244690357753 17010859618330683517768315)
  ·
    refine ⟨25516289427496025276652473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17010859618330683517768315 25516289427496025276652473)
    ·
      refine ⟨19137217070622018957489355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25516289427496025276652473 19137217070622018957489355)
      ·
        refine ⟨28705825605933028436234033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19137217070622018957489355 28705825605933028436234033)
        ·
          refine ⟨21529369204449771327175525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28705825605933028436234033 21529369204449771327175525)
          ·
            refine ⟨4036756725834332123845411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21529369204449771327175525 4036756725834332123845411)
            ·
              refine ⟨6055135088751498185768117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4036756725834332123845411 6055135088751498185768117)
              ·
                refine ⟨567668914570452954915761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6055135088751498185768117 567668914570452954915761)
                ·
                  refine ⟨425751685927839716186821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567668914570452954915761 425751685927839716186821)
                  ·
                    rfl

theorem cell20_932792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_932792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932792 prefixEnd_932792 := by exact prefixLift 932792
  have htrace : WordTrace (prefixWord ++ tailWord_932792) baseStart_932792 baseEnd_932792 := by
    simpa [prefixWord, tailWord_932792, baseEnd_932792] using wordTrace_append hprefix tailTrace_932792
  have hstable : (prefixWord ++ tailWord_932792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932792).length < 2 ^ (prefixWord ++ tailWord_932792).sum := by decide
  have hdescent : baseEnd_932792 < baseStart_932792 := by decide
  rcases family_descends (prefixWord ++ tailWord_932792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932847 : List Nat := [1, 1, 2, 1, 4, 5, 1, 3, 2]
def baseStart_932847 : Nat := 118140960795 + 932847 * 2 ^ 59
def prefixEnd_932847 : Nat := 4983230072969 + 3 ^ 40 * 932847 * 2
def baseEnd_932847 : Nat := 425776789426503969353263

theorem tailTrace_932847 : CollatzResearch.WordTrace tailWord_932847 prefixEnd_932847 425776789426503969353263 := by
  unfold tailWord_932847
  simp only [CollatzResearch.WordTrace]
  refine ⟨34023725251462111428788795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22682483500974740952525863 34023725251462111428788795)
  ·
    refine ⟨51035587877193167143183193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34023725251462111428788795 51035587877193167143183193)
    ·
      refine ⟨38276690907894875357387395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51035587877193167143183193 38276690907894875357387395)
      ·
        refine ⟨57415036361842313036081093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38276690907894875357387395 57415036361842313036081093)
        ·
          refine ⟨10765319317845433694265205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57415036361842313036081093 10765319317845433694265205)
          ·
            refine ⟨1009248686048009408837363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10765319317845433694265205 1009248686048009408837363)
            ·
              refine ⟨1513873029072014113256045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009248686048009408837363 1513873029072014113256045)
              ·
                refine ⟨567702385902005292471017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1513873029072014113256045 567702385902005292471017)
                ·
                  refine ⟨425776789426503969353263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567702385902005292471017 425776789426503969353263)
                  ·
                    rfl

theorem cell20_932847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 2].length) (baseStart_932847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932847 prefixEnd_932847 := by exact prefixLift 932847
  have htrace : WordTrace (prefixWord ++ tailWord_932847) baseStart_932847 baseEnd_932847 := by
    simpa [prefixWord, tailWord_932847, baseEnd_932847] using wordTrace_append hprefix tailTrace_932847
  have hstable : (prefixWord ++ tailWord_932847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932847).length < 2 ^ (prefixWord ++ tailWord_932847).sum := by decide
  have hdescent : baseEnd_932847 < baseStart_932847 := by decide
  rcases family_descends (prefixWord ++ tailWord_932847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932878 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_932878 : Nat := 118140960795 + 932878 * 2 ^ 59
def prefixEnd_932878 : Nat := 4983230072969 + 3 ^ 40 * 932878 * 2
def baseEnd_932878 : Nat := 425790938671205639319803

theorem tailTrace_932878 : CollatzResearch.WordTrace tailWord_932878 prefixEnd_932878 425790938671205639319803 := by
  unfold tailWord_932878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253106989293725465395911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22683237276233202482111525 4253106989293725465395911)
  ·
    refine ⟨6379660483940588198093867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4253106989293725465395911 6379660483940588198093867)
    ·
      refine ⟨9569490725910882297140801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6379660483940588198093867 9569490725910882297140801)
      ·
        refine ⟨7177118044433161722855601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9569490725910882297140801 7177118044433161722855601)
        ·
          refine ⟨5382838533324871292141701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7177118044433161722855601 5382838533324871292141701)
          ·
            refine ⟨1009282224998413367276569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5382838533324871292141701 1009282224998413367276569)
            ·
              refine ⟨756961668748810025457427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009282224998413367276569 756961668748810025457427)
              ·
                refine ⟨1135442503123215038186141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756961668748810025457427 1135442503123215038186141)
                ·
                  refine ⟨425790938671205639319803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135442503123215038186141 425790938671205639319803)
                  ·
                    rfl

theorem cell20_932878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_932878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932878 prefixEnd_932878 := by exact prefixLift 932878
  have htrace : WordTrace (prefixWord ++ tailWord_932878) baseStart_932878 baseEnd_932878 := by
    simpa [prefixWord, tailWord_932878, baseEnd_932878] using wordTrace_append hprefix tailTrace_932878
  have hstable : (prefixWord ++ tailWord_932878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932878).length < 2 ^ (prefixWord ++ tailWord_932878).sum := by decide
  have hdescent : baseEnd_932878 < baseStart_932878 := by decide
  rcases family_descends (prefixWord ++ tailWord_932878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932916 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_932916 : Nat := 118140960795 + 932916 * 2 ^ 59
def prefixEnd_932916 : Nat := 4983230072969 + 3 ^ 40 * 932916 * 2
def baseEnd_932916 : Nat := 425808282906646396052981

theorem tailTrace_932916 : CollatzResearch.WordTrace tailWord_932916 prefixEnd_932916 425808282906646396052981 := by
  unfold tailWord_932916
  simp only [CollatzResearch.WordTrace]
  refine ⟨17013120944106068106525301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22684161258808090808700401 17013120944106068106525301)
  ·
    refine ⟨1594980088509943884986747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17013120944106068106525301 1594980088509943884986747)
    ·
      refine ⟨2392470132764915827480121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1594980088509943884986747 2392470132764915827480121)
      ·
        refine ⟨1794352599573686870610091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2392470132764915827480121 1794352599573686870610091)
        ·
          refine ⟨2691528899360530305915137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794352599573686870610091 2691528899360530305915137)
          ·
            refine ⟨2018646674520397729436353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2691528899360530305915137 2018646674520397729436353)
            ·
              refine ⟨1513985005890298297077265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2018646674520397729436353 1513985005890298297077265)
              ·
                refine ⟨1135488754417723722807949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513985005890298297077265 1135488754417723722807949)
                ·
                  refine ⟨425808282906646396052981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135488754417723722807949 425808282906646396052981)
                  ·
                    rfl

theorem cell20_932916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_932916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932916 prefixEnd_932916 := by exact prefixLift 932916
  have htrace : WordTrace (prefixWord ++ tailWord_932916) baseStart_932916 baseEnd_932916 := by
    simpa [prefixWord, tailWord_932916, baseEnd_932916] using wordTrace_append hprefix tailTrace_932916
  have hstable : (prefixWord ++ tailWord_932916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932916).length < 2 ^ (prefixWord ++ tailWord_932916).sum := by decide
  have hdescent : baseEnd_932916 < baseStart_932916 := by decide
  rcases family_descends (prefixWord ++ tailWord_932916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932920 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_932920 : Nat := 118140960795 + 932920 * 2 ^ 59
def prefixEnd_932920 : Nat := 4983230072969 + 3 ^ 40 * 932920 * 2
def baseEnd_932920 : Nat := 425810108615640159919631

theorem tailTrace_932920 : CollatzResearch.WordTrace tailWord_932920 prefixEnd_932920 425810108615640159919631 := by
  unfold tailWord_932920
  simp only [CollatzResearch.WordTrace]
  refine ⟨17013193890098822448098107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22684258520131763264130809 17013193890098822448098107)
  ·
    refine ⟨25519790835148233672147161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17013193890098822448098107 25519790835148233672147161)
    ·
      refine ⟨19139843126361175254110371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25519790835148233672147161 19139843126361175254110371)
      ·
        refine ⟨28709764689541762881165557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19139843126361175254110371 28709764689541762881165557)
        ·
          refine ⟨2691540439644540270109271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28709764689541762881165557 2691540439644540270109271)
          ·
            refine ⟨4037310659466810405163907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691540439644540270109271 4037310659466810405163907)
            ·
              refine ⟨6055965989200215607745861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037310659466810405163907 6055965989200215607745861)
              ·
                refine ⟨1135493622975040426452349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6055965989200215607745861 1135493622975040426452349)
                ·
                  refine ⟨425810108615640159919631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135493622975040426452349 425810108615640159919631)
                  ·
                    rfl

theorem cell20_932920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_932920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932920 prefixEnd_932920 := by exact prefixLift 932920
  have htrace : WordTrace (prefixWord ++ tailWord_932920) baseStart_932920 baseEnd_932920 := by
    simpa [prefixWord, tailWord_932920, baseEnd_932920] using wordTrace_append hprefix tailTrace_932920
  have hstable : (prefixWord ++ tailWord_932920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932920).length < 2 ^ (prefixWord ++ tailWord_932920).sum := by decide
  have hdescent : baseEnd_932920 < baseStart_932920 := by decide
  rcases family_descends (prefixWord ++ tailWord_932920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932982 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_932982 : Nat := 118140960795 + 932982 * 2 ^ 59
def prefixEnd_932982 : Nat := 4983230072969 + 3 ^ 40 * 932982 * 2
def baseEnd_932982 : Nat := 425838407105043499852711

theorem tailTrace_932982 : CollatzResearch.WordTrace tailWord_932982 prefixEnd_932982 425838407105043499852711 := by
  unfold tailWord_932982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126790569123314342809575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22685766070648686323302133 2126790569123314342809575)
  ·
    refine ⟨3190185853684971514214363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2126790569123314342809575 3190185853684971514214363)
    ·
      refine ⟨4785278780527457271321545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190185853684971514214363 4785278780527457271321545)
      ·
        refine ⟨3588959085395592953491159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4785278780527457271321545 3588959085395592953491159)
        ·
          refine ⟨5383438628093389430236739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588959085395592953491159 5383438628093389430236739)
          ·
            refine ⟨8075157942140084145355109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383438628093389430236739 8075157942140084145355109)
            ·
              refine ⟨1514092114151265777254083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8075157942140084145355109 1514092114151265777254083)
              ·
                refine ⟨2271138171226898665881125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514092114151265777254083 2271138171226898665881125)
                ·
                  refine ⟨425838407105043499852711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271138171226898665881125 425838407105043499852711)
                  ·
                    rfl

theorem cell20_932982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_932982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_932982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_932982 prefixEnd_932982 := by exact prefixLift 932982
  have htrace : WordTrace (prefixWord ++ tailWord_932982) baseStart_932982 baseEnd_932982 := by
    simpa [prefixWord, tailWord_932982, baseEnd_932982] using wordTrace_append hprefix tailTrace_932982
  have hstable : (prefixWord ++ tailWord_932982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932982).length < 2 ^ (prefixWord ++ tailWord_932982).sum := by decide
  have hdescent : baseEnd_932982 < baseStart_932982 := by decide
  rcases family_descends (prefixWord ++ tailWord_932982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933006 : List Nat := [4, 1, 1, 3, 2, 3, 2, 4]
def baseStart_933006 : Nat := 118140960795 + 933006 * 2 ^ 59
def prefixEnd_933006 : Nat := 4983230072969 + 3 ^ 40 * 933006 * 2
def baseEnd_933006 : Nat := 141949787119668694350871

theorem tailTrace_933006 : CollatzResearch.WordTrace tailWord_933006 prefixEnd_933006 141949787119668694350871 := by
  unfold tailWord_933006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253690557235760197978359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22686349638590721055884581 4253690557235760197978359)
  ·
    refine ⟨6380535835853640296967539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4253690557235760197978359 6380535835853640296967539)
    ·
      refine ⟨9570803753780460445451309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6380535835853640296967539 9570803753780460445451309)
      ·
        refine ⟨3589051407667672667044241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9570803753780460445451309 3589051407667672667044241)
        ·
          refine ⟨2691788555750754500283181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3589051407667672667044241 2691788555750754500283181)
          ·
            refine ⟨1009420708406532937606193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2691788555750754500283181 1009420708406532937606193)
            ·
              refine ⟨757065531304899703204645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009420708406532937606193 757065531304899703204645)
              ·
                refine ⟨141949787119668694350871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 757065531304899703204645 141949787119668694350871)
                ·
                  rfl

theorem cell20_933006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_933006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933006 prefixEnd_933006 := by exact prefixLift 933006
  have htrace : WordTrace (prefixWord ++ tailWord_933006) baseStart_933006 baseEnd_933006 := by
    simpa [prefixWord, tailWord_933006, baseEnd_933006] using wordTrace_append hprefix tailTrace_933006
  have hstable : (prefixWord ++ tailWord_933006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933006).length < 2 ^ (prefixWord ++ tailWord_933006).sum := by decide
  have hdescent : baseEnd_933006 < baseStart_933006 := by decide
  rcases family_descends (prefixWord ++ tailWord_933006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933037 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 4]
def baseStart_933037 : Nat := 118140960795 + 933037 * 2 ^ 59
def prefixEnd_933037 : Nat := 4983230072969 + 3 ^ 40 * 933037 * 2
def baseEnd_933037 : Nat := 425863510603707753019153

theorem tailTrace_933037 : CollatzResearch.WordTrace tailWord_933037 prefixEnd_933037 425863510603707753019153 := by
  unfold tailWord_933037
  simp only [CollatzResearch.WordTrace]
  refine ⟨34030655120773773878205365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22687103413849182585470243 34030655120773773878205365)
  ·
    refine ⟨3190373917572541301081753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34030655120773773878205365 3190373917572541301081753)
    ·
      refine ⟨2392780438179405975811315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3190373917572541301081753 2392780438179405975811315)
      ·
        refine ⟨3589170657269108963716973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392780438179405975811315 3589170657269108963716973)
        ·
          refine ⟨1345938996475915861393865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3589170657269108963716973 1345938996475915861393865)
          ·
            refine ⟨1009454247356936896045399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1345938996475915861393865 1009454247356936896045399)
            ·
              refine ⟨1514181371035405344068099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009454247356936896045399 1514181371035405344068099)
              ·
                refine ⟨2271272056553108016102149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514181371035405344068099 2271272056553108016102149)
                ·
                  refine ⟨425863510603707753019153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271272056553108016102149 425863510603707753019153)
                  ·
                    rfl

theorem cell20_933037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_933037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933037 prefixEnd_933037 := by exact prefixLift 933037
  have htrace : WordTrace (prefixWord ++ tailWord_933037) baseStart_933037 baseEnd_933037 := by
    simpa [prefixWord, tailWord_933037, baseEnd_933037] using wordTrace_append hprefix tailTrace_933037
  have hstable : (prefixWord ++ tailWord_933037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933037).length < 2 ^ (prefixWord ++ tailWord_933037).sum := by decide
  have hdescent : baseEnd_933037 < baseStart_933037 := by decide
  rcases family_descends (prefixWord ++ tailWord_933037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933096 : List Nat := [2, 1, 4, 1, 2, 1, 3, 4, 2]
def baseStart_933096 : Nat := 118140960795 + 933096 * 2 ^ 59
def prefixEnd_933096 : Nat := 4983230072969 + 3 ^ 40 * 933096 * 2
def baseEnd_933096 : Nat := 425890439811365770052245

theorem tailTrace_933096 : CollatzResearch.WordTrace tailWord_933096 prefixEnd_933096 425890439811365770052245 := by
  unfold tailWord_933096
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016403513780013477301571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22688538018373351303068761 17016403513780013477301571)
  ·
    refine ⟨25524605270670020215952357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17016403513780013477301571 25524605270670020215952357)
    ·
      refine ⟨4785863488250628790491067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25524605270670020215952357 4785863488250628790491067)
      ·
        refine ⟨7178795232375943185736601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785863488250628790491067 7178795232375943185736601)
        ·
          refine ⟨5384096424281957389302451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7178795232375943185736601 5384096424281957389302451)
          ·
            refine ⟨8076144636422936083953677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5384096424281957389302451 8076144636422936083953677)
            ·
              refine ⟨3028554238658601031482629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8076144636422936083953677 3028554238658601031482629)
              ·
                refine ⟨567853919748487693402993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3028554238658601031482629 567853919748487693402993)
                ·
                  refine ⟨425890439811365770052245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567853919748487693402993 425890439811365770052245)
                  ·
                    rfl

theorem cell20_933096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_933096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933096 prefixEnd_933096 := by exact prefixLift 933096
  have htrace : WordTrace (prefixWord ++ tailWord_933096) baseStart_933096 baseEnd_933096 := by
    simpa [prefixWord, tailWord_933096, baseEnd_933096] using wordTrace_append hprefix tailTrace_933096
  have hstable : (prefixWord ++ tailWord_933096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933096).length < 2 ^ (prefixWord ++ tailWord_933096).sum := by decide
  have hdescent : baseEnd_933096 < baseStart_933096 := by decide
  rcases family_descends (prefixWord ++ tailWord_933096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933103 : List Nat := [1, 1, 2, 1, 7, 2, 1, 5]
def baseStart_933103 : Nat := 118140960795 + 933103 * 2 ^ 59
def prefixEnd_933103 : Nat := 4983230072969 + 3 ^ 40 * 933103 * 2
def baseEnd_933103 : Nat := 141964544934034952272961

theorem tailTrace_933103 : CollatzResearch.WordTrace tailWord_933103 prefixEnd_933103 141964544934034952272961 := by
  unfold tailWord_933103
  simp only [CollatzResearch.WordTrace]
  refine ⟨34033062338534667150107963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22688708225689778100071975 34033062338534667150107963)
  ·
    refine ⟨51049593507802000725161945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34033062338534667150107963 51049593507802000725161945)
    ·
      refine ⟨38287195130851500543871459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51049593507802000725161945 38287195130851500543871459)
      ·
        refine ⟨57430792696277250815807189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38287195130851500543871459 57430792696277250815807189)
        ·
          refine ⟨1346034203818998065995481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 57430792696277250815807189 1346034203818998065995481)
          ·
            refine ⟨1009525652864248549496611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346034203818998065995481 1009525652864248549496611)
            ·
              refine ⟨1514288479296372824244917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009525652864248549496611 1514288479296372824244917)
              ·
                refine ⟨141964544934034952272961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1514288479296372824244917 141964544934034952272961)
                ·
                  rfl

theorem cell20_933103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 5].length) (baseStart_933103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933103 prefixEnd_933103 := by exact prefixLift 933103
  have htrace : WordTrace (prefixWord ++ tailWord_933103) baseStart_933103 baseEnd_933103 := by
    simpa [prefixWord, tailWord_933103, baseEnd_933103] using wordTrace_append hprefix tailTrace_933103
  have hstable : (prefixWord ++ tailWord_933103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933103).length < 2 ^ (prefixWord ++ tailWord_933103).sum := by decide
  have hdescent : baseEnd_933103 < baseStart_933103 := by decide
  rcases family_descends (prefixWord ++ tailWord_933103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933134 : List Nat := [4, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_933134 : Nat := 118140960795 + 933134 * 2 ^ 59
def prefixEnd_933134 : Nat := 4983230072969 + 3 ^ 40 * 933134 * 2
def baseEnd_933134 : Nat := 425907784046806526785423

theorem tailTrace_933134 : CollatzResearch.WordTrace tailWord_933134 prefixEnd_933134 425907784046806526785423 := by
  unfold tailWord_933134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4254274125177794930560807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22689462000948239629657637 4254274125177794930560807)
  ·
    refine ⟨6381411187766692395841211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4254274125177794930560807 6381411187766692395841211)
    ·
      refine ⟨9572116781650038593761817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6381411187766692395841211 9572116781650038593761817)
      ·
        refine ⟨7179087586237528945321363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9572116781650038593761817 7179087586237528945321363)
        ·
          refine ⟨10768631379356293417982045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179087586237528945321363 10768631379356293417982045)
          ·
            refine ⟨4038236767258610031743267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10768631379356293417982045 4038236767258610031743267)
            ·
              refine ⟨6057355150887915047614901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4038236767258610031743267 6057355150887915047614901)
              ·
                refine ⟨567877045395742035713897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6057355150887915047614901 567877045395742035713897)
                ·
                  refine ⟨425907784046806526785423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567877045395742035713897 425907784046806526785423)
                  ·
                    rfl

theorem cell20_933134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_933134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933134 prefixEnd_933134 := by exact prefixLift 933134
  have htrace : WordTrace (prefixWord ++ tailWord_933134) baseStart_933134 baseEnd_933134 := by
    simpa [prefixWord, tailWord_933134, baseEnd_933134] using wordTrace_append hprefix tailTrace_933134
  have hstable : (prefixWord ++ tailWord_933134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933134).length < 2 ^ (prefixWord ++ tailWord_933134).sum := by decide
  have hdescent : baseEnd_933134 < baseStart_933134 := by decide
  rcases family_descends (prefixWord ++ tailWord_933134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933148 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_933148 : Nat := 118140960795 + 933148 * 2 ^ 59
def prefixEnd_933148 : Nat := 4983230072969 + 3 ^ 40 * 933148 * 2
def baseEnd_933148 : Nat := 425914174028284700318699

theorem tailTrace_933148 : CollatzResearch.WordTrace tailWord_933148 prefixEnd_933148 425914174028284700318699 := by
  unfold tailWord_933148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17017351811685819917748049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22689802415581093223664065 17017351811685819917748049)
  ·
    refine ⟨12763013858764364938311037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17017351811685819917748049 12763013858764364938311037)
    ·
      refine ⟨4786130197036636851866639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12763013858764364938311037 4786130197036636851866639)
      ·
        refine ⟨7179195295554955277799959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4786130197036636851866639 7179195295554955277799959)
        ·
          refine ⟨10768792943332432916699939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179195295554955277799959 10768792943332432916699939)
          ·
            refine ⟨16153189414998649375049909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10768792943332432916699939 16153189414998649375049909)
            ·
              refine ⟨1514361507656123378910929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16153189414998649375049909 1514361507656123378910929)
              ·
                refine ⟨1135771130742092534183197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514361507656123378910929 1135771130742092534183197)
                ·
                  refine ⟨425914174028284700318699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135771130742092534183197 425914174028284700318699)
                  ·
                    rfl

theorem cell20_933148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_933148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933148 prefixEnd_933148 := by exact prefixLift 933148
  have htrace : WordTrace (prefixWord ++ tailWord_933148) baseStart_933148 baseEnd_933148 := by
    simpa [prefixWord, tailWord_933148, baseEnd_933148] using wordTrace_append hprefix tailTrace_933148
  have hstable : (prefixWord ++ tailWord_933148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933148).length < 2 ^ (prefixWord ++ tailWord_933148).sum := by decide
  have hdescent : baseEnd_933148 < baseStart_933148 := by decide
  rcases family_descends (prefixWord ++ tailWord_933148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933155 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_933155 : Nat := 118140960795 + 933155 * 2 ^ 59
def prefixEnd_933155 : Nat := 4983230072969 + 3 ^ 40 * 933155 * 2
def baseEnd_933155 : Nat := 425917369019023787085337

theorem tailTrace_933155 : CollatzResearch.WordTrace tailWord_933155 prefixEnd_933155 425917369019023787085337 := by
  unfold tailWord_933155
  simp only [CollatzResearch.WordTrace]
  refine ⟨34034958934346280031000919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22689972622897520020667279 34034958934346280031000919)
  ·
    refine ⟨51052438401519420046501379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34034958934346280031000919 51052438401519420046501379)
    ·
      refine ⟨76578657602279130069752069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51052438401519420046501379 76578657602279130069752069)
      ·
        refine ⟨14358498300427336888078513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76578657602279130069752069 14358498300427336888078513)
        ·
          refine ⟨10768873725320502666058885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14358498300427336888078513 10768873725320502666058885)
          ·
            refine ⟨2019163823497594249886041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10768873725320502666058885 2019163823497594249886041)
            ·
              refine ⟨1514372867623195687414531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019163823497594249886041 1514372867623195687414531)
              ·
                refine ⟨2271559301434793531121797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514372867623195687414531 2271559301434793531121797)
                ·
                  refine ⟨425917369019023787085337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271559301434793531121797 425917369019023787085337)
                  ·
                    rfl

theorem cell20_933155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_933155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933155 prefixEnd_933155 := by exact prefixLift 933155
  have htrace : WordTrace (prefixWord ++ tailWord_933155) baseStart_933155 baseEnd_933155 := by
    simpa [prefixWord, tailWord_933155, baseEnd_933155] using wordTrace_append hprefix tailTrace_933155
  have hstable : (prefixWord ++ tailWord_933155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933155).length < 2 ^ (prefixWord ++ tailWord_933155).sum := by decide
  have hdescent : baseEnd_933155 < baseStart_933155 := by decide
  rcases family_descends (prefixWord ++ tailWord_933155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933207 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_933207 : Nat := 118140960795 + 933207 * 2 ^ 59
def prefixEnd_933207 : Nat := 4983230072969 + 3 ^ 40 * 933207 * 2
def baseEnd_933207 : Nat := 425941103235942717351791

theorem tailTrace_933207 : CollatzResearch.WordTrace tailWord_933207 prefixEnd_933207 425941103235942717351791 := by
  unfold tailWord_933207
  simp only [CollatzResearch.WordTrace]
  refine ⟨34036855530157892911893875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22691237020105261941262583 34036855530157892911893875)
  ·
    refine ⟨51055283295236839367840813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34036855530157892911893875 51055283295236839367840813)
    ·
      refine ⟨19145731235713814762940305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51055283295236839367840813 19145731235713814762940305)
      ·
        refine ⟨14359298426785361072205229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19145731235713814762940305 14359298426785361072205229)
        ·
          refine ⟨5384736910044510402076961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14359298426785361072205229 5384736910044510402076961)
          ·
            refine ⟨4038552682533382801557721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5384736910044510402076961 4038552682533382801557721)
            ·
              refine ⟨3028914511900037101168291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038552682533382801557721 3028914511900037101168291)
              ·
                refine ⟨4543371767850055651752437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028914511900037101168291 4543371767850055651752437)
                ·
                  refine ⟨425941103235942717351791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4543371767850055651752437 425941103235942717351791)
                  ·
                    rfl

theorem cell20_933207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_933207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933207 prefixEnd_933207 := by exact prefixLift 933207
  have htrace : WordTrace (prefixWord ++ tailWord_933207) baseStart_933207 baseEnd_933207 := by
    simpa [prefixWord, tailWord_933207, baseEnd_933207] using wordTrace_append hprefix tailTrace_933207
  have hstable : (prefixWord ++ tailWord_933207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933207).length < 2 ^ (prefixWord ++ tailWord_933207).sum := by decide
  have hdescent : baseEnd_933207 < baseStart_933207 := by decide
  rcases family_descends (prefixWord ++ tailWord_933207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933213 : List Nat := [1, 4, 5, 1, 1, 1, 2, 5]
def baseStart_933213 : Nat := 118140960795 + 933213 * 2 ^ 59
def prefixEnd_933213 : Nat := 4983230072969 + 3 ^ 40 * 933213 * 2
def baseEnd_933213 : Nat := 141981280599811121050589

theorem tailTrace_933213 : CollatzResearch.WordTrace tailWord_933213 prefixEnd_933213 141981280599811121050589 := by
  unfold tailWord_933213
  simp only [CollatzResearch.WordTrace]
  refine ⟨34037074368136155936612293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22691382912090770624408195 34037074368136155936612293)
  ·
    refine ⟨6381951444025529238114805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34037074368136155936612293 6381951444025529238114805)
    ·
      refine ⟨598307947877393366073263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6381951444025529238114805 598307947877393366073263)
      ·
        refine ⟨897461921816090049109895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598307947877393366073263 897461921816090049109895)
        ·
          refine ⟨1346192882724135073664843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897461921816090049109895 1346192882724135073664843)
          ·
            refine ⟨2019289324086202610497265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346192882724135073664843 2019289324086202610497265)
            ·
              refine ⟨1514466993064651957872949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019289324086202610497265 1514466993064651957872949)
              ·
                refine ⟨141981280599811121050589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1514466993064651957872949 141981280599811121050589)
                ·
                  rfl

theorem cell20_933213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 5].length) (baseStart_933213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933213 prefixEnd_933213 := by exact prefixLift 933213
  have htrace : WordTrace (prefixWord ++ tailWord_933213) baseStart_933213 baseEnd_933213 := by
    simpa [prefixWord, tailWord_933213, baseEnd_933213] using wordTrace_append hprefix tailTrace_933213
  have hstable : (prefixWord ++ tailWord_933213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933213).length < 2 ^ (prefixWord ++ tailWord_933213).sum := by decide
  have hdescent : baseEnd_933213 < baseStart_933213 := by decide
  rcases family_descends (prefixWord ++ tailWord_933213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933272 : List Nat := [2, 1, 2, 5, 3, 1, 1, 5]
def baseStart_933272 : Nat := 118140960795 + 933272 * 2 ^ 59
def prefixEnd_933272 : Nat := 4983230072969 + 3 ^ 40 * 933272 * 2
def baseEnd_933272 : Nat := 141990257002363793394953

theorem tailTrace_933272 : CollatzResearch.WordTrace tailWord_933272 prefixEnd_933272 141990257002363793394953 := by
  unfold tailWord_933272
  simp only [CollatzResearch.WordTrace]
  refine ⟨17019613137461204506505035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22692817516614939342006713 17019613137461204506505035)
  ·
    refine ⟨25529419706191806759757553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17019613137461204506505035 25529419706191806759757553)
    ·
      refine ⟨19147064779643855069818165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25529419706191806759757553 19147064779643855069818165)
      ·
        refine ⟨1795037323091611412795453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19147064779643855069818165 1795037323091611412795453)
        ·
          refine ⟨673138996159354279798295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1795037323091611412795453 673138996159354279798295)
          ·
            refine ⟨1009708494239031419697443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673138996159354279798295 1009708494239031419697443)
            ·
              refine ⟨1514562741358547129546165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009708494239031419697443 1514562741358547129546165)
              ·
                refine ⟨141990257002363793394953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1514562741358547129546165 141990257002363793394953)
                ·
                  rfl

theorem cell20_933272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_933272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933272 prefixEnd_933272 := by exact prefixLift 933272
  have htrace : WordTrace (prefixWord ++ tailWord_933272) baseStart_933272 baseEnd_933272 := by
    simpa [prefixWord, tailWord_933272, baseEnd_933272] using wordTrace_append hprefix tailTrace_933272
  have hstable : (prefixWord ++ tailWord_933272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933272).length < 2 ^ (prefixWord ++ tailWord_933272).sum := by decide
  have hdescent : baseEnd_933272 < baseStart_933272 := by decide
  rcases family_descends (prefixWord ++ tailWord_933272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933283 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 3]
def baseStart_933283 : Nat := 118140960795 + 933283 * 2 ^ 59
def prefixEnd_933283 : Nat := 4983230072969 + 3 ^ 40 * 933283 * 2
def baseEnd_933283 : Nat := 425975791706824230818147

theorem tailTrace_933283 : CollatzResearch.WordTrace tailWord_933283 prefixEnd_933283 425975791706824230818147 := by
  unfold tailWord_933283
  simp only [CollatzResearch.WordTrace]
  refine ⟨34039627477882557891660503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22693084985255038594440335 34039627477882557891660503)
  ·
    refine ⟨51059441216823836837490755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34039627477882557891660503 51059441216823836837490755)
    ·
      refine ⟨76589161825235755256236133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51059441216823836837490755 76589161825235755256236133)
      ·
        refine ⟨14360467842231704110544275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76589161825235755256236133 14360467842231704110544275)
        ·
          refine ⟨21540701763347556165816413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14360467842231704110544275 21540701763347556165816413)
          ·
            refine ⟨8077763161255333562181155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21540701763347556165816413 8077763161255333562181155)
            ·
              refine ⟨12116644741883000343271733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077763161255333562181155 12116644741883000343271733)
              ·
                refine ⟨1135935444551531282181725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12116644741883000343271733 1135935444551531282181725)
                ·
                  refine ⟨425975791706824230818147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135935444551531282181725 425975791706824230818147)
                  ·
                    rfl

theorem cell20_933283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_933283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933283 prefixEnd_933283 := by exact prefixLift 933283
  have htrace : WordTrace (prefixWord ++ tailWord_933283) baseStart_933283 baseEnd_933283 := by
    simpa [prefixWord, tailWord_933283, baseEnd_933283] using wordTrace_append hprefix tailTrace_933283
  have hstable : (prefixWord ++ tailWord_933283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933283).length < 2 ^ (prefixWord ++ tailWord_933283).sum := by decide
  have hdescent : baseEnd_933283 < baseStart_933283 := by decide
  rcases family_descends (prefixWord ++ tailWord_933283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933324 : List Nat := [2, 2, 1, 4, 2, 1, 2, 4, 2]
def baseStart_933324 : Nat := 118140960795 + 933324 * 2 ^ 59
def prefixEnd_933324 : Nat := 4983230072969 + 3 ^ 40 * 933324 * 2
def baseEnd_933324 : Nat := 425994505224010310451313

theorem tailTrace_933324 : CollatzResearch.WordTrace tailWord_933324 prefixEnd_933324 425994505224010310451313 := by
  unfold tailWord_933324
  simp only [CollatzResearch.WordTrace]
  refine ⟨17020561435367010946951513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22694081913822681262602017 17020561435367010946951513)
  ·
    refine ⟨12765421076525258210213635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17020561435367010946951513 12765421076525258210213635)
    ·
      refine ⟨19148131614787887315320453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12765421076525258210213635 19148131614787887315320453)
      ·
        refine ⟨3590274677772728871622585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19148131614787887315320453 3590274677772728871622585)
        ·
          refine ⟨2692706008329546653716939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590274677772728871622585 2692706008329546653716939)
          ·
            refine ⟨4039059012494319980575409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692706008329546653716939 4039059012494319980575409)
            ·
              refine ⟨3029294259370739985431557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4039059012494319980575409 3029294259370739985431557)
              ·
                refine ⟨567992673632013747268417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3029294259370739985431557 567992673632013747268417)
                ·
                  refine ⟨425994505224010310451313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567992673632013747268417 425994505224010310451313)
                  ·
                    rfl

theorem cell20_933324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_933324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933324 prefixEnd_933324 := by exact prefixLift 933324
  have htrace : WordTrace (prefixWord ++ tailWord_933324) baseStart_933324 baseEnd_933324 := by
    simpa [prefixWord, tailWord_933324, baseEnd_933324] using wordTrace_append hprefix tailTrace_933324
  have hstable : (prefixWord ++ tailWord_933324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933324).length < 2 ^ (prefixWord ++ tailWord_933324).sum := by decide
  have hdescent : baseEnd_933324 < baseStart_933324 := by decide
  rcases family_descends (prefixWord ++ tailWord_933324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933334 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_933334 : Nat := 118140960795 + 933334 * 2 ^ 59
def prefixEnd_933334 : Nat := 4983230072969 + 3 ^ 40 * 933334 * 2
def baseEnd_933334 : Nat := 425999069496494720117939

theorem tailTrace_933334 : CollatzResearch.WordTrace tailWord_933334 prefixEnd_933334 425999069496494720117939 := by
  unfold tailWord_933334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127592975043612100110441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22694325067131862401178037 2127592975043612100110441)
  ·
    refine ⟨1595694731282709075082831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2127592975043612100110441 1595694731282709075082831)
    ·
      refine ⟨2393542096924063612624247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1595694731282709075082831 2393542096924063612624247)
      ·
        refine ⟨3590313145386095418936371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393542096924063612624247 3590313145386095418936371)
        ·
          refine ⟨5385469718079143128404557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590313145386095418936371 5385469718079143128404557)
          ·
            refine ⟨2019551144279678673151709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5385469718079143128404557 2019551144279678673151709)
            ·
              refine ⟨757331679104879502431891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2019551144279678673151709 757331679104879502431891)
              ·
                refine ⟨1135997518657319253647837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757331679104879502431891 1135997518657319253647837)
                ·
                  refine ⟨425999069496494720117939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135997518657319253647837 425999069496494720117939)
                  ·
                    rfl

theorem cell20_933334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_933334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933334 prefixEnd_933334 := by exact prefixLift 933334
  have htrace : WordTrace (prefixWord ++ tailWord_933334) baseStart_933334 baseEnd_933334 := by
    simpa [prefixWord, tailWord_933334, baseEnd_933334] using wordTrace_append hprefix tailTrace_933334
  have hstable : (prefixWord ++ tailWord_933334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933334).length < 2 ^ (prefixWord ++ tailWord_933334).sum := by decide
  have hdescent : baseEnd_933334 < baseStart_933334 := by decide
  rcases family_descends (prefixWord ++ tailWord_933334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933373 : List Nat := [1, 4, 1, 1, 1, 4, 8]
def baseStart_933373 : Nat := 118140960795 + 933373 * 2 ^ 59
def prefixEnd_933373 : Nat := 4983230072969 + 3 ^ 40 * 933373 * 2
def baseEnd_933373 : Nat := 47335207795464879757531

theorem tailTrace_933373 : CollatzResearch.WordTrace tailWord_933373 prefixEnd_933373 47335207795464879757531 := by
  unfold tailWord_933373
  simp only [CollatzResearch.WordTrace]
  refine ⟨34042910047556503262436773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22695273365037668841624515 34042910047556503262436773)
  ·
    refine ⟨6383045633916844361706895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34042910047556503262436773 6383045633916844361706895)
    ·
      refine ⟨9574568450875266542560343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383045633916844361706895 9574568450875266542560343)
      ·
        refine ⟨14361852676312899813840515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9574568450875266542560343 14361852676312899813840515)
        ·
          refine ⟨21542779014469349720760773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14361852676312899813840515 21542779014469349720760773)
          ·
            refine ⟨4039271065213003072642645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21542779014469349720760773 4039271065213003072642645)
            ·
              refine ⟨47335207795464879757531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4039271065213003072642645 47335207795464879757531)
              ·
                rfl

theorem cell20_933373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 8].length) (baseStart_933373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933373 prefixEnd_933373 := by exact prefixLift 933373
  have htrace : WordTrace (prefixWord ++ tailWord_933373) baseStart_933373 baseEnd_933373 := by
    simpa [prefixWord, tailWord_933373, baseEnd_933373] using wordTrace_append hprefix tailTrace_933373
  have hstable : (prefixWord ++ tailWord_933373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933373).length < 2 ^ (prefixWord ++ tailWord_933373).sum := by decide
  have hdescent : baseEnd_933373 < baseStart_933373 := by decide
  rcases family_descends (prefixWord ++ tailWord_933373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933383 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_933383 : Nat := 118140960795 + 933383 * 2 ^ 59
def prefixEnd_933383 : Nat := 4983230072969 + 3 ^ 40 * 933383 * 2
def baseEnd_933383 : Nat := 426021434431668327484405

theorem tailTrace_933383 : CollatzResearch.WordTrace tailWord_933383 prefixEnd_933383 426021434431668327484405 := by
  unfold tailWord_933383
  simp only [CollatzResearch.WordTrace]
  refine ⟨34043274777520274970300803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22695516518346849980200535 34043274777520274970300803)
  ·
    refine ⟨51064912166280412455451205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34043274777520274970300803 51064912166280412455451205)
    ·
      refine ⟨9574671031177577335397101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51064912166280412455451205 9574671031177577335397101)
      ·
        refine ⟨3590501636691591500773913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9574671031177577335397101 3590501636691591500773913)
        ·
          refine ⟨2692876227518693625580435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590501636691591500773913 2692876227518693625580435)
          ·
            refine ⟨4039314341278040438370653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692876227518693625580435 4039314341278040438370653)
            ·
              refine ⟨1514742877979265164388995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4039314341278040438370653 1514742877979265164388995)
              ·
                refine ⟨2272114316968897746583493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514742877979265164388995 2272114316968897746583493)
                ·
                  refine ⟨426021434431668327484405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2272114316968897746583493 426021434431668327484405)
                  ·
                    rfl

theorem cell20_933383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_933383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933383 prefixEnd_933383 := by exact prefixLift 933383
  have htrace : WordTrace (prefixWord ++ tailWord_933383) baseStart_933383 baseEnd_933383 := by
    simpa [prefixWord, tailWord_933383, baseEnd_933383] using wordTrace_append hprefix tailTrace_933383
  have hstable : (prefixWord ++ tailWord_933383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933383).length < 2 ^ (prefixWord ++ tailWord_933383).sum := by decide
  have hdescent : baseEnd_933383 < baseStart_933383 := by decide
  rcases family_descends (prefixWord ++ tailWord_933383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933404 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_933404 : Nat := 118140960795 + 933404 * 2 ^ 59
def prefixEnd_933404 : Nat := 4983230072969 + 3 ^ 40 * 933404 * 2
def baseEnd_933404 : Nat := 426031019403885587784319

theorem tailTrace_933404 : CollatzResearch.WordTrace tailWord_933404 prefixEnd_933404 426031019403885587784319 := by
  unfold tailWord_933404
  simp only [CollatzResearch.WordTrace]
  refine ⟨17022020355222097778407633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22696027140296130371210177 17022020355222097778407633)
  ·
    refine ⟨12766515266416573333805725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17022020355222097778407633 12766515266416573333805725)
    ·
      refine ⟨4787443224906215000177147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12766515266416573333805725 4787443224906215000177147)
      ·
        refine ⟨7181164837359322500265721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787443224906215000177147 7181164837359322500265721)
        ·
          refine ⟨5385873628019491875199291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7181164837359322500265721 5385873628019491875199291)
          ·
            refine ⟨8078810442029237812798937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385873628019491875199291 8078810442029237812798937)
            ·
              refine ⟨6059107831521928359599203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8078810442029237812798937 6059107831521928359599203)
              ·
                refine ⟨9088661747282892539398805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059107831521928359599203 9088661747282892539398805)
                ·
                  refine ⟨426031019403885587784319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9088661747282892539398805 426031019403885587784319)
                  ·
                    rfl

theorem cell20_933404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_933404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933404 prefixEnd_933404 := by exact prefixLift 933404
  have htrace : WordTrace (prefixWord ++ tailWord_933404) baseStart_933404 baseEnd_933404 := by
    simpa [prefixWord, tailWord_933404, baseEnd_933404] using wordTrace_append hprefix tailTrace_933404
  have hstable : (prefixWord ++ tailWord_933404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933404).length < 2 ^ (prefixWord ++ tailWord_933404).sum := by decide
  have hdescent : baseEnd_933404 < baseStart_933404 := by decide
  rcases family_descends (prefixWord ++ tailWord_933404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933476 : List Nat := [2, 3, 1, 1, 2, 4, 2, 3, 2]
def baseStart_933476 : Nat := 118140960795 + 933476 * 2 ^ 59
def prefixEnd_933476 : Nat := 4983230072969 + 3 ^ 40 * 933476 * 2
def baseEnd_933476 : Nat := 426063882165773337384025

theorem tailTrace_933476 : CollatzResearch.WordTrace tailWord_933476 prefixEnd_933476 426063882165773337384025 := by
  unfold tailWord_933476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17023333383091675926718141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22697777844122234568957521 17023333383091675926718141)
  ·
    refine ⟨6383750018659378472519303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17023333383091675926718141 6383750018659378472519303)
    ·
      refine ⟨9575625027989067708778955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383750018659378472519303 9575625027989067708778955)
      ·
        refine ⟨14363437541983601563168433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9575625027989067708778955 14363437541983601563168433)
        ·
          refine ⟨10772578156487701172376325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14363437541983601563168433 10772578156487701172376325)
          ·
            refine ⟨2019858404341443969820561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10772578156487701172376325 2019858404341443969820561)
            ·
              refine ⟨1514893803256082977365421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019858404341443969820561 1514893803256082977365421)
              ·
                refine ⟨568085176221031116512033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1514893803256082977365421 568085176221031116512033)
                ·
                  refine ⟨426063882165773337384025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568085176221031116512033 426063882165773337384025)
                  ·
                    rfl

theorem cell20_933476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_933476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933476 prefixEnd_933476 := by exact prefixLift 933476
  have htrace : WordTrace (prefixWord ++ tailWord_933476) baseStart_933476 baseEnd_933476 := by
    simpa [prefixWord, tailWord_933476, baseEnd_933476] using wordTrace_append hprefix tailTrace_933476
  have hstable : (prefixWord ++ tailWord_933476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933476).length < 2 ^ (prefixWord ++ tailWord_933476).sum := by decide
  have hdescent : baseEnd_933476 < baseStart_933476 := by decide
  rcases family_descends (prefixWord ++ tailWord_933476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933486 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_933486 : Nat := 118140960795 + 933486 * 2 ^ 59
def prefixEnd_933486 : Nat := 4983230072969 + 3 ^ 40 * 933486 * 2
def baseEnd_933486 : Nat := 426068446438257747050651

theorem tailTrace_933486 : CollatzResearch.WordTrace tailWord_933486 prefixEnd_933486 426068446438257747050651 := by
  unfold tailWord_933486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255878937018390445162539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22698020997431415707533541 4255878937018390445162539)
  ·
    refine ⟨6383818405527585667743809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4255878937018390445162539 6383818405527585667743809)
    ·
      refine ⟨4787863804145689250807857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6383818405527585667743809 4787863804145689250807857)
      ·
        refine ⟨3590897853109266938105893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4787863804145689250807857 3590897853109266938105893)
        ·
          refine ⟨673293347457987550894855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3590897853109266938105893 673293347457987550894855)
          ·
            refine ⟨1009940021186981326342283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673293347457987550894855 1009940021186981326342283)
            ·
              refine ⟨1514910031780471989513425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009940021186981326342283 1514910031780471989513425)
              ·
                refine ⟨1136182523835353992135069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514910031780471989513425 1136182523835353992135069)
                ·
                  refine ⟨426068446438257747050651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136182523835353992135069 426068446438257747050651)
                  ·
                    rfl

theorem cell20_933486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_933486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933486 prefixEnd_933486 := by exact prefixLift 933486
  have htrace : WordTrace (prefixWord ++ tailWord_933486) baseStart_933486 baseEnd_933486 := by
    simpa [prefixWord, tailWord_933486, baseEnd_933486] using wordTrace_append hprefix tailTrace_933486
  have hstable : (prefixWord ++ tailWord_933486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933486).length < 2 ^ (prefixWord ++ tailWord_933486).sum := by decide
  have hdescent : baseEnd_933486 < baseStart_933486 := by decide
  rcases family_descends (prefixWord ++ tailWord_933486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933490 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_933490 : Nat := 118140960795 + 933490 * 2 ^ 59
def prefixEnd_933490 : Nat := 4983230072969 + 3 ^ 40 * 933490 * 2
def baseEnd_933490 : Nat := 426070272147251510917301

theorem tailTrace_933490 : CollatzResearch.WordTrace tailWord_933490 prefixEnd_933490 426070272147251510917301 := by
  unfold tailWord_933490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511794347033158061111481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22698118258755088162963949 8511794347033158061111481)
  ·
    refine ⟨6383845760274868545833611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8511794347033158061111481 6383845760274868545833611)
    ·
      refine ⟨9575768640412302818750417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383845760274868545833611 9575768640412302818750417)
      ·
        refine ⟨7181826480309227114062813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9575768640412302818750417 7181826480309227114062813)
        ·
          refine ⟨2693184930115960167773555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7181826480309227114062813 2693184930115960167773555)
          ·
            refine ⟨4039777395173940251660333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693184930115960167773555 4039777395173940251660333)
            ·
              refine ⟨1514916523190227594372625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4039777395173940251660333 1514916523190227594372625)
              ·
                refine ⟨1136187392392670695779469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514916523190227594372625 1136187392392670695779469)
                ·
                  refine ⟨426070272147251510917301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136187392392670695779469 426070272147251510917301)
                  ·
                    rfl

theorem cell20_933490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_933490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933490 prefixEnd_933490 := by exact prefixLift 933490
  have htrace : WordTrace (prefixWord ++ tailWord_933490) baseStart_933490 baseEnd_933490 := by
    simpa [prefixWord, tailWord_933490, baseEnd_933490] using wordTrace_append hprefix tailTrace_933490
  have hstable : (prefixWord ++ tailWord_933490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933490).length < 2 ^ (prefixWord ++ tailWord_933490).sum := by decide
  have hdescent : baseEnd_933490 < baseStart_933490 := by decide
  rcases family_descends (prefixWord ++ tailWord_933490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933497 : List Nat := [1, 2, 1, 3, 3, 1, 1, 6, 2]
def baseStart_933497 : Nat := 118140960795 + 933497 * 2 ^ 59
def prefixEnd_933497 : Nat := 4983230072969 + 3 ^ 40 * 933497 * 2
def baseEnd_933497 : Nat := 426073467137990597683939

theorem tailTrace_933497 : CollatzResearch.WordTrace tailWord_933497 prefixEnd_933497 426073467137990597683939 := by
  unfold tailWord_933497
  simp only [CollatzResearch.WordTrace]
  refine ⟨34047432699107272439950745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22698288466071514959967163 34047432699107272439950745)
  ·
    refine ⟨25535574524330454329963059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34047432699107272439950745 25535574524330454329963059)
    ·
      refine ⟨38303361786495681494944589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25535574524330454329963059 38303361786495681494944589)
      ·
        refine ⟨14363760669935880560604221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38303361786495681494944589 14363760669935880560604221)
        ·
          refine ⟨5386410251225955210226583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14363760669935880560604221 5386410251225955210226583)
          ·
            refine ⟨8079615376838932815339875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386410251225955210226583 8079615376838932815339875)
            ·
              refine ⟨12119423065258399223009813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8079615376838932815339875 12119423065258399223009813)
              ·
                refine ⟨568097956183987463578585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12119423065258399223009813 568097956183987463578585)
                ·
                  refine ⟨426073467137990597683939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568097956183987463578585 426073467137990597683939)
                  ·
                    rfl

theorem cell20_933497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_933497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933497 prefixEnd_933497 := by exact prefixLift 933497
  have htrace : WordTrace (prefixWord ++ tailWord_933497) baseStart_933497 baseEnd_933497 := by
    simpa [prefixWord, tailWord_933497, baseEnd_933497] using wordTrace_append hprefix tailTrace_933497
  have hstable : (prefixWord ++ tailWord_933497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933497).length < 2 ^ (prefixWord ++ tailWord_933497).sum := by decide
  have hdescent : baseEnd_933497 < baseStart_933497 := by decide
  rcases family_descends (prefixWord ++ tailWord_933497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933538 : List Nat := [3, 3, 1, 4, 2, 1, 6]
def baseStart_933538 : Nat := 118140960795 + 933538 * 2 ^ 59
def prefixEnd_933538 : Nat := 4983230072969 + 3 ^ 40 * 933538 * 2
def baseEnd_933538 : Nat := 47343575628352964146345

theorem tailTrace_933538 : CollatzResearch.WordTrace tailWord_933538 prefixEnd_933538 47343575628352964146345 := by
  unfold tailWord_933538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512232022989684110548317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22699285394639157628128845 8512232022989684110548317)
  ·
    refine ⟨3192087008621131541455619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8512232022989684110548317 3192087008621131541455619)
    ·
      refine ⟨4788130512931697312183429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192087008621131541455619 4788130512931697312183429)
      ·
        refine ⟨897774471174693246034393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4788130512931697312183429 897774471174693246034393)
        ·
          refine ⟨673330853381019934525795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897774471174693246034393 673330853381019934525795)
          ·
            refine ⟨1009996280071529901788693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673330853381019934525795 1009996280071529901788693)
            ·
              refine ⟨47343575628352964146345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1009996280071529901788693 47343575628352964146345)
              ·
                rfl

theorem cell20_933538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 6].length) (baseStart_933538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933538 prefixEnd_933538 := by exact prefixLift 933538
  have htrace : WordTrace (prefixWord ++ tailWord_933538) baseStart_933538 baseEnd_933538 := by
    simpa [prefixWord, tailWord_933538, baseEnd_933538] using wordTrace_append hprefix tailTrace_933538
  have hstable : (prefixWord ++ tailWord_933538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933538).length < 2 ^ (prefixWord ++ tailWord_933538).sum := by decide
  have hdescent : baseEnd_933538 < baseStart_933538 := by decide
  rcases family_descends (prefixWord ++ tailWord_933538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933549 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_933549 : Nat := 118140960795 + 933549 * 2 ^ 59
def prefixEnd_933549 : Nat := 4983230072969 + 3 ^ 40 * 933549 * 2
def baseEnd_933549 : Nat := 426097201354909527950393

theorem tailTrace_933549 : CollatzResearch.WordTrace tailWord_933549 prefixEnd_933549 426097201354909527950393 := by
  unfold tailWord_933549
  simp only [CollatzResearch.WordTrace]
  refine ⟨34049329294918885320843701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22699552863279256880562467 34049329294918885320843701)
  ·
    refine ⟨3192124621398645498829097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34049329294918885320843701 3192124621398645498829097)
    ·
      refine ⟨2394093466048984124121823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3192124621398645498829097 2394093466048984124121823)
      ·
        refine ⟨3591140199073476186182735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394093466048984124121823 3591140199073476186182735)
        ·
          refine ⟨5386710298610214279274103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591140199073476186182735 5386710298610214279274103)
          ·
            refine ⟨8080065447915321418911155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386710298610214279274103 8080065447915321418911155)
            ·
              refine ⟨12120098171872982128366733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8080065447915321418911155 12120098171872982128366733)
              ·
                refine ⟨4545036814452368298137525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12120098171872982128366733 4545036814452368298137525)
                ·
                  refine ⟨426097201354909527950393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4545036814452368298137525 426097201354909527950393)
                  ·
                    rfl

theorem cell20_933549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_933549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933549 prefixEnd_933549 := by exact prefixLift 933549
  have htrace : WordTrace (prefixWord ++ tailWord_933549) baseStart_933549 baseEnd_933549 := by
    simpa [prefixWord, tailWord_933549, baseEnd_933549] using wordTrace_append hprefix tailTrace_933549
  have hstable : (prefixWord ++ tailWord_933549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933549).length < 2 ^ (prefixWord ++ tailWord_933549).sum := by decide
  have hdescent : baseEnd_933549 < baseStart_933549 := by decide
  rcases family_descends (prefixWord ++ tailWord_933549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933566 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_933566 : Nat := 118140960795 + 933566 * 2 ^ 59
def prefixEnd_933566 : Nat := 4983230072969 + 3 ^ 40 * 933566 * 2
def baseEnd_933566 : Nat := 426104960618133024383657

theorem tailTrace_933566 : CollatzResearch.WordTrace tailWord_933566 prefixEnd_933566 426104960618133024383657 := by
  unfold tailWord_933566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256243666982162153026569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22699966223904864816141701 4256243666982162153026569)
  ·
    refine ⟨3192182750236621614769927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4256243666982162153026569 3192182750236621614769927)
    ·
      refine ⟨4788274125354932422154891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192182750236621614769927 4788274125354932422154891)
      ·
        refine ⟨7182411188032398633232337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4788274125354932422154891 7182411188032398633232337)
        ·
          refine ⟨5386808391024298974924253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7182411188032398633232337 5386808391024298974924253)
          ·
            refine ⟨2020053146634112115596595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5386808391024298974924253 2020053146634112115596595)
            ·
              refine ⟨3030079719951168173394893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020053146634112115596595 3030079719951168173394893)
              ·
                refine ⟨1136279894981688065023085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3030079719951168173394893 1136279894981688065023085)
                ·
                  refine ⟨426104960618133024383657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136279894981688065023085 426104960618133024383657)
                  ·
                    rfl

theorem cell20_933566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_933566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933566 prefixEnd_933566 := by exact prefixLift 933566
  have htrace : WordTrace (prefixWord ++ tailWord_933566) baseStart_933566 baseEnd_933566 := by
    simpa [prefixWord, tailWord_933566, baseEnd_933566] using wordTrace_append hprefix tailTrace_933566
  have hstable : (prefixWord ++ tailWord_933566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933566).length < 2 ^ (prefixWord ++ tailWord_933566).sum := by decide
  have hdescent : baseEnd_933566 < baseStart_933566 := by decide
  rcases family_descends (prefixWord ++ tailWord_933566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933597 : List Nat := [1, 4, 3, 3, 2, 7]
def baseStart_933597 : Nat := 118140960795 + 933597 * 2 ^ 59
def prefixEnd_933597 : Nat := 4983230072969 + 3 ^ 40 * 933597 * 2
def baseEnd_933597 : Nat := 15782189254179062753711

theorem tailTrace_933597 : CollatzResearch.WordTrace tailWord_933597 prefixEnd_933597 15782189254179062753711 := by
  unfold tailWord_933597
  simp only [CollatzResearch.WordTrace]
  refine ⟨34051079998744989518591045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22700719999163326345727363 34051079998744989518591045)
  ·
    refine ⟨6384577499764685534735821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34051079998744989518591045 6384577499764685534735821)
    ·
      refine ⟨2394216562411757075525933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6384577499764685534735821 2394216562411757075525933)
      ·
        refine ⟨897831210904408903322225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2394216562411757075525933 897831210904408903322225)
        ·
          refine ⟨673373408178306677491669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897831210904408903322225 673373408178306677491669)
          ·
            refine ⟨15782189254179062753711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 673373408178306677491669 15782189254179062753711)
            ·
              rfl

theorem cell20_933597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 7].length) (baseStart_933597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933597 prefixEnd_933597 := by exact prefixLift 933597
  have htrace : WordTrace (prefixWord ++ tailWord_933597) baseStart_933597 baseEnd_933597 := by
    simpa [prefixWord, tailWord_933597, baseEnd_933597] using wordTrace_append hprefix tailTrace_933597
  have hstable : (prefixWord ++ tailWord_933597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933597).length < 2 ^ (prefixWord ++ tailWord_933597).sum := by decide
  have hdescent : baseEnd_933597 < baseStart_933597 := by decide
  rcases family_descends (prefixWord ++ tailWord_933597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933601 : List Nat := [1, 2, 3, 1, 5, 8]
def baseStart_933601 : Nat := 118140960795 + 933601 * 2 ^ 59
def prefixEnd_933601 : Nat := 4983230072969 + 3 ^ 40 * 933601 * 2
def baseEnd_933601 : Nat := 15782256873030683637661

theorem tailTrace_933601 : CollatzResearch.WordTrace tailWord_933601 prefixEnd_933601 15782256873030683637661 := by
  unfold tailWord_933601
  simp only [CollatzResearch.WordTrace]
  refine ⟨34051225890730498201736657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22700817260486998801157771 34051225890730498201736657)
  ·
    refine ⟨25538419418047873651302493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34051225890730498201736657 25538419418047873651302493)
    ·
      refine ⟨9576907281767952619238435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25538419418047873651302493 9576907281767952619238435)
      ·
        refine ⟨14365360922651928928857653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9576907281767952619238435 14365360922651928928857653)
        ·
          refine ⟨1346752586498618337080405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14365360922651928928857653 1346752586498618337080405)
          ·
            refine ⟨15782256873030683637661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1346752586498618337080405 15782256873030683637661)
            ·
              rfl

theorem cell20_933601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 8].length) (baseStart_933601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933601 prefixEnd_933601 := by exact prefixLift 933601
  have htrace : WordTrace (prefixWord ++ tailWord_933601) baseStart_933601 baseEnd_933601 := by
    simpa [prefixWord, tailWord_933601, baseEnd_933601] using wordTrace_append hprefix tailTrace_933601
  have hstable : (prefixWord ++ tailWord_933601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933601).length < 2 ^ (prefixWord ++ tailWord_933601).sum := by decide
  have hdescent : baseEnd_933601 < baseStart_933601 := by decide
  rcases family_descends (prefixWord ++ tailWord_933601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933607 : List Nat := [1, 1, 5, 4, 1, 1, 1, 4, 2]
def baseStart_933607 : Nat := 118140960795 + 933607 * 2 ^ 59
def prefixEnd_933607 : Nat := 4983230072969 + 3 ^ 40 * 933607 * 2
def baseEnd_933607 : Nat := 426123674135319104016823

theorem tailTrace_933607 : CollatzResearch.WordTrace tailWord_933607 prefixEnd_933607 426123674135319104016823 := by
  unfold tailWord_933607
  simp only [CollatzResearch.WordTrace]
  refine ⟨34051444728708761226455075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22700963152472507484303383 34051444728708761226455075)
  ·
    refine ⟨51077167093063141839682613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34051444728708761226455075 51077167093063141839682613)
    ·
      refine ⟨4788484414974669547470245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51077167093063141839682613 4788484414974669547470245)
      ·
        refine ⟨897840827807750540150671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4788484414974669547470245 897840827807750540150671)
        ·
          refine ⟨1346761241711625810226007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897840827807750540150671 1346761241711625810226007)
          ·
            refine ⟨2020141862567438715339011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346761241711625810226007 2020141862567438715339011)
            ·
              refine ⟨3030212793851158073008517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020141862567438715339011 3030212793851158073008517)
              ·
                refine ⟨568164898847092138689097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3030212793851158073008517 568164898847092138689097)
                ·
                  refine ⟨426123674135319104016823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568164898847092138689097 426123674135319104016823)
                  ·
                    rfl

theorem cell20_933607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 2].length) (baseStart_933607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933607 prefixEnd_933607 := by exact prefixLift 933607
  have htrace : WordTrace (prefixWord ++ tailWord_933607) baseStart_933607 baseEnd_933607 := by
    simpa [prefixWord, tailWord_933607, baseEnd_933607] using wordTrace_append hprefix tailTrace_933607
  have hstable : (prefixWord ++ tailWord_933607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933607).length < 2 ^ (prefixWord ++ tailWord_933607).sum := by decide
  have hdescent : baseEnd_933607 < baseStart_933607 := by decide
  rcases family_descends (prefixWord ++ tailWord_933607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933652 : List Nat := [2, 4, 4, 1, 1, 1, 7]
def baseStart_933652 : Nat := 118140960795 + 933652 * 2 ^ 59
def prefixEnd_933652 : Nat := 4983230072969 + 3 ^ 40 * 933652 * 2
def baseEnd_933652 : Nat := 47349357040166549724071

theorem tailTrace_933652 : CollatzResearch.WordTrace tailWord_933652 prefixEnd_933652 47349357040166549724071 := by
  unfold tailWord_933652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17026543006772866955921605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22702057342363822607895473 17026543006772866955921605)
  ·
    refine ⟨3192476813769912554235301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17026543006772866955921605 3192476813769912554235301)
    ·
      refine ⟨598589402581858603919119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3192476813769912554235301 598589402581858603919119)
      ·
        refine ⟨897884103872787905878679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598589402581858603919119 897884103872787905878679)
        ·
          refine ⟨1346826155809181858818019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897884103872787905878679 1346826155809181858818019)
          ·
            refine ⟨2020239233713772788227029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346826155809181858818019 2020239233713772788227029)
            ·
              refine ⟨47349357040166549724071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2020239233713772788227029 47349357040166549724071)
              ·
                rfl

theorem cell20_933652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 7].length) (baseStart_933652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933652 prefixEnd_933652 := by exact prefixLift 933652
  have htrace : WordTrace (prefixWord ++ tailWord_933652) baseStart_933652 baseEnd_933652 := by
    simpa [prefixWord, tailWord_933652, baseEnd_933652] using wordTrace_append hprefix tailTrace_933652
  have hstable : (prefixWord ++ tailWord_933652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933652).length < 2 ^ (prefixWord ++ tailWord_933652).sum := by decide
  have hdescent : baseEnd_933652 < baseStart_933652 := by decide
  rcases family_descends (prefixWord ++ tailWord_933652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933694 : List Nat := [4, 2, 1, 2, 2, 2, 1, 6]
def baseStart_933694 : Nat := 118140960795 + 933694 * 2 ^ 59
def prefixEnd_933694 : Nat := 4983230072969 + 3 ^ 40 * 933694 * 2
def baseEnd_933694 : Nat := 142054461101977822705489

theorem tailTrace_933694 : CollatzResearch.WordTrace tailWord_933694 prefixEnd_933694 142054461101977822705489 := by
  unfold tailWord_933694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256827234924196885609017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22703078586262383389914757 4256827234924196885609017)
  ·
    refine ⟨3192620426193147664206763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4256827234924196885609017 3192620426193147664206763)
    ·
      refine ⟨4788930639289721496310145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192620426193147664206763 4788930639289721496310145)
      ·
        refine ⟨3591697979467291122232609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4788930639289721496310145 3591697979467291122232609)
        ·
          refine ⟨2693773484600468341674457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3591697979467291122232609 2693773484600468341674457)
          ·
            refine ⟨2020330113450351256255843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2693773484600468341674457 2020330113450351256255843)
            ·
              refine ⟨3030495170175526884383765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020330113450351256255843 3030495170175526884383765)
              ·
                refine ⟨142054461101977822705489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3030495170175526884383765 142054461101977822705489)
                ·
                  rfl

theorem cell20_933694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_933694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933694 prefixEnd_933694 := by exact prefixLift 933694
  have htrace : WordTrace (prefixWord ++ tailWord_933694) baseStart_933694 baseEnd_933694 := by
    simpa [prefixWord, tailWord_933694, baseEnd_933694] using wordTrace_append hprefix tailTrace_933694
  have hstable : (prefixWord ++ tailWord_933694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933694).length < 2 ^ (prefixWord ++ tailWord_933694).sum := by decide
  have hdescent : baseEnd_933694 < baseStart_933694 := by decide
  rcases family_descends (prefixWord ++ tailWord_933694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933704 : List Nat := [2, 1, 3, 1, 1, 6, 1, 3, 2]
def baseStart_933704 : Nat := 118140960795 + 933704 * 2 ^ 59
def prefixEnd_933704 : Nat := 4983230072969 + 3 ^ 40 * 933704 * 2
def baseEnd_933704 : Nat := 426167947578417877783093

theorem tailTrace_933704 : CollatzResearch.WordTrace tailWord_933704 prefixEnd_933704 426167947578417877783093 := by
  unfold tailWord_933704
  simp only [CollatzResearch.WordTrace]
  refine ⟨17027491304678673396368083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22703321739571564528490777 17027491304678673396368083)
  ·
    refine ⟨25541236957018010094552125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17027491304678673396368083 25541236957018010094552125)
    ·
      refine ⟨9577963858881753785457047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25541236957018010094552125 9577963858881753785457047)
      ·
        refine ⟨14366945788322630678185571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9577963858881753785457047 14366945788322630678185571)
        ·
          refine ⟨21550418682483946017278357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14366945788322630678185571 21550418682483946017278357)
          ·
            refine ⟨1010175875741434969559923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21550418682483946017278357 1010175875741434969559923)
            ·
              refine ⟨1515263813612152454339885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010175875741434969559923 1515263813612152454339885)
              ·
                refine ⟨568223930104557170377457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1515263813612152454339885 568223930104557170377457)
                ·
                  refine ⟨426167947578417877783093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568223930104557170377457 426167947578417877783093)
                  ·
                    rfl

theorem cell20_933704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_933704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933704 prefixEnd_933704 := by exact prefixLift 933704
  have htrace : WordTrace (prefixWord ++ tailWord_933704) baseStart_933704 baseEnd_933704 := by
    simpa [prefixWord, tailWord_933704, baseEnd_933704] using wordTrace_append hprefix tailTrace_933704
  have hstable : (prefixWord ++ tailWord_933704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933704).length < 2 ^ (prefixWord ++ tailWord_933704).sum := by decide
  have hdescent : baseEnd_933704 < baseStart_933704 := by decide
  rcases family_descends (prefixWord ++ tailWord_933704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933722 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_933722 : Nat := 118140960795 + 933722 * 2 ^ 59
def prefixEnd_933722 : Nat := 4983230072969 + 3 ^ 40 * 933722 * 2
def baseEnd_933722 : Nat := 426176163268889815183019

theorem tailTrace_933722 : CollatzResearch.WordTrace tailWord_933722 prefixEnd_933722 426176163268889815183019 := by
  unfold tailWord_933722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8513909780823033966722855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22703759415528090577927613 8513909780823033966722855)
  ·
    refine ⟨12770864671234550950084283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8513909780823033966722855 12770864671234550950084283)
    ·
      refine ⟨19156297006851826425126425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12770864671234550950084283 19156297006851826425126425)
      ·
        refine ⟨14367222755138869818844819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19156297006851826425126425 14367222755138869818844819)
        ·
          refine ⟨21550834132708304728267229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14367222755138869818844819 21550834132708304728267229)
          ·
            refine ⟨8081562799765614273100211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21550834132708304728267229 8081562799765614273100211)
            ·
              refine ⟨12122344199648421409650317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8081562799765614273100211 12122344199648421409650317)
              ·
                refine ⟨4545879074868158028618869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12122344199648421409650317 4545879074868158028618869)
                ·
                  refine ⟨426176163268889815183019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4545879074868158028618869 426176163268889815183019)
                  ·
                    rfl

theorem cell20_933722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_933722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933722 prefixEnd_933722 := by exact prefixLift 933722
  have htrace : WordTrace (prefixWord ++ tailWord_933722) baseStart_933722 baseEnd_933722 := by
    simpa [prefixWord, tailWord_933722, baseEnd_933722] using wordTrace_append hprefix tailTrace_933722
  have hstable : (prefixWord ++ tailWord_933722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933722).length < 2 ^ (prefixWord ++ tailWord_933722).sum := by decide
  have hdescent : baseEnd_933722 < baseStart_933722 := by decide
  rcases family_descends (prefixWord ++ tailWord_933722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933732 : List Nat := [2, 3, 1, 1, 5, 1, 2, 5]
def baseStart_933732 : Nat := 118140960795 + 933732 * 2 ^ 59
def prefixEnd_933732 : Nat := 4983230072969 + 3 ^ 40 * 933732 * 2
def baseEnd_933732 : Nat := 142060242513791408283215

theorem tailTrace_933732 : CollatzResearch.WordTrace tailWord_933732 prefixEnd_933732 142060242513791408283215 := by
  unfold tailWord_933732
  simp only [CollatzResearch.WordTrace]
  refine ⟨17028001926627953787377725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22704002568837271716503633 17028001926627953787377725)
  ·
    refine ⟨6385500722485482670266647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17028001926627953787377725 6385500722485482670266647)
    ·
      refine ⟨9578251083728224005399971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6385500722485482670266647 9578251083728224005399971)
      ·
        refine ⟨14367376625592336008099957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9578251083728224005399971 14367376625592336008099957)
        ·
          refine ⟨1346941558649281500759371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14367376625592336008099957 1346941558649281500759371)
          ·
            refine ⟨2020412337973922251139057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346941558649281500759371 2020412337973922251139057)
            ·
              refine ⟨1515309253480441688354293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2020412337973922251139057 1515309253480441688354293)
              ·
                refine ⟨142060242513791408283215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1515309253480441688354293 142060242513791408283215)
                ·
                  rfl

theorem cell20_933732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_933732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933732 prefixEnd_933732 := by exact prefixLift 933732
  have htrace : WordTrace (prefixWord ++ tailWord_933732) baseStart_933732 baseEnd_933732 := by
    simpa [prefixWord, tailWord_933732, baseEnd_933732] using wordTrace_append hprefix tailTrace_933732
  have hstable : (prefixWord ++ tailWord_933732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933732).length < 2 ^ (prefixWord ++ tailWord_933732).sum := by decide
  have hdescent : baseEnd_933732 < baseStart_933732 := by decide
  rcases family_descends (prefixWord ++ tailWord_933732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933770 : List Nat := [3, 1, 2, 4, 3, 7]
def baseStart_933770 : Nat := 118140960795 + 933770 * 2 ^ 59
def prefixEnd_933770 : Nat := 4983230072969 + 3 ^ 40 * 933770 * 2
def baseEnd_933770 : Nat := 15785113769511665984549

theorem tailTrace_933770 : CollatzResearch.WordTrace tailWord_933770 prefixEnd_933770 15785113769511665984549 := by
  unfold tailWord_933770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514347456779560016159691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22704926551412160043092509 8514347456779560016159691)
  ·
    refine ⟨12771521185169340024239537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8514347456779560016159691 12771521185169340024239537)
    ·
      refine ⟨9578640888877005018179653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12771521185169340024239537 9578640888877005018179653)
      ·
        refine ⟨1795995166664438440908685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9578640888877005018179653 1795995166664438440908685)
        ·
          refine ⟨673498187499164415340757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1795995166664438440908685 673498187499164415340757)
          ·
            refine ⟨15785113769511665984549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 673498187499164415340757 15785113769511665984549)
            ·
              rfl

theorem cell20_933770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 7].length) (baseStart_933770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933770 prefixEnd_933770 := by exact prefixLift 933770
  have htrace : WordTrace (prefixWord ++ tailWord_933770) baseStart_933770 baseEnd_933770 := by
    simpa [prefixWord, tailWord_933770, baseEnd_933770] using wordTrace_append hprefix tailTrace_933770
  have hstable : (prefixWord ++ tailWord_933770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933770).length < 2 ^ (prefixWord ++ tailWord_933770).sum := by decide
  have hdescent : baseEnd_933770 < baseStart_933770 := by decide
  rcases family_descends (prefixWord ++ tailWord_933770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933780 : List Nat := [2, 4, 2, 1, 1, 3, 1, 4, 2]
def baseStart_933780 : Nat := 118140960795 + 933780 * 2 ^ 59
def prefixEnd_933780 : Nat := 4983230072969 + 3 ^ 40 * 933780 * 2
def baseEnd_933780 : Nat := 426202636049299391249449

theorem tailTrace_933780 : CollatzResearch.WordTrace tailWord_933780 prefixEnd_933780 426202636049299391249449 := by
  unfold tailWord_933780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17028877278541005886251397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22705169704721341181668529 17028877278541005886251397)
  ·
    refine ⟨3192914489726438603672137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17028877278541005886251397 3192914489726438603672137)
    ·
      refine ⟨2394685867294828952754103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3192914489726438603672137 2394685867294828952754103)
      ·
        refine ⟨3592028800942243429131155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394685867294828952754103 3592028800942243429131155)
        ·
          refine ⟨5388043201413365143696733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3592028800942243429131155 5388043201413365143696733)
          ·
            refine ⟨2020516200530011928886275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5388043201413365143696733 2020516200530011928886275)
            ·
              refine ⟨3030774300795017893329413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020516200530011928886275 3030774300795017893329413)
              ·
                refine ⟨568270181399065854999265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3030774300795017893329413 568270181399065854999265)
                ·
                  refine ⟨426202636049299391249449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568270181399065854999265 426202636049299391249449)
                  ·
                    rfl

theorem cell20_933780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_933780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933780 prefixEnd_933780 := by exact prefixLift 933780
  have htrace : WordTrace (prefixWord ++ tailWord_933780) baseStart_933780 baseEnd_933780 := by
    simpa [prefixWord, tailWord_933780, baseEnd_933780] using wordTrace_append hprefix tailTrace_933780
  have hstable : (prefixWord ++ tailWord_933780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933780).length < 2 ^ (prefixWord ++ tailWord_933780).sum := by decide
  have hdescent : baseEnd_933780 < baseStart_933780 := by decide
  rcases family_descends (prefixWord ++ tailWord_933780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933832 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 3]
def baseStart_933832 : Nat := 118140960795 + 933832 * 2 ^ 59
def prefixEnd_933832 : Nat := 4983230072969 + 3 ^ 40 * 933832 * 2
def baseEnd_933832 : Nat := 426226370266218321515903

theorem tailTrace_933832 : CollatzResearch.WordTrace tailWord_933832 prefixEnd_933832 426226370266218321515903 := by
  unfold tailWord_933832
  simp only [CollatzResearch.WordTrace]
  refine ⟨17029825576446812326697875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22706434101929083102263833 17029825576446812326697875)
  ·
    refine ⟨25544738364670218490046813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17029825576446812326697875 25544738364670218490046813)
    ·
      refine ⟨9579276886751331933767555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25544738364670218490046813 9579276886751331933767555)
      ·
        refine ⟨14368915330126997900651333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9579276886751331933767555 14368915330126997900651333)
        ·
          refine ⟨2694171624398812106372125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14368915330126997900651333 2694171624398812106372125)
          ·
            refine ⟨1010314359149554539889547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2694171624398812106372125 1010314359149554539889547)
            ·
              refine ⟨1515471538724331809834321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010314359149554539889547 1515471538724331809834321)
              ·
                refine ⟨1136603654043248857375741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515471538724331809834321 1136603654043248857375741)
                ·
                  refine ⟨426226370266218321515903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136603654043248857375741 426226370266218321515903)
                  ·
                    rfl

theorem cell20_933832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_933832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933832 prefixEnd_933832 := by exact prefixLift 933832
  have htrace : WordTrace (prefixWord ++ tailWord_933832) baseStart_933832 baseEnd_933832 := by
    simpa [prefixWord, tailWord_933832, baseEnd_933832] using wordTrace_append hprefix tailTrace_933832
  have hstable : (prefixWord ++ tailWord_933832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933832).length < 2 ^ (prefixWord ++ tailWord_933832).sum := by decide
  have hdescent : baseEnd_933832 < baseStart_933832 := by decide
  rcases family_descends (prefixWord ++ tailWord_933832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933863 : List Nat := [1, 1, 5, 2, 3, 2, 2, 4]
def baseStart_933863 : Nat := 118140960795 + 933863 * 2 ^ 59
def prefixEnd_933863 : Nat := 4983230072969 + 3 ^ 40 * 933863 * 2
def baseEnd_933863 : Nat := 142080173170306663827481

theorem tailTrace_933863 : CollatzResearch.WordTrace tailWord_933863 prefixEnd_933863 142080173170306663827481 := by
  unfold tailWord_933863
  simp only [CollatzResearch.WordTrace]
  refine ⟨34060781815781316947774243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22707187877187544631849495 34060781815781316947774243)
  ·
    refine ⟨51091172723671975421661365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34060781815781316947774243 51091172723671975421661365)
    ·
      refine ⟨4789797442844247695780753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51091172723671975421661365 4789797442844247695780753)
      ·
        refine ⟨3592348082133185771835565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4789797442844247695780753 3592348082133185771835565)
        ·
          refine ⟨1347130530799944664438337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3592348082133185771835565 1347130530799944664438337)
          ·
            refine ⟨1010347898099958498328753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347130530799944664438337 1010347898099958498328753)
            ·
              refine ⟨757760923574968873746565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010347898099958498328753 757760923574968873746565)
              ·
                refine ⟨142080173170306663827481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 757760923574968873746565 142080173170306663827481)
                ·
                  rfl

theorem cell20_933863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 4].length) (baseStart_933863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933863 prefixEnd_933863 := by exact prefixLift 933863
  have htrace : WordTrace (prefixWord ++ tailWord_933863) baseStart_933863 baseEnd_933863 := by
    simpa [prefixWord, tailWord_933863, baseEnd_933863] using wordTrace_append hprefix tailTrace_933863
  have hstable : (prefixWord ++ tailWord_933863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933863).length < 2 ^ (prefixWord ++ tailWord_933863).sum := by decide
  have hdescent : baseEnd_933863 < baseStart_933863 := by decide
  rcases family_descends (prefixWord ++ tailWord_933863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933873 : List Nat := [1, 2, 2, 2, 6, 1, 1, 3, 2]
def baseStart_933873 : Nat := 118140960795 + 933873 * 2 ^ 59
def prefixEnd_933873 : Nat := 4983230072969 + 3 ^ 40 * 933873 * 2
def baseEnd_933873 : Nat := 426245083783404401149069

theorem tailTrace_933873 : CollatzResearch.WordTrace tailWord_933873 prefixEnd_933873 426245083783404401149069 := by
  unfold tailWord_933873
  simp only [CollatzResearch.WordTrace]
  refine ⟨34061146545745088655638273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22707431030496725770425515 34061146545745088655638273)
  ·
    refine ⟨25545859909308816491728705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34061146545745088655638273 25545859909308816491728705)
    ·
      refine ⟨19159394931981612368796529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25545859909308816491728705 19159394931981612368796529)
      ·
        refine ⟨14369546198986209276597397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19159394931981612368796529 14369546198986209276597397)
        ·
          refine ⟨673572478077478559840503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14369546198986209276597397 673572478077478559840503)
          ·
            refine ⟨1010358717116217839760755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673572478077478559840503 1010358717116217839760755)
            ·
              refine ⟨1515538075674326759641133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010358717116217839760755 1515538075674326759641133)
              ·
                refine ⟨568326778377872534865425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1515538075674326759641133 568326778377872534865425)
                ·
                  refine ⟨426245083783404401149069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568326778377872534865425 426245083783404401149069)
                  ·
                    rfl

theorem cell20_933873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_933873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933873 prefixEnd_933873 := by exact prefixLift 933873
  have htrace : WordTrace (prefixWord ++ tailWord_933873) baseStart_933873 baseEnd_933873 := by
    simpa [prefixWord, tailWord_933873, baseEnd_933873] using wordTrace_append hprefix tailTrace_933873
  have hstable : (prefixWord ++ tailWord_933873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933873).length < 2 ^ (prefixWord ++ tailWord_933873).sum := by decide
  have hdescent : baseEnd_933873 < baseStart_933873 := by decide
  rcases family_descends (prefixWord ++ tailWord_933873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933919 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_933919 : Nat := 118140960795 + 933919 * 2 ^ 59
def prefixEnd_933919 : Nat := 4983230072969 + 3 ^ 40 * 933919 * 2
def baseEnd_933919 : Nat := 426266079436832685615547

theorem tailTrace_933919 : CollatzResearch.WordTrace tailWord_933919 prefixEnd_933919 426266079436832685615547 := by
  unfold tailWord_933919
  simp only [CollatzResearch.WordTrace]
  refine ⟨34062824303578438511812811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22708549535718959007875207 34062824303578438511812811)
  ·
    refine ⟨51094236455367657767719217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34062824303578438511812811 51094236455367657767719217)
    ·
      refine ⟨38320677341525743325789413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51094236455367657767719217 38320677341525743325789413)
      ·
        refine ⟨7185127001536076873585515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38320677341525743325789413 7185127001536076873585515)
        ·
          refine ⟨10777690502304115310378273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7185127001536076873585515 10777690502304115310378273)
          ·
            refine ⟨8083267876728086482783705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10777690502304115310378273 8083267876728086482783705)
            ·
              refine ⟨6062450907546064862087779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8083267876728086482783705 6062450907546064862087779)
              ·
                refine ⟨9093676361319097293131669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062450907546064862087779 9093676361319097293131669)
                ·
                  refine ⟨426266079436832685615547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9093676361319097293131669 426266079436832685615547)
                  ·
                    rfl

theorem cell20_933919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_933919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933919 prefixEnd_933919 := by exact prefixLift 933919
  have htrace : WordTrace (prefixWord ++ tailWord_933919) baseStart_933919 baseEnd_933919 := by
    simpa [prefixWord, tailWord_933919, baseEnd_933919] using wordTrace_append hprefix tailTrace_933919
  have hstable : (prefixWord ++ tailWord_933919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933919).length < 2 ^ (prefixWord ++ tailWord_933919).sum := by decide
  have hdescent : baseEnd_933919 < baseStart_933919 := by decide
  rcases family_descends (prefixWord ++ tailWord_933919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933957 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_933957 : Nat := 118140960795 + 933957 * 2 ^ 59
def prefixEnd_933957 : Nat := 4983230072969 + 3 ^ 40 * 933957 * 2
def baseEnd_933957 : Nat := 426283423672273442348725

theorem tailTrace_933957 : CollatzResearch.WordTrace tailWord_933957 prefixEnd_933957 426283423672273442348725 := by
  unfold tailWord_933957
  simp only [CollatzResearch.WordTrace]
  refine ⟨34064210277440771001696125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22709473518293847334464083 34064210277440771001696125)
  ·
    refine ⟨12774078854040289125636047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34064210277440771001696125 12774078854040289125636047)
    ·
      refine ⟨19161118281060433688454071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12774078854040289125636047 19161118281060433688454071)
      ·
        refine ⟨28741677421590650532681107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19161118281060433688454071 28741677421590650532681107)
        ·
          refine ⟨43112516132385975799021661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28741677421590650532681107 43112516132385975799021661)
          ·
            refine ⟨16167193549644740924633123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43112516132385975799021661 16167193549644740924633123)
            ·
              refine ⟨24250790324467111386949685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16167193549644740924633123 24250790324467111386949685)
              ·
                refine ⟨2273511592918791692526533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24250790324467111386949685 2273511592918791692526533)
                ·
                  refine ⟨426283423672273442348725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273511592918791692526533 426283423672273442348725)
                  ·
                    rfl

theorem cell20_933957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_933957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933957 prefixEnd_933957 := by exact prefixLift 933957
  have htrace : WordTrace (prefixWord ++ tailWord_933957) baseStart_933957 baseEnd_933957 := by
    simpa [prefixWord, tailWord_933957, baseEnd_933957] using wordTrace_append hprefix tailTrace_933957
  have hstable : (prefixWord ++ tailWord_933957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933957).length < 2 ^ (prefixWord ++ tailWord_933957).sum := by decide
  have hdescent : baseEnd_933957 < baseStart_933957 := by decide
  rcases family_descends (prefixWord ++ tailWord_933957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933991 : List Nat := [1, 1, 5, 1, 1, 2, 4, 3, 2]
def baseStart_933991 : Nat := 118140960795 + 933991 * 2 ^ 59
def prefixEnd_933991 : Nat := 4983230072969 + 3 ^ 40 * 933991 * 2
def baseEnd_933991 : Nat := 426298942198720435215253

theorem tailTrace_933991 : CollatzResearch.WordTrace tailWord_933991 prefixEnd_933991 426298942198720435215253 := by
  unfold tailWord_933991
  simp only [CollatzResearch.WordTrace]
  refine ⟨34065450359317594808433827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22710300239545063205622551 34065450359317594808433827)
  ·
    refine ⟨51098175538976392212650741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34065450359317594808433827 51098175538976392212650741)
    ·
      refine ⟨4790453956779036769936007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51098175538976392212650741 4790453956779036769936007)
      ·
        refine ⟨7185680935168555154904011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790453956779036769936007 7185680935168555154904011)
        ·
          refine ⟨10778521402752832732356017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7185680935168555154904011 10778521402752832732356017)
          ·
            refine ⟨8083891052064624549267013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10778521402752832732356017 8083891052064624549267013)
            ·
              refine ⟨1515729572262117102987565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8083891052064624549267013 1515729572262117102987565)
              ·
                refine ⟨568398589598293913620337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1515729572262117102987565 568398589598293913620337)
                ·
                  refine ⟨426298942198720435215253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568398589598293913620337 426298942198720435215253)
                  ·
                    rfl

theorem cell20_933991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 2].length) (baseStart_933991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_933991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_933991 prefixEnd_933991 := by exact prefixLift 933991
  have htrace : WordTrace (prefixWord ++ tailWord_933991) baseStart_933991 baseEnd_933991 := by
    simpa [prefixWord, tailWord_933991, baseEnd_933991] using wordTrace_append hprefix tailTrace_933991
  have hstable : (prefixWord ++ tailWord_933991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933991).length < 2 ^ (prefixWord ++ tailWord_933991).sum := by decide
  have hdescent : baseEnd_933991 < baseStart_933991 := by decide
  rcases family_descends (prefixWord ++ tailWord_933991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934012 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_934012 : Nat := 118140960795 + 934012 * 2 ^ 59
def prefixEnd_934012 : Nat := 4983230072969 + 3 ^ 40 * 934012 * 2
def baseEnd_934012 : Nat := 426308527170937695515167

theorem tailTrace_934012 : CollatzResearch.WordTrace tailWord_934012 prefixEnd_934012 426308527170937695515167 := by
  unfold tailWord_934012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17033108146120757697474145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22710810861494343596632193 17033108146120757697474145)
  ·
    refine ⟨12774831109590568273105609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17033108146120757697474145 12774831109590568273105609)
    ·
      refine ⟨9581123332192926204829207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12774831109590568273105609 9581123332192926204829207)
      ·
        refine ⟨14371684998289389307243811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9581123332192926204829207 14371684998289389307243811)
        ·
          refine ⟨21557527497434083960865717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371684998289389307243811 21557527497434083960865717)
          ·
            refine ⟨2021018202884445371331161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21557527497434083960865717 2021018202884445371331161)
            ·
              refine ⟨1515763652163334028498371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021018202884445371331161 1515763652163334028498371)
              ·
                refine ⟨2273645478245001042747557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515763652163334028498371 2273645478245001042747557)
                ·
                  refine ⟨426308527170937695515167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273645478245001042747557 426308527170937695515167)
                  ·
                    rfl

theorem cell20_934012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_934012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934012 prefixEnd_934012 := by exact prefixLift 934012
  have htrace : WordTrace (prefixWord ++ tailWord_934012) baseStart_934012 baseEnd_934012 := by
    simpa [prefixWord, tailWord_934012, baseEnd_934012] using wordTrace_append hprefix tailTrace_934012
  have hstable : (prefixWord ++ tailWord_934012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934012).length < 2 ^ (prefixWord ++ tailWord_934012).sum := by decide
  have hdescent : baseEnd_934012 < baseStart_934012 := by decide
  rcases family_descends (prefixWord ++ tailWord_934012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934038 : List Nat := [5, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_934038 : Nat := 118140960795 + 934038 * 2 ^ 59
def prefixEnd_934038 : Nat := 4983230072969 + 3 ^ 40 * 934038 * 2
def baseEnd_934038 : Nat := 426320394279397160648395

theorem tailTrace_934038 : CollatzResearch.WordTrace tailWord_934038 prefixEnd_934038 426320394279397160648395 := by
  unfold tailWord_934038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129197786884207614712173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22711443060098214556929845 2129197786884207614712173)
  ·
    refine ⟨798449170081577855517065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2129197786884207614712173 798449170081577855517065)
    ·
      refine ⟨598836877561183391637799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798449170081577855517065 598836877561183391637799)
      ·
        refine ⟨898255316341775087456699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598836877561183391637799 898255316341775087456699)
        ·
          refine ⟨1347382974512662631185049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898255316341775087456699 1347382974512662631185049)
          ·
            refine ⟨1010537230884496973388787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347382974512662631185049 1010537230884496973388787)
            ·
              refine ⟨1515805846326745460083181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010537230884496973388787 1515805846326745460083181)
              ·
                refine ⟨568427192372529547531193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1515805846326745460083181 568427192372529547531193)
                ·
                  refine ⟨426320394279397160648395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568427192372529547531193 426320394279397160648395)
                  ·
                    rfl

theorem cell20_934038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_934038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934038 prefixEnd_934038 := by exact prefixLift 934038
  have htrace : WordTrace (prefixWord ++ tailWord_934038) baseStart_934038 baseEnd_934038 := by
    simpa [prefixWord, tailWord_934038, baseEnd_934038] using wordTrace_append hprefix tailTrace_934038
  have hstable : (prefixWord ++ tailWord_934038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934038).length < 2 ^ (prefixWord ++ tailWord_934038).sum := by decide
  have hdescent : baseEnd_934038 < baseStart_934038 := by decide
  rcases family_descends (prefixWord ++ tailWord_934038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934114 : List Nat := [3, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_934114 : Nat := 118140960795 + 934114 * 2 ^ 59
def prefixEnd_934114 : Nat := 4983230072969 + 3 ^ 40 * 934114 * 2
def baseEnd_934114 : Nat := 426355082750278674114751

theorem tailTrace_934114 : CollatzResearch.WordTrace tailWord_934114 prefixEnd_934114 426355082750278674114751 := by
  unfold tailWord_934114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517484134467996703790349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22713291025247991210107597 8517484134467996703790349)
  ·
    refine ⟨3194056550425498763921381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8517484134467996703790349 3194056550425498763921381)
    ·
      refine ⟨598885603204781018235259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3194056550425498763921381 598885603204781018235259)
      ·
        refine ⟨898328404807171527352889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598885603204781018235259 898328404807171527352889)
        ·
          refine ⟨673746303605378645514667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898328404807171527352889 673746303605378645514667)
          ·
            refine ⟨1010619455408067968272001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673746303605378645514667 1010619455408067968272001)
            ·
              refine ⟨757964591556050976204001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010619455408067968272001 757964591556050976204001)
              ·
                refine ⟨568473443667038232153001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757964591556050976204001 568473443667038232153001)
                ·
                  refine ⟨426355082750278674114751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568473443667038232153001 426355082750278674114751)
                  ·
                    rfl

theorem cell20_934114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_934114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934114 prefixEnd_934114 := by exact prefixLift 934114
  have htrace : WordTrace (prefixWord ++ tailWord_934114) baseStart_934114 baseEnd_934114 := by
    simpa [prefixWord, tailWord_934114, baseEnd_934114] using wordTrace_append hprefix tailTrace_934114
  have hstable : (prefixWord ++ tailWord_934114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934114).length < 2 ^ (prefixWord ++ tailWord_934114).sum := by decide
  have hdescent : baseEnd_934114 < baseStart_934114 := by decide
  rcases family_descends (prefixWord ++ tailWord_934114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934119 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 3]
def baseStart_934119 : Nat := 118140960795 + 934119 * 2 ^ 59
def prefixEnd_934119 : Nat := 4983230072969 + 3 ^ 40 * 934119 * 2
def baseEnd_934119 : Nat := 426357364886520878948063

theorem tailTrace_934119 : CollatzResearch.WordTrace tailWord_934119 prefixEnd_934119 426357364886520878948063 := by
  unfold tailWord_934119
  simp only [CollatzResearch.WordTrace]
  refine ⟨34070118902853872669093411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22713412601902581779395607 34070118902853872669093411)
  ·
    refine ⟨51105178354280809003640117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34070118902853872669093411 51105178354280809003640117)
    ·
      refine ⟨4791110470713825844091261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51105178354280809003640117 4791110470713825844091261)
      ·
        refine ⟨1796666426517684691534223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4791110470713825844091261 1796666426517684691534223)
        ·
          refine ⟨2694999639776527037301335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796666426517684691534223 2694999639776527037301335)
          ·
            refine ⟨4042499459664790555952003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694999639776527037301335 4042499459664790555952003)
            ·
              refine ⟨6063749189497185833928005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4042499459664790555952003 6063749189497185833928005)
              ·
                refine ⟨1136952973030722343861501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6063749189497185833928005 1136952973030722343861501)
                ·
                  refine ⟨426357364886520878948063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136952973030722343861501 426357364886520878948063)
                  ·
                    rfl

theorem cell20_934119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_934119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934119 prefixEnd_934119 := by exact prefixLift 934119
  have htrace : WordTrace (prefixWord ++ tailWord_934119) baseStart_934119 baseEnd_934119 := by
    simpa [prefixWord, tailWord_934119, baseEnd_934119] using wordTrace_append hprefix tailTrace_934119
  have hstable : (prefixWord ++ tailWord_934119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934119).length < 2 ^ (prefixWord ++ tailWord_934119).sum := by decide
  have hdescent : baseEnd_934119 < baseStart_934119 := by decide
  rcases family_descends (prefixWord ++ tailWord_934119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934147 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_934147 : Nat := 118140960795 + 934147 * 2 ^ 59
def prefixEnd_934147 : Nat := 4983230072969 + 3 ^ 40 * 934147 * 2
def baseEnd_934147 : Nat := 426370144849477226014615

theorem tailTrace_934147 : CollatzResearch.WordTrace tailWord_934147 prefixEnd_934147 426370144849477226014615 := by
  unfold tailWord_934147
  simp only [CollatzResearch.WordTrace]
  refine ⟨34071140146752433451112695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22714093431168288967408463 34071140146752433451112695)
  ·
    refine ⟨51106710220128650176669043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34071140146752433451112695 51106710220128650176669043)
    ·
      refine ⟨76660065330192975265003565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51106710220128650176669043 76660065330192975265003565)
      ·
        refine ⟨28747524498822365724376337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76660065330192975265003565 28747524498822365724376337)
        ·
          refine ⟨21560643374116774293282253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28747524498822365724376337 21560643374116774293282253)
          ·
            refine ⟨8085241265293790359980845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21560643374116774293282253 8085241265293790359980845)
            ·
              refine ⟨3031965474485171384992817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8085241265293790359980845 3031965474485171384992817)
              ·
                refine ⟨2273974105863878538744613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3031965474485171384992817 2273974105863878538744613)
                ·
                  refine ⟨426370144849477226014615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273974105863878538744613 426370144849477226014615)
                  ·
                    rfl

theorem cell20_934147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_934147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934147 prefixEnd_934147 := by exact prefixLift 934147
  have htrace : WordTrace (prefixWord ++ tailWord_934147) baseStart_934147 baseEnd_934147 := by
    simpa [prefixWord, tailWord_934147, baseEnd_934147] using wordTrace_append hprefix tailTrace_934147
  have hstable : (prefixWord ++ tailWord_934147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934147).length < 2 ^ (prefixWord ++ tailWord_934147).sum := by decide
  have hdescent : baseEnd_934147 < baseStart_934147 := by decide
  rcases family_descends (prefixWord ++ tailWord_934147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934154 : List Nat := [3, 1, 2, 2, 1, 1, 2, 8]
def baseStart_934154 : Nat := 118140960795 + 934154 * 2 ^ 59
def prefixEnd_934154 : Nat := 4983230072969 + 3 ^ 40 * 934154 * 2
def baseEnd_934154 : Nat := 142124446613405437593751

theorem tailTrace_934154 : CollatzResearch.WordTrace tailWord_934154 prefixEnd_934154 142124446613405437593751 := by
  unfold tailWord_934154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517848864431768411654379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22714263638484715764411677 8517848864431768411654379)
  ·
    refine ⟨12776773296647652617481569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8517848864431768411654379 12776773296647652617481569)
    ·
      refine ⟨9582579972485739463111177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12776773296647652617481569 9582579972485739463111177)
      ·
        refine ⟨7186934979364304597333383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9582579972485739463111177 7186934979364304597333383)
        ·
          refine ⟨10780402469046456896000075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7186934979364304597333383 10780402469046456896000075)
          ·
            refine ⟨16170603703569685344000113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10780402469046456896000075 16170603703569685344000113)
            ·
              refine ⟨12127952777677264008000085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16170603703569685344000113 12127952777677264008000085)
              ·
                refine ⟨142124446613405437593751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12127952777677264008000085 142124446613405437593751)
                ·
                  rfl

theorem cell20_934154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_934154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934154 prefixEnd_934154 := by exact prefixLift 934154
  have htrace : WordTrace (prefixWord ++ tailWord_934154) baseStart_934154 baseEnd_934154 := by
    simpa [prefixWord, tailWord_934154, baseEnd_934154] using wordTrace_append hprefix tailTrace_934154
  have hstable : (prefixWord ++ tailWord_934154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934154).length < 2 ^ (prefixWord ++ tailWord_934154).sum := by decide
  have hdescent : baseEnd_934154 < baseStart_934154 := by decide
  rcases family_descends (prefixWord ++ tailWord_934154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934174 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_934174 : Nat := 118140960795 + 934174 * 2 ^ 59
def prefixEnd_934174 : Nat := 4983230072969 + 3 ^ 40 * 934174 * 2
def baseEnd_934174 : Nat := 426382468385185132114505

theorem tailTrace_934174 : CollatzResearch.WordTrace tailWord_934174 prefixEnd_934174 426382468385185132114505 := by
  unfold tailWord_934174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259015614706827132793197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22714749945103078041563717 4259015614706827132793197)
  ·
    refine ⟨1597130855515060174797449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4259015614706827132793197 1597130855515060174797449)
    ·
      refine ⟨1197848141636295131098087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1597130855515060174797449 1197848141636295131098087)
      ·
        refine ⟨1796772212454442696647131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197848141636295131098087 1796772212454442696647131)
        ·
          refine ⟨2695158318681664044970697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796772212454442696647131 2695158318681664044970697)
          ·
            refine ⟨2021368739011248033728023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2695158318681664044970697 2021368739011248033728023)
            ·
              refine ⟨3032053108516872050592035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021368739011248033728023 3032053108516872050592035)
              ·
                refine ⟨4548079662775308075888053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032053108516872050592035 4548079662775308075888053)
                ·
                  refine ⟨426382468385185132114505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4548079662775308075888053 426382468385185132114505)
                  ·
                    rfl

theorem cell20_934174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_934174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934174 prefixEnd_934174 := by exact prefixLift 934174
  have htrace : WordTrace (prefixWord ++ tailWord_934174) baseStart_934174 baseEnd_934174 := by
    simpa [prefixWord, tailWord_934174, baseEnd_934174] using wordTrace_append hprefix tailTrace_934174
  have hstable : (prefixWord ++ tailWord_934174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934174).length < 2 ^ (prefixWord ++ tailWord_934174).sum := by decide
  have hdescent : baseEnd_934174 < baseStart_934174 := by decide
  rcases family_descends (prefixWord ++ tailWord_934174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934195 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 3]
def baseStart_934195 : Nat := 118140960795 + 934195 * 2 ^ 59
def prefixEnd_934195 : Nat := 4983230072969 + 3 ^ 40 * 934195 * 2
def baseEnd_934195 : Nat := 426392053357402392414419

theorem tailTrace_934195 : CollatzResearch.WordTrace tailWord_934195 prefixEnd_934195 426392053357402392414419 := by
  unfold tailWord_934195
  simp only [CollatzResearch.WordTrace]
  refine ⟨34072890850578537648860039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22715260567052358432573359 34072890850578537648860039)
  ·
    refine ⟨51109336275867806473290059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34072890850578537648860039 51109336275867806473290059)
    ·
      refine ⟨76664004413801709709935089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51109336275867806473290059 76664004413801709709935089)
      ·
        refine ⟨57498003310351282282451317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76664004413801709709935089 57498003310351282282451317)
        ·
          refine ⟨5390437810345432713979811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57498003310351282282451317 5390437810345432713979811)
          ·
            refine ⟨8085656715518149070969717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390437810345432713979811 8085656715518149070969717)
            ·
              refine ⟨758030317079826475403411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8085656715518149070969717 758030317079826475403411)
              ·
                refine ⟨1137045475619739713105117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758030317079826475403411 1137045475619739713105117)
                ·
                  refine ⟨426392053357402392414419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137045475619739713105117 426392053357402392414419)
                  ·
                    rfl

theorem cell20_934195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 3].length) (baseStart_934195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934195 prefixEnd_934195 := by exact prefixLift 934195
  have htrace : WordTrace (prefixWord ++ tailWord_934195) baseStart_934195 baseEnd_934195 := by
    simpa [prefixWord, tailWord_934195, baseEnd_934195] using wordTrace_append hprefix tailTrace_934195
  have hstable : (prefixWord ++ tailWord_934195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934195).length < 2 ^ (prefixWord ++ tailWord_934195).sum := by decide
  have hdescent : baseEnd_934195 < baseStart_934195 := by decide
  rcases family_descends (prefixWord ++ tailWord_934195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934236 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 4]
def baseStart_934236 : Nat := 118140960795 + 934236 * 2 ^ 59
def prefixEnd_934236 : Nat := 4983230072969 + 3 ^ 40 * 934236 * 2
def baseEnd_934236 : Nat := 426410766874588472047585

theorem tailTrace_934236 : CollatzResearch.WordTrace tailWord_934236 prefixEnd_934236 426410766874588472047585 := by
  unfold tailWord_934236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17037193121715000825551281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22716257495620001100735041 17037193121715000825551281)
  ·
    refine ⟨12777894841286250619163461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17037193121715000825551281 12777894841286250619163461)
    ·
      refine ⟨2395855282741171991093149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12777894841286250619163461 2395855282741171991093149)
      ·
        refine ⟨898445731027939496659931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2395855282741171991093149 898445731027939496659931)
        ·
          refine ⟨1347668596541909244989897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898445731027939496659931 1347668596541909244989897)
          ·
            refine ⟨1010751447406431933742423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347668596541909244989897 1010751447406431933742423)
            ·
              refine ⟨1516127171109647900613635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010751447406431933742423 1516127171109647900613635)
              ·
                refine ⟨2274190756664471850920453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516127171109647900613635 2274190756664471850920453)
                ·
                  refine ⟨426410766874588472047585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274190756664471850920453 426410766874588472047585)
                  ·
                    rfl

theorem cell20_934236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_934236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934236 prefixEnd_934236 := by exact prefixLift 934236
  have htrace : WordTrace (prefixWord ++ tailWord_934236) baseStart_934236 baseEnd_934236 := by
    simpa [prefixWord, tailWord_934236, baseEnd_934236] using wordTrace_append hprefix tailTrace_934236
  have hstable : (prefixWord ++ tailWord_934236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934236).length < 2 ^ (prefixWord ++ tailWord_934236).sum := by decide
  have hdescent : baseEnd_934236 < baseStart_934236 := by decide
  rcases family_descends (prefixWord ++ tailWord_934236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934247 : List Nat := [1, 1, 5, 1, 3, 2, 2, 5]
def baseStart_934247 : Nat := 118140960795 + 934247 * 2 ^ 59
def prefixEnd_934247 : Nat := 4983230072969 + 3 ^ 40 * 934247 * 2
def baseEnd_934247 : Nat := 142138595858107107560291

theorem tailTrace_934247 : CollatzResearch.WordTrace tailWord_934247 prefixEnd_934247 142138595858107107560291 := by
  unfold tailWord_934247
  simp only [CollatzResearch.WordTrace]
  refine ⟨34074787446390150529752995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22716524964260100353168663 34074787446390150529752995)
  ·
    refine ⟨51112181169585225794629493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34074787446390150529752995 51112181169585225794629493)
    ·
      refine ⟨4791766984648614918246515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51112181169585225794629493 4791766984648614918246515)
      ·
        refine ⟨7187650476972922377369773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4791766984648614918246515 7187650476972922377369773)
        ·
          refine ⟨2695368928864845891513665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7187650476972922377369773 2695368928864845891513665)
          ·
            refine ⟨2021526696648634418635249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2695368928864845891513665 2021526696648634418635249)
            ·
              refine ⟨1516145022486475813976437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021526696648634418635249 1516145022486475813976437)
              ·
                refine ⟨142138595858107107560291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1516145022486475813976437 142138595858107107560291)
                ·
                  rfl

theorem cell20_934247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_934247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934247 prefixEnd_934247 := by exact prefixLift 934247
  have htrace : WordTrace (prefixWord ++ tailWord_934247) baseStart_934247 baseEnd_934247 := by
    simpa [prefixWord, tailWord_934247, baseEnd_934247] using wordTrace_append hprefix tailTrace_934247
  have hstable : (prefixWord ++ tailWord_934247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934247).length < 2 ^ (prefixWord ++ tailWord_934247).sum := by decide
  have hdescent : baseEnd_934247 < baseStart_934247 := by decide
  rcases family_descends (prefixWord ++ tailWord_934247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934250 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_934250 : Nat := 118140960795 + 934250 * 2 ^ 59
def prefixEnd_934250 : Nat := 4983230072969 + 3 ^ 40 * 934250 * 2
def baseEnd_934250 : Nat := 426417156856066645580861

theorem tailTrace_934250 : CollatzResearch.WordTrace tailWord_934250 prefixEnd_934250 426417156856066645580861 := by
  unfold tailWord_934250
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518724216344820510528051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22716597910252854694741469 8518724216344820510528051)
  ·
    refine ⟨12778086324517230765792077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8518724216344820510528051 12778086324517230765792077)
    ·
      refine ⟨4791782371693961537172029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12778086324517230765792077 4791782371693961537172029)
      ·
        refine ⟨1796918389385235576439511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4791782371693961537172029 1796918389385235576439511)
        ·
          refine ⟨2695377584077853364659267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796918389385235576439511 2695377584077853364659267)
          ·
            refine ⟨4043066376116780046988901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695377584077853364659267 4043066376116780046988901)
            ·
              refine ⟨758074945521896258810419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4043066376116780046988901 758074945521896258810419)
              ·
                refine ⟨1137112418282844388215629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758074945521896258810419 1137112418282844388215629)
                ·
                  refine ⟨426417156856066645580861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137112418282844388215629 426417156856066645580861)
                  ·
                    rfl

theorem cell20_934250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_934250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934250 prefixEnd_934250 := by exact prefixLift 934250
  have htrace : WordTrace (prefixWord ++ tailWord_934250) baseStart_934250 baseEnd_934250 := by
    simpa [prefixWord, tailWord_934250, baseEnd_934250] using wordTrace_append hprefix tailTrace_934250
  have hstable : (prefixWord ++ tailWord_934250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934250).length < 2 ^ (prefixWord ++ tailWord_934250).sum := by decide
  have hdescent : baseEnd_934250 < baseStart_934250 := by decide
  rcases family_descends (prefixWord ++ tailWord_934250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934295 : List Nat := [1, 1, 3, 3, 1, 1, 6, 2, 2]
def baseStart_934295 : Nat := 118140960795 + 934295 * 2 ^ 59
def prefixEnd_934295 : Nat := 4983230072969 + 3 ^ 40 * 934295 * 2
def baseEnd_934295 : Nat := 426437696082246489080677

theorem tailTrace_934295 : CollatzResearch.WordTrace tailWord_934295 prefixEnd_934295 426437696082246489080677 := by
  unfold tailWord_934295
  simp only [CollatzResearch.WordTrace]
  refine ⟨34076538150216254727500339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22717692100144169818333559 34076538150216254727500339)
  ·
    refine ⟨51114807225324382091250509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34076538150216254727500339 51114807225324382091250509)
    ·
      refine ⟨19168052709496643284218941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51114807225324382091250509 19168052709496643284218941)
      ·
        refine ⟨7188019766061241231582103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19168052709496643284218941 7188019766061241231582103)
        ·
          refine ⟨10782029649091861847373155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7188019766061241231582103 10782029649091861847373155)
          ·
            refine ⟨16173044473637792771059733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10782029649091861847373155 16173044473637792771059733)
            ·
              refine ⟨758111459701771536143425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16173044473637792771059733 758111459701771536143425)
              ·
                refine ⟨568583594776328652107569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758111459701771536143425 568583594776328652107569)
                ·
                  refine ⟨426437696082246489080677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568583594776328652107569 426437696082246489080677)
                  ·
                    rfl

theorem cell20_934295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 2].length) (baseStart_934295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934295 prefixEnd_934295 := by exact prefixLift 934295
  have htrace : WordTrace (prefixWord ++ tailWord_934295) baseStart_934295 baseEnd_934295 := by
    simpa [prefixWord, tailWord_934295, baseEnd_934295] using wordTrace_append hprefix tailTrace_934295
  have hstable : (prefixWord ++ tailWord_934295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934295).length < 2 ^ (prefixWord ++ tailWord_934295).sum := by decide
  have hdescent : baseEnd_934295 < baseStart_934295 := by decide
  rcases family_descends (prefixWord ++ tailWord_934295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934302 : List Nat := [4, 3, 1, 2, 1, 1, 3, 5]
def baseStart_934302 : Nat := 118140960795 + 934302 * 2 ^ 59
def prefixEnd_934302 : Nat := 4983230072969 + 3 ^ 40 * 934302 * 2
def baseEnd_934302 : Nat := 142146963690995191949105

theorem tailTrace_934302 : CollatzResearch.WordTrace tailWord_934302 prefixEnd_934302 142146963690995191949105 := by
  unfold tailWord_934302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259599182648861865375645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22717862307460596615336773 4259599182648861865375645)
  ·
    refine ⟨1597349693493323199515867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4259599182648861865375645 1597349693493323199515867)
    ·
      refine ⟨2396024540239984799273801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597349693493323199515867 2396024540239984799273801)
      ·
        refine ⟨1797018405179988599455351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2396024540239984799273801 1797018405179988599455351)
        ·
          refine ⟨2695527607769982899183027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797018405179988599455351 2695527607769982899183027)
          ·
            refine ⟨4043291411654974348774541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695527607769982899183027 4043291411654974348774541)
            ·
              refine ⟨1516234279370615380790453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4043291411654974348774541 1516234279370615380790453)
              ·
                refine ⟨142146963690995191949105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1516234279370615380790453 142146963690995191949105)
                ·
                  rfl

theorem cell20_934302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_934302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934302 prefixEnd_934302 := by exact prefixLift 934302
  have htrace : WordTrace (prefixWord ++ tailWord_934302) baseStart_934302 baseEnd_934302 := by
    simpa [prefixWord, tailWord_934302, baseEnd_934302] using wordTrace_append hprefix tailTrace_934302
  have hstable : (prefixWord ++ tailWord_934302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934302).length < 2 ^ (prefixWord ++ tailWord_934302).sum := by decide
  have hdescent : baseEnd_934302 < baseStart_934302 := by decide
  rcases family_descends (prefixWord ++ tailWord_934302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934333 : List Nat := [1, 4, 1, 2, 2, 3, 2, 3, 2]
def baseStart_934333 : Nat := 118140960795 + 934333 * 2 ^ 59
def prefixEnd_934333 : Nat := 4983230072969 + 3 ^ 40 * 934333 * 2
def baseEnd_934333 : Nat := 426455040317687245813855

theorem tailTrace_934333 : CollatzResearch.WordTrace tailWord_934333 prefixEnd_934333 426455040317687245813855 := by
  unfold tailWord_934333
  simp only [CollatzResearch.WordTrace]
  refine ⟨34077924124078587217383653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22718616082719058144922435 34077924124078587217383653)
  ·
    refine ⟨6389610773264735103259435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34077924124078587217383653 6389610773264735103259435)
    ·
      refine ⟨9584416159897102654889153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6389610773264735103259435 9584416159897102654889153)
      ·
        refine ⟨7188312119922826991166865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9584416159897102654889153 7188312119922826991166865)
        ·
          refine ⟨5391234089942120243375149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7188312119922826991166865 5391234089942120243375149)
          ·
            refine ⟨2021712783728295091265681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5391234089942120243375149 2021712783728295091265681)
            ·
              refine ⟨1516284587796221318449261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021712783728295091265681 1516284587796221318449261)
              ·
                refine ⟨568606720423582994418473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1516284587796221318449261 568606720423582994418473)
                ·
                  refine ⟨426455040317687245813855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568606720423582994418473 426455040317687245813855)
                  ·
                    rfl

theorem cell20_934333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_934333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934333 prefixEnd_934333 := by exact prefixLift 934333
  have htrace : WordTrace (prefixWord ++ tailWord_934333) baseStart_934333 baseEnd_934333 := by
    simpa [prefixWord, tailWord_934333, baseEnd_934333] using wordTrace_append hprefix tailTrace_934333
  have hstable : (prefixWord ++ tailWord_934333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934333).length < 2 ^ (prefixWord ++ tailWord_934333).sum := by decide
  have hdescent : baseEnd_934333 < baseStart_934333 := by decide
  rcases family_descends (prefixWord ++ tailWord_934333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934344 : List Nat := [2, 1, 3, 1, 3, 3, 7]
def baseStart_934344 : Nat := 118140960795 + 934344 * 2 ^ 59
def prefixEnd_934344 : Nat := 4983230072969 + 3 ^ 40 * 934344 * 2
def baseEnd_934344 : Nat := 47384451224157788494127

theorem tailTrace_934344 : CollatzResearch.WordTrace tailWord_934344 prefixEnd_934344 47384451224157788494127 := by
  unfold tailWord_934344
  simp only [CollatzResearch.WordTrace]
  refine ⟨17039162663519368048017043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22718883551359157397356057 17039162663519368048017043)
  ·
    refine ⟨25558743995279052072025565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17039162663519368048017043 25558743995279052072025565)
    ·
      refine ⟨9584528998229644527009587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25558743995279052072025565 9584528998229644527009587)
      ·
        refine ⟨14376793497344466790514381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9584528998229644527009587 14376793497344466790514381)
        ·
          refine ⟨5391297561504175046442893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14376793497344466790514381 5391297561504175046442893)
          ·
            refine ⟨2021736585564065642416085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5391297561504175046442893 2021736585564065642416085)
            ·
              refine ⟨47384451224157788494127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2021736585564065642416085 47384451224157788494127)
              ·
                rfl

theorem cell20_934344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 7].length) (baseStart_934344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934344 prefixEnd_934344 := by exact prefixLift 934344
  have htrace : WordTrace (prefixWord ++ tailWord_934344) baseStart_934344 baseEnd_934344 := by
    simpa [prefixWord, tailWord_934344, baseEnd_934344] using wordTrace_append hprefix tailTrace_934344
  have hstable : (prefixWord ++ tailWord_934344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934344).length < 2 ^ (prefixWord ++ tailWord_934344).sum := by decide
  have hdescent : baseEnd_934344 < baseStart_934344 := by decide
  rcases family_descends (prefixWord ++ tailWord_934344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934375 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_934375 : Nat := 118140960795 + 934375 * 2 ^ 59
def prefixEnd_934375 : Nat := 4983230072969 + 3 ^ 40 * 934375 * 2
def baseEnd_934375 : Nat := 426474210262121766413683

theorem tailTrace_934375 : CollatzResearch.WordTrace tailWord_934375 prefixEnd_934375 426474210262121766413683 := by
  unfold tailWord_934375
  simp only [CollatzResearch.WordTrace]
  refine ⟨34079455989926428390412579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22719637326617618926941719 34079455989926428390412579)
  ·
    refine ⟨51119183984889642585618869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34079455989926428390412579 51119183984889642585618869)
    ·
      refine ⟨4792423498583403992401769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51119183984889642585618869 4792423498583403992401769)
      ·
        refine ⟨3594317623937552994301327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4792423498583403992401769 3594317623937552994301327)
        ·
          refine ⟨5391476435906329491451991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594317623937552994301327 5391476435906329491451991)
          ·
            refine ⟨8087214653859494237177987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391476435906329491451991 8087214653859494237177987)
            ·
              refine ⟨12130821980789241355766981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087214653859494237177987 12130821980789241355766981)
              ·
                refine ⟨2274529121397982754206309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12130821980789241355766981 2274529121397982754206309)
                ·
                  refine ⟨426474210262121766413683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274529121397982754206309 426474210262121766413683)
                  ·
                    rfl

theorem cell20_934375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_934375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934375 prefixEnd_934375 := by exact prefixLift 934375
  have htrace : WordTrace (prefixWord ++ tailWord_934375) baseStart_934375 baseEnd_934375 := by
    simpa [prefixWord, tailWord_934375, baseEnd_934375] using wordTrace_append hprefix tailTrace_934375
  have hstable : (prefixWord ++ tailWord_934375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934375).length < 2 ^ (prefixWord ++ tailWord_934375).sum := by decide
  have hdescent : baseEnd_934375 < baseStart_934375 := by decide
  rcases family_descends (prefixWord ++ tailWord_934375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934378 : List Nat := [3, 1, 3, 1, 3, 3, 2, 4]
def baseStart_934378 : Nat := 118140960795 + 934378 * 2 ^ 59
def prefixEnd_934378 : Nat := 4983230072969 + 3 ^ 40 * 934378 * 2
def baseEnd_934378 : Nat := 142158526514622363104557

theorem tailTrace_934378 : CollatzResearch.WordTrace tailWord_934378 prefixEnd_934378 142158526514622363104557 := by
  unfold tailWord_934378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8519891352228889975692947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22719710272610373268514525 8519891352228889975692947)
  ·
    refine ⟨12779837028343334963539421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8519891352228889975692947 12779837028343334963539421)
    ·
      refine ⟨4792438885628750611327283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12779837028343334963539421 4792438885628750611327283)
      ·
        refine ⟨7188658328443125916990925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4792438885628750611327283 7188658328443125916990925)
        ·
          refine ⟨2695746873166172218871597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7188658328443125916990925 2695746873166172218871597)
          ·
            refine ⟨1010905077437314582076849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2695746873166172218871597 1010905077437314582076849)
            ·
              refine ⟨758178808077985936557637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010905077437314582076849 758178808077985936557637)
              ·
                refine ⟨142158526514622363104557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758178808077985936557637 142158526514622363104557)
                ·
                  rfl

theorem cell20_934378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_934378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934378 prefixEnd_934378 := by exact prefixLift 934378
  have htrace : WordTrace (prefixWord ++ tailWord_934378) baseStart_934378 baseEnd_934378 := by
    simpa [prefixWord, tailWord_934378, baseEnd_934378] using wordTrace_append hprefix tailTrace_934378
  have hstable : (prefixWord ++ tailWord_934378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934378).length < 2 ^ (prefixWord ++ tailWord_934378).sum := by decide
  have hdescent : baseEnd_934378 < baseStart_934378 := by decide
  rcases family_descends (prefixWord ++ tailWord_934378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934461 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 3]
def baseStart_934461 : Nat := 118140960795 + 934461 * 2 ^ 59
def prefixEnd_934461 : Nat := 4983230072969 + 3 ^ 40 * 934461 * 2
def baseEnd_934461 : Nat := 426513463005487689546665

theorem tailTrace_934461 : CollatzResearch.WordTrace tailWord_934461 prefixEnd_934461 426513463005487689546665 := by
  unfold tailWord_934461
  simp only [CollatzResearch.WordTrace]
  refine ⟨34082592667614865078043237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22721728445076576718695491 34082592667614865078043237)
  ·
    refine ⟨6390486125177787202133107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34082592667614865078043237 6390486125177787202133107)
    ·
      refine ⟨9585729187766680803199661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6390486125177787202133107 9585729187766680803199661)
      ·
        refine ⟨3594648445412505301199873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9585729187766680803199661 3594648445412505301199873)
        ·
          refine ⟨2695986334059378975899905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3594648445412505301199873 2695986334059378975899905)
          ·
            refine ⟨2021989750544534231924929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2695986334059378975899905 2021989750544534231924929)
            ·
              refine ⟨1516492312908400673943697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021989750544534231924929 1516492312908400673943697)
              ·
                refine ⟨1137369234681300505457773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516492312908400673943697 1137369234681300505457773)
                ·
                  refine ⟨426513463005487689546665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137369234681300505457773 426513463005487689546665)
                  ·
                    rfl

theorem cell20_934461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_934461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934461 prefixEnd_934461 := by exact prefixLift 934461
  have htrace : WordTrace (prefixWord ++ tailWord_934461) baseStart_934461 baseEnd_934461 := by
    simpa [prefixWord, tailWord_934461, baseEnd_934461] using wordTrace_append hprefix tailTrace_934461
  have hstable : (prefixWord ++ tailWord_934461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934461).length < 2 ^ (prefixWord ++ tailWord_934461).sum := by decide
  have hdescent : baseEnd_934461 < baseStart_934461 := by decide
  rcases family_descends (prefixWord ++ tailWord_934461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934472 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_934472 : Nat := 118140960795 + 934472 * 2 ^ 59
def prefixEnd_934472 : Nat := 4983230072969 + 3 ^ 40 * 934472 * 2
def baseEnd_934472 : Nat := 426518483705220540179953

theorem tailTrace_934472 : CollatzResearch.WordTrace tailWord_934472 prefixEnd_934472 426518483705220540179953 := by
  unfold tailWord_934472
  simp only [CollatzResearch.WordTrace]
  refine ⟨17041496935287506978346835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22721995913716675971129113 17041496935287506978346835)
  ·
    refine ⟨25562245402931260467520253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17041496935287506978346835 25562245402931260467520253)
    ·
      refine ⟨9585842026099222675320095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25562245402931260467520253 9585842026099222675320095)
      ·
        refine ⟨14378763039148834012980143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9585842026099222675320095 14378763039148834012980143)
        ·
          refine ⟨21568144558723251019470215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14378763039148834012980143 21568144558723251019470215)
          ·
            refine ⟨32352216838084876529205323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21568144558723251019470215 32352216838084876529205323)
            ·
              refine ⟨48528325257127314793807985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32352216838084876529205323 48528325257127314793807985)
              ·
                refine ⟨36396243942845486095355989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48528325257127314793807985 36396243942845486095355989)
                ·
                  refine ⟨426518483705220540179953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36396243942845486095355989 426518483705220540179953)
                  ·
                    rfl

theorem cell20_934472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_934472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934472 prefixEnd_934472 := by exact prefixLift 934472
  have htrace : WordTrace (prefixWord ++ tailWord_934472) baseStart_934472 baseEnd_934472 := by
    simpa [prefixWord, tailWord_934472, baseEnd_934472] using wordTrace_append hprefix tailTrace_934472
  have hstable : (prefixWord ++ tailWord_934472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934472).length < 2 ^ (prefixWord ++ tailWord_934472).sum := by decide
  have hdescent : baseEnd_934472 < baseStart_934472 := by decide
  rcases family_descends (prefixWord ++ tailWord_934472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934482 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_934482 : Nat := 118140960795 + 934482 * 2 ^ 59
def prefixEnd_934482 : Nat := 4983230072969 + 3 ^ 40 * 934482 * 2
def baseEnd_934482 : Nat := 426523047977704949846579

theorem tailTrace_934482 : CollatzResearch.WordTrace tailWord_934482 prefixEnd_934482 426523047977704949846579 := by
  unfold tailWord_934482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8520839650134696416139425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22722239067025857109705133 8520839650134696416139425)
  ·
    refine ⟨6390629737601022312104569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8520839650134696416139425 6390629737601022312104569)
    ·
      refine ⟨4792972303200766734078427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6390629737601022312104569 4792972303200766734078427)
      ·
        refine ⟨7189458454801150101117641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4792972303200766734078427 7189458454801150101117641)
        ·
          refine ⟨5392093841100862575838231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7189458454801150101117641 5392093841100862575838231)
          ·
            refine ⟨8088140761651293863757347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392093841100862575838231 8088140761651293863757347)
            ·
              refine ⟨12132211142476940795636021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088140761651293863757347 12132211142476940795636021)
              ·
                refine ⟨1137394794607213199590877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12132211142476940795636021 1137394794607213199590877)
                ·
                  refine ⟨426523047977704949846579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137394794607213199590877 426523047977704949846579)
                  ·
                    rfl

theorem cell20_934482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_934482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934482 prefixEnd_934482 := by exact prefixLift 934482
  have htrace : WordTrace (prefixWord ++ tailWord_934482) baseStart_934482 baseEnd_934482 := by
    simpa [prefixWord, tailWord_934482, baseEnd_934482] using wordTrace_append hprefix tailTrace_934482
  have hstable : (prefixWord ++ tailWord_934482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934482).length < 2 ^ (prefixWord ++ tailWord_934482).sum := by decide
  have hdescent : baseEnd_934482 < baseStart_934482 := by decide
  rcases family_descends (prefixWord ++ tailWord_934482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934492 : List Nat := [2, 2, 4, 1, 3, 1, 3, 4]
def baseStart_934492 : Nat := 118140960795 + 934492 * 2 ^ 59
def prefixEnd_934492 : Nat := 4983230072969 + 3 ^ 40 * 934492 * 2
def baseEnd_934492 : Nat := 142175870750063119837735

theorem tailTrace_934492 : CollatzResearch.WordTrace tailWord_934492 prefixEnd_934492 142175870750063119837735 := by
  unfold tailWord_934492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17041861665251278686210865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22722482220335038248281153 17041861665251278686210865)
  ·
    refine ⟨12781396248938459014658149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17041861665251278686210865 12781396248938459014658149)
    ·
      refine ⟨2396511796675961065248403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12781396248938459014658149 2396511796675961065248403)
      ·
        refine ⟨3594767695013941597872605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396511796675961065248403 3594767695013941597872605)
        ·
          refine ⟨1348037885630228099202227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3594767695013941597872605 1348037885630228099202227)
          ·
            refine ⟨2022056828445342148803341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348037885630228099202227 2022056828445342148803341)
            ·
              refine ⟨758271310667003305801253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2022056828445342148803341 758271310667003305801253)
              ·
                refine ⟨142175870750063119837735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758271310667003305801253 142175870750063119837735)
                ·
                  rfl

theorem cell20_934492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_934492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934492 prefixEnd_934492 := by exact prefixLift 934492
  have htrace : WordTrace (prefixWord ++ tailWord_934492) baseStart_934492 baseEnd_934492 := by
    simpa [prefixWord, tailWord_934492, baseEnd_934492] using wordTrace_append hprefix tailTrace_934492
  have hstable : (prefixWord ++ tailWord_934492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934492).length < 2 ^ (prefixWord ++ tailWord_934492).sum := by decide
  have hdescent : baseEnd_934492 < baseStart_934492 := by decide
  rcases family_descends (prefixWord ++ tailWord_934492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934503 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_934503 : Nat := 118140960795 + 934503 * 2 ^ 59
def prefixEnd_934503 : Nat := 4983230072969 + 3 ^ 40 * 934503 * 2
def baseEnd_934503 : Nat := 426532632949922210146493

theorem tailTrace_934503 : CollatzResearch.WordTrace tailWord_934503 prefixEnd_934503 426532632949922210146493 := by
  unfold tailWord_934503
  simp only [CollatzResearch.WordTrace]
  refine ⟨34084124533462706251072163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22722749688975137500714775 34084124533462706251072163)
  ·
    refine ⟨51126186800194059376608245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34084124533462706251072163 51126186800194059376608245)
    ·
      refine ⟨4793080012518193066557023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51126186800194059376608245 4793080012518193066557023)
      ·
        refine ⟨7189620018777289599835535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793080012518193066557023 7189620018777289599835535)
        ·
          refine ⟨10784430028165934399753303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7189620018777289599835535 10784430028165934399753303)
          ·
            refine ⟨16176645042248901599629955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10784430028165934399753303 16176645042248901599629955)
            ·
              refine ⟨24264967563373352399444933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16176645042248901599629955 24264967563373352399444933)
              ·
                refine ⟨4549681418132503574895925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24264967563373352399444933 4549681418132503574895925)
                ·
                  refine ⟨426532632949922210146493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4549681418132503574895925 426532632949922210146493)
                  ·
                    rfl

theorem cell20_934503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_934503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934503 prefixEnd_934503 := by exact prefixLift 934503
  have htrace : WordTrace (prefixWord ++ tailWord_934503) baseStart_934503 baseEnd_934503 := by
    simpa [prefixWord, tailWord_934503, baseEnd_934503] using wordTrace_append hprefix tailTrace_934503
  have hstable : (prefixWord ++ tailWord_934503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934503).length < 2 ^ (prefixWord ++ tailWord_934503).sum := by decide
  have hdescent : baseEnd_934503 < baseStart_934503 := by decide
  rcases family_descends (prefixWord ++ tailWord_934503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934558 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_934558 : Nat := 118140960795 + 934558 * 2 ^ 59
def prefixEnd_934558 : Nat := 4983230072969 + 3 ^ 40 * 934558 * 2
def baseEnd_934558 : Nat := 426557736448586463312935

theorem tailTrace_934558 : CollatzResearch.WordTrace tailWord_934558 prefixEnd_934558 426557736448586463312935 := by
  unfold tailWord_934558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4260766318532931330540541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22724087032175633762882885 4260766318532931330540541)
  ·
    refine ⟨1597787369449849248952703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4260766318532931330540541 1597787369449849248952703)
    ·
      refine ⟨2396681054174773873429055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597787369449849248952703 2396681054174773873429055)
      ·
        refine ⟨3595021581262160810143583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396681054174773873429055 3595021581262160810143583)
        ·
          refine ⟨5392532371893241215215375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595021581262160810143583 5392532371893241215215375)
          ·
            refine ⟨8088798557839861822823063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392532371893241215215375 8088798557839861822823063)
            ·
              refine ⟨12133197836759792734234595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088798557839861822823063 12133197836759792734234595)
              ·
                refine ⟨18199796755139689101351893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12133197836759792734234595 18199796755139689101351893)
                ·
                  refine ⟨426557736448586463312935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18199796755139689101351893 426557736448586463312935)
                  ·
                    rfl

theorem cell20_934558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_934558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934558 prefixEnd_934558 := by exact prefixLift 934558
  have htrace : WordTrace (prefixWord ++ tailWord_934558) baseStart_934558 baseEnd_934558 := by
    simpa [prefixWord, tailWord_934558, baseEnd_934558] using wordTrace_append hprefix tailTrace_934558
  have hstable : (prefixWord ++ tailWord_934558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934558).length < 2 ^ (prefixWord ++ tailWord_934558).sum := by decide
  have hdescent : baseEnd_934558 < baseStart_934558 := by decide
  rcases family_descends (prefixWord ++ tailWord_934558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934579 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_934579 : Nat := 118140960795 + 934579 * 2 ^ 59
def prefixEnd_934579 : Nat := 4983230072969 + 3 ^ 40 * 934579 * 2
def baseEnd_934579 : Nat := 426567321420803723612849

theorem tailTrace_934579 : CollatzResearch.WordTrace tailWord_934579 prefixEnd_934579 426567321420803723612849 := by
  unfold tailWord_934579
  simp only [CollatzResearch.WordTrace]
  refine ⟨34086896481187371230838791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22724597654124914153892527 34086896481187371230838791)
  ·
    refine ⟨51130344721781056846258187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34086896481187371230838791 51130344721781056846258187)
    ·
      refine ⟨76695517082671585269387281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51130344721781056846258187 76695517082671585269387281)
      ·
        refine ⟨57521637812003688952040461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76695517082671585269387281 57521637812003688952040461)
        ·
          refine ⟨21570614179501383357015173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57521637812003688952040461 21570614179501383357015173)
          ·
            refine ⟨4044490158656509379440345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21570614179501383357015173 4044490158656509379440345)
            ·
              refine ⟨3033367618992382034580259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4044490158656509379440345 3033367618992382034580259)
              ·
                refine ⟨4550051428488573051870389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033367618992382034580259 4550051428488573051870389)
                ·
                  refine ⟨426567321420803723612849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4550051428488573051870389 426567321420803723612849)
                  ·
                    rfl

theorem cell20_934579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_934579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934579 prefixEnd_934579 := by exact prefixLift 934579
  have htrace : WordTrace (prefixWord ++ tailWord_934579) baseStart_934579 baseEnd_934579 := by
    simpa [prefixWord, tailWord_934579, baseEnd_934579] using wordTrace_append hprefix tailTrace_934579
  have hstable : (prefixWord ++ tailWord_934579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934579).length < 2 ^ (prefixWord ++ tailWord_934579).sum := by decide
  have hdescent : baseEnd_934579 < baseStart_934579 := by decide
  rcases family_descends (prefixWord ++ tailWord_934579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934631 : List Nat := [1, 1, 5, 13]
def baseStart_934631 : Nat := 118140960795 + 934631 * 2 ^ 59
def prefixEnd_934631 : Nat := 4983230072969 + 3 ^ 40 * 934631 * 2
def baseEnd_934631 : Nat := 1755518747480340139421

theorem tailTrace_934631 : CollatzResearch.WordTrace tailWord_934631 prefixEnd_934631 1755518747480340139421 := by
  unfold tailWord_934631
  simp only [CollatzResearch.WordTrace]
  refine ⟨34088793076998984111731747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22725862051332656074487831 34088793076998984111731747)
  ·
    refine ⟨51133189615498476167597621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34088793076998984111731747 51133189615498476167597621)
    ·
      refine ⟨4793736526452982140712277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51133189615498476167597621 4793736526452982140712277)
      ·
        refine ⟨1755518747480340139421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4793736526452982140712277 1755518747480340139421)
        ·
          rfl

theorem cell20_934631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 13].length) (baseStart_934631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934631 prefixEnd_934631 := by exact prefixLift 934631
  have htrace : WordTrace (prefixWord ++ tailWord_934631) baseStart_934631 baseEnd_934631 := by
    simpa [prefixWord, tailWord_934631, baseEnd_934631] using wordTrace_append hprefix tailTrace_934631
  have hstable : (prefixWord ++ tailWord_934631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934631).length < 2 ^ (prefixWord ++ tailWord_934631).sum := by decide
  have hdescent : baseEnd_934631 < baseStart_934631 := by decide
  rcases family_descends (prefixWord ++ tailWord_934631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934658 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_934658 : Nat := 118140960795 + 934658 * 2 ^ 59
def prefixEnd_934658 : Nat := 4983230072969 + 3 ^ 40 * 934658 * 2
def baseEnd_934658 : Nat := 426603379173430559979193

theorem tailTrace_934658 : CollatzResearch.WordTrace tailWord_934658 prefixEnd_934658 426603379173430559979193 := by
  unfold tailWord_934658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8522444461975291930741157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22726518565267445148643085 8522444461975291930741157)
  ·
    refine ⟨1597958336620367237013967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8522444461975291930741157 1597958336620367237013967)
    ·
      refine ⟨2396937504930550855520951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597958336620367237013967 2396937504930550855520951)
      ·
        refine ⟨3595406257395826283281427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396937504930550855520951 3595406257395826283281427)
        ·
          refine ⟨5393109386093739424922141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595406257395826283281427 5393109386093739424922141)
          ·
            refine ⟨2022416019785152284345803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5393109386093739424922141 2022416019785152284345803)
            ·
              refine ⟨3033624029677728426518705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022416019785152284345803 3033624029677728426518705)
              ·
                refine ⟨2275218022258296319889029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033624029677728426518705 2275218022258296319889029)
                ·
                  refine ⟨426603379173430559979193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2275218022258296319889029 426603379173430559979193)
                  ·
                    rfl

theorem cell20_934658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_934658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934658 prefixEnd_934658 := by exact prefixLift 934658
  have htrace : WordTrace (prefixWord ++ tailWord_934658) baseStart_934658 baseEnd_934658 := by
    simpa [prefixWord, tailWord_934658, baseEnd_934658] using wordTrace_append hprefix tailTrace_934658
  have hstable : (prefixWord ++ tailWord_934658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934658).length < 2 ^ (prefixWord ++ tailWord_934658).sum := by decide
  have hdescent : baseEnd_934658 < baseStart_934658 := by decide
  rcases family_descends (prefixWord ++ tailWord_934658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934685 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 3]
def baseStart_934685 : Nat := 118140960795 + 934685 * 2 ^ 59
def prefixEnd_934685 : Nat := 4983230072969 + 3 ^ 40 * 934685 * 2
def baseEnd_934685 : Nat := 426615702709138466079083

theorem tailTrace_934685 : CollatzResearch.WordTrace tailWord_934685 prefixEnd_934685 426615702709138466079083 := by
  unfold tailWord_934685
  simp only [CollatzResearch.WordTrace]
  refine ⟨34090762618803351334197509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22727175079202234222798339 34090762618803351334197509)
  ·
    refine ⟨6392017991025628375162033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34090762618803351334197509 6392017991025628375162033)
    ·
      refine ⟨4794013493269221281371525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6392017991025628375162033 4794013493269221281371525)
      ·
        refine ⟨898877529987978990257161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4794013493269221281371525 898877529987978990257161)
        ·
          refine ⟨674158147490984242692871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898877529987978990257161 674158147490984242692871)
          ·
            refine ⟨1011237221236476364039307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674158147490984242692871 1011237221236476364039307)
            ·
              refine ⟨1516855831854714546058961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011237221236476364039307 1516855831854714546058961)
              ·
                refine ⟨1137641873891035909544221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516855831854714546058961 1137641873891035909544221)
                ·
                  refine ⟨426615702709138466079083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137641873891035909544221 426615702709138466079083)
                  ·
                    rfl

theorem cell20_934685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_934685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934685 prefixEnd_934685 := by exact prefixLift 934685
  have htrace : WordTrace (prefixWord ++ tailWord_934685) baseStart_934685 baseEnd_934685 := by
    simpa [prefixWord, tailWord_934685, baseEnd_934685] using wordTrace_append hprefix tailTrace_934685
  have hstable : (prefixWord ++ tailWord_934685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934685).length < 2 ^ (prefixWord ++ tailWord_934685).sum := by decide
  have hdescent : baseEnd_934685 < baseStart_934685 := by decide
  rcases family_descends (prefixWord ++ tailWord_934685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934693 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_934693 : Nat := 118140960795 + 934693 * 2 ^ 59
def prefixEnd_934693 : Nat := 4983230072969 + 3 ^ 40 * 934693 * 2
def baseEnd_934693 : Nat := 426619354127125993812383

theorem tailTrace_934693 : CollatzResearch.WordTrace tailWord_934693 prefixEnd_934693 426619354127125993812383 := by
  unfold tailWord_934693
  simp only [CollatzResearch.WordTrace]
  refine ⟨34091054402774368700488733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22727369601849579133659155 34091054402774368700488733)
  ·
    refine ⟨12784145401040388262683275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34091054402774368700488733 12784145401040388262683275)
    ·
      refine ⟨19176218101560582394024913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12784145401040388262683275 19176218101560582394024913)
      ·
        refine ⟨14382163576170436795518685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19176218101560582394024913 14382163576170436795518685)
        ·
          refine ⟨5393311341063913798319507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14382163576170436795518685 5393311341063913798319507)
          ·
            refine ⟨8089967011595870697479261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393311341063913798319507 8089967011595870697479261)
            ·
              refine ⟨3033737629348451511554723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8089967011595870697479261 3033737629348451511554723)
              ·
                refine ⟨4550606444022677267332085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033737629348451511554723 4550606444022677267332085)
                ·
                  refine ⟨426619354127125993812383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4550606444022677267332085 426619354127125993812383)
                  ·
                    rfl

theorem cell20_934693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_934693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934693 prefixEnd_934693 := by exact prefixLift 934693
  have htrace : WordTrace (prefixWord ++ tailWord_934693) baseStart_934693 baseEnd_934693 := by
    simpa [prefixWord, tailWord_934693, baseEnd_934693] using wordTrace_append hprefix tailTrace_934693
  have hstable : (prefixWord ++ tailWord_934693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934693).length < 2 ^ (prefixWord ++ tailWord_934693).sum := by decide
  have hdescent : baseEnd_934693 < baseStart_934693 := by decide
  rcases family_descends (prefixWord ++ tailWord_934693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934696 : List Nat := [2, 1, 5, 1, 1, 1, 1, 6, 2]
def baseStart_934696 : Nat := 118140960795 + 934696 * 2 ^ 59
def prefixEnd_934696 : Nat := 4983230072969 + 3 ^ 40 * 934696 * 2
def baseEnd_934696 : Nat := 426620723408871316712371

theorem tailTrace_934696 : CollatzResearch.WordTrace tailWord_934696 prefixEnd_934696 426620723408871316712371 := by
  unfold tailWord_934696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17045581910881750106423971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22727442547842333475231961 17045581910881750106423971)
  ·
    refine ⟨25568372866322625159635957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17045581910881750106423971 25568372866322625159635957)
    ·
      refine ⟨2397034956217746108715871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25568372866322625159635957 2397034956217746108715871)
      ·
        refine ⟨3595552434326619163073807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397034956217746108715871 3595552434326619163073807)
        ·
          refine ⟨5393328651489928744610711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595552434326619163073807 5393328651489928744610711)
          ·
            refine ⟨8089992977234893116916067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393328651489928744610711 8089992977234893116916067)
            ·
              refine ⟨12134989465852339675374101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089992977234893116916067 12134989465852339675374101)
              ·
                refine ⟨568827631211828422283161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12134989465852339675374101 568827631211828422283161)
                ·
                  refine ⟨426620723408871316712371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568827631211828422283161 426620723408871316712371)
                  ·
                    rfl

theorem cell20_934696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_934696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934696 prefixEnd_934696 := by exact prefixLift 934696
  have htrace : WordTrace (prefixWord ++ tailWord_934696) baseStart_934696 baseEnd_934696 := by
    simpa [prefixWord, tailWord_934696, baseEnd_934696] using wordTrace_append hprefix tailTrace_934696
  have hstable : (prefixWord ++ tailWord_934696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934696).length < 2 ^ (prefixWord ++ tailWord_934696).sum := by decide
  have hdescent : baseEnd_934696 < baseStart_934696 := by decide
  rcases family_descends (prefixWord ++ tailWord_934696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934726 : List Nat := [6, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_934726 : Nat := 118140960795 + 934726 * 2 ^ 59
def prefixEnd_934726 : Nat := 4983230072969 + 3 ^ 40 * 934726 * 2
def baseEnd_934726 : Nat := 426634416226324545712249

theorem tailTrace_934726 : CollatzResearch.WordTrace tailWord_934726 prefixEnd_934726 426634416226324545712249 := by
  unfold tailWord_934726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065383062864212979263751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22728172007769876890960021 1065383062864212979263751)
  ·
    refine ⟨1598074594296319468895627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1065383062864212979263751 1598074594296319468895627)
    ·
      refine ⟨2397111891444479203343441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1598074594296319468895627 2397111891444479203343441)
      ·
        refine ⟨1797833918583359402507581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2397111891444479203343441 1797833918583359402507581)
        ·
          refine ⟨674187719468759775940343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1797833918583359402507581 674187719468759775940343)
          ·
            refine ⟨1011281579203139663910515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674187719468759775940343 1011281579203139663910515)
            ·
              refine ⟨1516922368804709495865773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011281579203139663910515 1516922368804709495865773)
              ·
                refine ⟨568845888301766060949665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1516922368804709495865773 568845888301766060949665)
                ·
                  refine ⟨426634416226324545712249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568845888301766060949665 426634416226324545712249)
                  ·
                    rfl

theorem cell20_934726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_934726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934726 prefixEnd_934726 := by exact prefixLift 934726
  have htrace : WordTrace (prefixWord ++ tailWord_934726) baseStart_934726 baseEnd_934726 := by
    simpa [prefixWord, tailWord_934726, baseEnd_934726] using wordTrace_append hprefix tailTrace_934726
  have hstable : (prefixWord ++ tailWord_934726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934726).length < 2 ^ (prefixWord ++ tailWord_934726).sum := by decide
  have hdescent : baseEnd_934726 < baseStart_934726 := by decide
  rcases family_descends (prefixWord ++ tailWord_934726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934745 : List Nat := [1, 2, 1, 2, 2, 4, 8]
def baseStart_934745 : Nat := 118140960795 + 934745 * 2 ^ 59
def prefixEnd_934745 : Nat := 4983230072969 + 3 ^ 40 * 934745 * 2
def baseEnd_934745 : Nat := 47404787593782769342093

theorem tailTrace_934745 : CollatzResearch.WordTrace tailWord_934745 prefixEnd_934745 47404787593782769342093 := by
  unfold tailWord_934745
  simp only [CollatzResearch.WordTrace]
  refine ⟨34092950998585981581381689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22728633999057321054254459 34092950998585981581381689)
  ·
    refine ⟨25569713248939486186036267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34092950998585981581381689 25569713248939486186036267)
    ·
      refine ⟨38354569873409229279054401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25569713248939486186036267 38354569873409229279054401)
      ·
        refine ⟨28765927405056921959290801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38354569873409229279054401 28765927405056921959290801)
        ·
          refine ⟨21574445553792691469468101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28765927405056921959290801 21574445553792691469468101)
          ·
            refine ⟨4045208541336129650525269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21574445553792691469468101 4045208541336129650525269)
            ·
              refine ⟨47404787593782769342093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4045208541336129650525269 47404787593782769342093)
              ·
                rfl

theorem cell20_934745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 8].length) (baseStart_934745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934745 prefixEnd_934745 := by exact prefixLift 934745
  have htrace : WordTrace (prefixWord ++ tailWord_934745) baseStart_934745 baseEnd_934745 := by
    simpa [prefixWord, tailWord_934745, baseEnd_934745] using wordTrace_append hprefix tailTrace_934745
  have hstable : (prefixWord ++ tailWord_934745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934745).length < 2 ^ (prefixWord ++ tailWord_934745).sum := by decide
  have hdescent : baseEnd_934745 < baseStart_934745 := by decide
  rcases family_descends (prefixWord ++ tailWord_934745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934748 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_934748 : Nat := 118140960795 + 934748 * 2 ^ 59
def prefixEnd_934748 : Nat := 4983230072969 + 3 ^ 40 * 934748 * 2
def baseEnd_934748 : Nat := 426644457625790246978825

theorem tailTrace_934748 : CollatzResearch.WordTrace tailWord_934748 prefixEnd_934748 426644457625790246978825 := by
  unfold tailWord_934748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17046530208787556546870449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22728706945050075395827265 17046530208787556546870449)
  ·
    refine ⟨12784897656590667410152837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17046530208787556546870449 12784897656590667410152837)
    ·
      refine ⟨2397168310610750139403657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12784897656590667410152837 2397168310610750139403657)
      ·
        refine ⟨1797876232958062604552743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2397168310610750139403657 1797876232958062604552743)
        ·
          refine ⟨2696814349437093906829115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797876232958062604552743 2696814349437093906829115)
          ·
            refine ⟨4045221524155640860243673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696814349437093906829115 4045221524155640860243673)
            ·
              refine ⟨3033916143116730645182755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4045221524155640860243673 3033916143116730645182755)
              ·
                refine ⟨4550874214675095967774133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033916143116730645182755 4550874214675095967774133)
                ·
                  refine ⟨426644457625790246978825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4550874214675095967774133 426644457625790246978825)
                  ·
                    rfl

theorem cell20_934748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_934748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934748 prefixEnd_934748 := by exact prefixLift 934748
  have htrace : WordTrace (prefixWord ++ tailWord_934748) baseStart_934748 baseEnd_934748 := by
    simpa [prefixWord, tailWord_934748, baseEnd_934748] using wordTrace_append hprefix tailTrace_934748
  have hstable : (prefixWord ++ tailWord_934748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934748).length < 2 ^ (prefixWord ++ tailWord_934748).sum := by decide
  have hdescent : baseEnd_934748 < baseStart_934748 := by decide
  rcases family_descends (prefixWord ++ tailWord_934748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934755 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_934755 : Nat := 118140960795 + 934755 * 2 ^ 59
def prefixEnd_934755 : Nat := 4983230072969 + 3 ^ 40 * 934755 * 2
def baseEnd_934755 : Nat := 426647652616529333745463

theorem tailTrace_934755 : CollatzResearch.WordTrace tailWord_934755 prefixEnd_934755 426647652616529333745463 := by
  unfold tailWord_934755
  simp only [CollatzResearch.WordTrace]
  refine ⟨34093315728549753289245719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22728877152366502192830479 34093315728549753289245719)
  ·
    refine ⟨51139973592824629933868579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34093315728549753289245719 51139973592824629933868579)
    ·
      refine ⟨76709960389236944900802869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51139973592824629933868579 76709960389236944900802869)
      ·
        refine ⟨7191558786490963584450269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76709960389236944900802869 7191558786490963584450269)
        ·
          refine ⟨2696834544934111344168851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7191558786490963584450269 2696834544934111344168851)
          ·
            refine ⟨4045251817401167016253277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696834544934111344168851 4045251817401167016253277)
            ·
              refine ⟨1516969431525437631094979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4045251817401167016253277 1516969431525437631094979)
              ·
                refine ⟨2275454147288156446642469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516969431525437631094979 2275454147288156446642469)
                ·
                  refine ⟨426647652616529333745463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2275454147288156446642469 426647652616529333745463)
                  ·
                    rfl

theorem cell20_934755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_934755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934755 prefixEnd_934755 := by exact prefixLift 934755
  have htrace : WordTrace (prefixWord ++ tailWord_934755) baseStart_934755 baseEnd_934755 := by
    simpa [prefixWord, tailWord_934755, baseEnd_934755] using wordTrace_append hprefix tailTrace_934755
  have hstable : (prefixWord ++ tailWord_934755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934755).length < 2 ^ (prefixWord ++ tailWord_934755).sum := by decide
  have hdescent : baseEnd_934755 < baseStart_934755 := by decide
  rcases family_descends (prefixWord ++ tailWord_934755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934783 : List Nat := [1, 1, 2, 2, 1, 1, 6, 6]
def baseStart_934783 : Nat := 118140960795 + 934783 * 2 ^ 59
def prefixEnd_934783 : Nat := 4983230072969 + 3 ^ 40 * 934783 * 2
def baseEnd_934783 : Nat := 142220144193161893604005

theorem tailTrace_934783 : CollatzResearch.WordTrace tailWord_934783 prefixEnd_934783 142220144193161893604005 := by
  unfold tailWord_934783
  simp only [CollatzResearch.WordTrace]
  refine ⟨34094336972448314071265003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22729557981632209380843335 34094336972448314071265003)
  ·
    refine ⟨51141505458672471106897505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34094336972448314071265003 51141505458672471106897505)
    ·
      refine ⟨38356129094004353330173129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51141505458672471106897505 38356129094004353330173129)
      ·
        refine ⟨28767096820503264997629847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38356129094004353330173129 28767096820503264997629847)
        ·
          refine ⟨43150645230754897496444771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28767096820503264997629847 43150645230754897496444771)
          ·
            refine ⟨64725967846132346244667157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43150645230754897496444771 64725967846132346244667157)
            ·
              refine ⟨3034029742787453730218773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64725967846132346244667157 3034029742787453730218773)
              ·
                refine ⟨142220144193161893604005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3034029742787453730218773 142220144193161893604005)
                ·
                  rfl

theorem cell20_934783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_934783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934783 prefixEnd_934783 := by exact prefixLift 934783
  have htrace : WordTrace (prefixWord ++ tailWord_934783) baseStart_934783 baseEnd_934783 := by
    simpa [prefixWord, tailWord_934783, baseEnd_934783] using wordTrace_append hprefix tailTrace_934783
  have hstable : (prefixWord ++ tailWord_934783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934783).length < 2 ^ (prefixWord ++ tailWord_934783).sum := by decide
  have hdescent : baseEnd_934783 < baseStart_934783 := by decide
  rcases family_descends (prefixWord ++ tailWord_934783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934817 : List Nat := [1, 2, 3, 4, 1, 3, 1, 5]
def baseStart_934817 : Nat := 118140960795 + 934817 * 2 ^ 59
def prefixEnd_934817 : Nat := 4983230072969 + 3 ^ 40 * 934817 * 2
def baseEnd_934817 : Nat := 142225317035310891226181

theorem tailTrace_934817 : CollatzResearch.WordTrace tailWord_934817 prefixEnd_934817 142225317035310891226181 := by
  unfold tailWord_934817
  simp only [CollatzResearch.WordTrace]
  refine ⟨34095577054325137878002705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22730384702883425252001803 34095577054325137878002705)
  ·
    refine ⟨25571682790743853408502029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34095577054325137878002705 25571682790743853408502029)
    ·
      refine ⟨9589381046528945028188261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25571682790743853408502029 9589381046528945028188261)
      ·
        refine ⟨1798008946224177192785299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9589381046528945028188261 1798008946224177192785299)
        ·
          refine ⟨2697013419336265789177949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798008946224177192785299 2697013419336265789177949)
          ·
            refine ⟨1011380032251099670941731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2697013419336265789177949 1011380032251099670941731)
            ·
              refine ⟨1517070048376649506412597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011380032251099670941731 1517070048376649506412597)
              ·
                refine ⟨142225317035310891226181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1517070048376649506412597 142225317035310891226181)
                ·
                  rfl

theorem cell20_934817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 5].length) (baseStart_934817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934817 prefixEnd_934817 := by exact prefixLift 934817
  have htrace : WordTrace (prefixWord ++ tailWord_934817) baseStart_934817 baseEnd_934817 := by
    simpa [prefixWord, tailWord_934817, baseEnd_934817] using wordTrace_append hprefix tailTrace_934817
  have hstable : (prefixWord ++ tailWord_934817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934817).length < 2 ^ (prefixWord ++ tailWord_934817).sum := by decide
  have hdescent : baseEnd_934817 < baseStart_934817 := by decide
  rcases family_descends (prefixWord ++ tailWord_934817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934848 : List Nat := [2, 1, 1, 2, 3, 4, 2, 3, 2]
def baseStart_934848 : Nat := 118140960795 + 934848 * 2 ^ 59
def prefixEnd_934848 : Nat := 4983230072969 + 3 ^ 40 * 934848 * 2
def baseEnd_934848 : Nat := 426690100350634343645083

theorem tailTrace_934848 : CollatzResearch.WordTrace tailWord_934848 prefixEnd_934848 426690100350634343645083 := by
  unfold tailWord_934848
  simp only [CollatzResearch.WordTrace]
  refine ⟨17048353858606415086190599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22731138478141886781587465 17048353858606415086190599)
  ·
    refine ⟨25572530787909622629285899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17048353858606415086190599 25572530787909622629285899)
    ·
      refine ⟨38358796181864433943928849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25572530787909622629285899 38358796181864433943928849)
      ·
        refine ⟨28769097136398325457946637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38358796181864433943928849 28769097136398325457946637)
        ·
          refine ⟨10788411426149372046729989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28769097136398325457946637 10788411426149372046729989)
          ·
            refine ⟨2022827142403007258761873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10788411426149372046729989 2022827142403007258761873)
            ·
              refine ⟨1517120356802255444071405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022827142403007258761873 1517120356802255444071405)
              ·
                refine ⟨568920133800845791526777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1517120356802255444071405 568920133800845791526777)
                ·
                  refine ⟨426690100350634343645083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568920133800845791526777 426690100350634343645083)
                  ·
                    rfl

theorem cell20_934848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_934848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934848 prefixEnd_934848 := by exact prefixLift 934848
  have htrace : WordTrace (prefixWord ++ tailWord_934848) baseStart_934848 baseEnd_934848 := by
    simpa [prefixWord, tailWord_934848, baseEnd_934848] using wordTrace_append hprefix tailTrace_934848
  have hstable : (prefixWord ++ tailWord_934848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934848).length < 2 ^ (prefixWord ++ tailWord_934848).sum := by decide
  have hdescent : baseEnd_934848 < baseStart_934848 := by decide
  rcases family_descends (prefixWord ++ tailWord_934848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934859 : List Nat := [1, 1, 1, 1, 3, 6, 7]
def baseStart_934859 : Nat := 118140960795 + 934859 * 2 ^ 59
def prefixEnd_934859 : Nat := 4983230072969 + 3 ^ 40 * 934859 * 2
def baseEnd_934859 : Nat := 47410569005596354919819

theorem tailTrace_934859 : CollatzResearch.WordTrace tailWord_934859 prefixEnd_934859 47410569005596354919819 := by
  unfold tailWord_934859
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097108920172979051031631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22731405946781986034021087 34097108920172979051031631)
  ·
    refine ⟨51145663380259468576547447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34097108920172979051031631 51145663380259468576547447)
    ·
      refine ⟨76718495070389202864821171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51145663380259468576547447 76718495070389202864821171)
      ·
        refine ⟨115077742605583804297231757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76718495070389202864821171 115077742605583804297231757)
        ·
          refine ⟨43154153477093926611461909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115077742605583804297231757 43154153477093926611461909)
          ·
            refine ⟨2022850944238777809912277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43154153477093926611461909 2022850944238777809912277)
            ·
              refine ⟨47410569005596354919819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2022850944238777809912277 47410569005596354919819)
              ·
                rfl

theorem cell20_934859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 7].length) (baseStart_934859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934859 prefixEnd_934859 := by exact prefixLift 934859
  have htrace : WordTrace (prefixWord ++ tailWord_934859) baseStart_934859 baseEnd_934859 := by
    simpa [prefixWord, tailWord_934859, baseEnd_934859] using wordTrace_append hprefix tailTrace_934859
  have hstable : (prefixWord ++ tailWord_934859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934859).length < 2 ^ (prefixWord ++ tailWord_934859).sum := by decide
  have hdescent : baseEnd_934859 < baseStart_934859 := by decide
  rcases family_descends (prefixWord ++ tailWord_934859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934862 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_934862 : Nat := 118140960795 + 934862 * 2 ^ 59
def prefixEnd_934862 : Nat := 4983230072969 + 3 ^ 40 * 934862 * 2
def baseEnd_934862 : Nat := 426696490332112517178359

theorem tailTrace_934862 : CollatzResearch.WordTrace tailWord_934862 prefixEnd_934862 426696490332112517178359 := by
  unfold tailWord_934862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262152292395263820423855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22731478892774740375593893 4262152292395263820423855)
  ·
    refine ⟨6393228438592895730635783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4262152292395263820423855 6393228438592895730635783)
    ·
      refine ⟨9589842657889343595953675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6393228438592895730635783 9589842657889343595953675)
      ·
        refine ⟨14384763986834015393930513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9589842657889343595953675 14384763986834015393930513)
        ·
          refine ⟨10788572990125511545447885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14384763986834015393930513 10788572990125511545447885)
          ·
            refine ⟨4045714871297066829542957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10788572990125511545447885 4045714871297066829542957)
            ·
              refine ⟨1517143076736400061078609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4045714871297066829542957 1517143076736400061078609)
              ·
                refine ⟨1137857307552300045808957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517143076736400061078609 1137857307552300045808957)
                ·
                  refine ⟨426696490332112517178359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137857307552300045808957 426696490332112517178359)
                  ·
                    rfl

theorem cell20_934862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_934862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934862 prefixEnd_934862 := by exact prefixLift 934862
  have htrace : WordTrace (prefixWord ++ tailWord_934862) baseStart_934862 baseEnd_934862 := by
    simpa [prefixWord, tailWord_934862, baseEnd_934862] using wordTrace_append hprefix tailTrace_934862
  have hstable : (prefixWord ++ tailWord_934862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934862).length < 2 ^ (prefixWord ++ tailWord_934862).sum := by decide
  have hdescent : baseEnd_934862 < baseStart_934862 := by decide
  rcases family_descends (prefixWord ++ tailWord_934862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934879 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 3]
def baseStart_934879 : Nat := 118140960795 + 934879 * 2 ^ 59
def prefixEnd_934879 : Nat := 4983230072969 + 3 ^ 40 * 934879 * 2
def baseEnd_934879 : Nat := 426704249595336013611623

theorem tailTrace_934879 : CollatzResearch.WordTrace tailWord_934879 prefixEnd_934879 426704249595336013611623 := by
  unfold tailWord_934879
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097838380100522466759691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22731892253400348311173127 34097838380100522466759691)
  ·
    refine ⟨51146757570150783700139537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34097838380100522466759691 51146757570150783700139537)
    ·
      refine ⟨38360068177613087775104653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51146757570150783700139537 38360068177613087775104653)
      ·
        refine ⟨14385025566604907915664245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38360068177613087775104653 14385025566604907915664245)
        ·
          refine ⟨1348596146869210117093523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14385025566604907915664245 1348596146869210117093523)
          ·
            refine ⟨2022894220303815175640285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348596146869210117093523 2022894220303815175640285)
            ·
              refine ⟨758585332613930690865107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2022894220303815175640285 758585332613930690865107)
              ·
                refine ⟨1137877998920896036297661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758585332613930690865107 1137877998920896036297661)
                ·
                  refine ⟨426704249595336013611623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137877998920896036297661 426704249595336013611623)
                  ·
                    rfl

theorem cell20_934879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 3].length) (baseStart_934879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934879 prefixEnd_934879 := by exact prefixLift 934879
  have htrace : WordTrace (prefixWord ++ tailWord_934879) baseStart_934879 baseEnd_934879 := by
    simpa [prefixWord, tailWord_934879, baseEnd_934879] using wordTrace_append hprefix tailTrace_934879
  have hstable : (prefixWord ++ tailWord_934879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934879).length < 2 ^ (prefixWord ++ tailWord_934879).sum := by decide
  have hdescent : baseEnd_934879 < baseStart_934879 := by decide
  rcases family_descends (prefixWord ++ tailWord_934879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934910 : List Nat := [4, 2, 2, 2, 3, 1, 6]
def baseStart_934910 : Nat := 118140960795 + 934910 * 2 ^ 59
def prefixEnd_934910 : Nat := 4983230072969 + 3 ^ 40 * 934910 * 2
def baseEnd_934910 : Nat := 47413155426670853730907

theorem tailTrace_934910 : CollatzResearch.WordTrace tailWord_934910 prefixEnd_934910 47413155426670853730907 := by
  unfold tailWord_934910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262371130373526845142273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22732646028658809840758789 4262371130373526845142273)
  ·
    refine ⟨3196778347780145133856705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4262371130373526845142273 3196778347780145133856705)
    ·
      refine ⟨2397583760835108850392529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3196778347780145133856705 2397583760835108850392529)
      ·
        refine ⟨1798187820626331637794397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2397583760835108850392529 1798187820626331637794397)
        ·
          refine ⟨674320432734874364172899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1798187820626331637794397 674320432734874364172899)
          ·
            refine ⟨1011480649102311546259349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674320432734874364172899 1011480649102311546259349)
            ·
              refine ⟨47413155426670853730907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1011480649102311546259349 47413155426670853730907)
              ·
                rfl

theorem cell20_934910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 6].length) (baseStart_934910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934910 prefixEnd_934910 := by exact prefixLift 934910
  have htrace : WordTrace (prefixWord ++ tailWord_934910) baseStart_934910 baseEnd_934910 := by
    simpa [prefixWord, tailWord_934910, baseEnd_934910] using wordTrace_append hprefix tailTrace_934910
  have hstable : (prefixWord ++ tailWord_934910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934910).length < 2 ^ (prefixWord ++ tailWord_934910).sum := by decide
  have hdescent : baseEnd_934910 < baseStart_934910 := by decide
  rcases family_descends (prefixWord ++ tailWord_934910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934930 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_934930 : Nat := 118140960795 + 934930 * 2 ^ 59
def prefixEnd_934930 : Nat := 4983230072969 + 3 ^ 40 * 934930 * 2
def baseEnd_934930 : Nat := 426727527385006502911415

theorem tailTrace_934930 : CollatzResearch.WordTrace tailWord_934930 prefixEnd_934930 426727527385006502911415 := by
  unfold tailWord_934930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8524924625728939544216561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22733132335277172117910829 8524924625728939544216561)
  ·
    refine ⟨6393693469296704658162421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8524924625728939544216561 6393693469296704658162421)
    ·
      refine ⟨599408762746566061702727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6393693469296704658162421 599408762746566061702727)
      ·
        refine ⟨899113144119849092554091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599408762746566061702727 899113144119849092554091)
        ·
          refine ⟨1348669716179773638831137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899113144119849092554091 1348669716179773638831137)
          ·
            refine ⟨1011502287134830229123353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1348669716179773638831137 1011502287134830229123353)
            ·
              refine ⟨758626715351122671842515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011502287134830229123353 758626715351122671842515)
              ·
                refine ⟨1137940073026684007763773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758626715351122671842515 1137940073026684007763773)
                ·
                  refine ⟨426727527385006502911415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137940073026684007763773 426727527385006502911415)
                  ·
                    rfl

theorem cell20_934930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_934930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934930 prefixEnd_934930 := by exact prefixLift 934930
  have htrace : WordTrace (prefixWord ++ tailWord_934930) baseStart_934930 baseEnd_934930 := by
    simpa [prefixWord, tailWord_934930, baseEnd_934930] using wordTrace_append hprefix tailTrace_934930
  have hstable : (prefixWord ++ tailWord_934930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934930).length < 2 ^ (prefixWord ++ tailWord_934930).sum := by decide
  have hdescent : baseEnd_934930 < baseStart_934930 := by decide
  rcases family_descends (prefixWord ++ tailWord_934930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934973 : List Nat := [1, 4, 1, 3, 1, 10]
def baseStart_934973 : Nat := 118140960795 + 934973 * 2 ^ 59
def prefixEnd_934973 : Nat := 4983230072969 + 3 ^ 40 * 934973 * 2
def baseEnd_934973 : Nat := 15805450139136646832515

theorem tailTrace_934973 : CollatzResearch.WordTrace tailWord_934973 prefixEnd_934973 15805450139136646832515 := by
  unfold tailWord_934973
  simp only [CollatzResearch.WordTrace]
  refine ⟨34101266841759976520681573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22734177894506651013787715 34101266841759976520681573)
  ·
    refine ⟨6393987532829995597627795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34101266841759976520681573 6393987532829995597627795)
    ·
      refine ⟨9590981299244993396441693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6393987532829995597627795 9590981299244993396441693)
      ·
        refine ⟨3596617987216872523665635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9590981299244993396441693 3596617987216872523665635)
        ·
          refine ⟨5394926980825308785498453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3596617987216872523665635 5394926980825308785498453)
          ·
            refine ⟨15805450139136646832515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5394926980825308785498453 15805450139136646832515)
            ·
              rfl

theorem cell20_934973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 10].length) (baseStart_934973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934973 prefixEnd_934973 := by exact prefixLift 934973
  have htrace : WordTrace (prefixWord ++ tailWord_934973) baseStart_934973 baseEnd_934973 := by
    simpa [prefixWord, tailWord_934973, baseEnd_934973] using wordTrace_append hprefix tailTrace_934973
  have hstable : (prefixWord ++ tailWord_934973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934973).length < 2 ^ (prefixWord ++ tailWord_934973).sum := by decide
  have hdescent : baseEnd_934973 < baseStart_934973 := by decide
  rcases family_descends (prefixWord ++ tailWord_934973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934997 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 3]
def baseStart_934997 : Nat := 118140960795 + 934997 * 2 ^ 59
def prefixEnd_934997 : Nat := 4983230072969 + 3 ^ 40 * 934997 * 2
def baseEnd_934997 : Nat := 426758108010652047677807

theorem tailTrace_934997 : CollatzResearch.WordTrace tailWord_934997 prefixEnd_934997 426758108010652047677807 := by
  unfold tailWord_934997
  simp only [CollatzResearch.WordTrace]
  refine ⟨34102142193673028619555245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22734761462448685746370163 34102142193673028619555245)
  ·
    refine ⟨12788303322627385732333217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34102142193673028619555245 12788303322627385732333217)
    ·
      refine ⟨9591227491970539299249913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12788303322627385732333217 9591227491970539299249913)
      ·
        refine ⟨7193420618977904474437435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9591227491970539299249913 7193420618977904474437435)
        ·
          refine ⟨10790130928466856711656153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7193420618977904474437435 10790130928466856711656153)
          ·
            refine ⟨8092598196350142533742115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10790130928466856711656153 8092598196350142533742115)
            ·
              refine ⟨12138897294525213800613173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092598196350142533742115 12138897294525213800613173)
              ·
                refine ⟨1138021621361738793807485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12138897294525213800613173 1138021621361738793807485)
                ·
                  refine ⟨426758108010652047677807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138021621361738793807485 426758108010652047677807)
                  ·
                    rfl

theorem cell20_934997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_934997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_934997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_934997 prefixEnd_934997 := by exact prefixLift 934997
  have htrace : WordTrace (prefixWord ++ tailWord_934997) baseStart_934997 baseEnd_934997 := by
    simpa [prefixWord, tailWord_934997, baseEnd_934997] using wordTrace_append hprefix tailTrace_934997
  have hstable : (prefixWord ++ tailWord_934997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934997).length < 2 ^ (prefixWord ++ tailWord_934997).sum := by decide
  have hdescent : baseEnd_934997 < baseStart_934997 := by decide
  rcases family_descends (prefixWord ++ tailWord_934997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935066 : List Nat := [3, 1, 1, 5, 1, 2, 1, 6]
def baseStart_935066 : Nat := 118140960795 + 935066 * 2 ^ 59
def prefixEnd_935066 : Nat := 4983230072969 + 3 ^ 40 * 935066 * 2
def baseEnd_935066 : Nat := 142263200496931491459175

theorem tailTrace_935066 : CollatzResearch.WordTrace tailWord_935066 prefixEnd_935066 142263200496931491459175 := by
  unfold tailWord_935066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526164707605763350954263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22736439220282035602544701 8526164707605763350954263)
  ·
    refine ⟨12789247061408645026431395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8526164707605763350954263 12789247061408645026431395)
    ·
      refine ⟨19183870592112967539647093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12789247061408645026431395 19183870592112967539647093)
      ·
        refine ⟨1798487868010590706841915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19183870592112967539647093 1798487868010590706841915)
        ·
          refine ⟨2697731802015886060262873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798487868010590706841915 2697731802015886060262873)
          ·
            refine ⟨2023298851511914545197155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2697731802015886060262873 2023298851511914545197155)
            ·
              refine ⟨3034948277267871817795733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023298851511914545197155 3034948277267871817795733)
              ·
                refine ⟨142263200496931491459175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3034948277267871817795733 142263200496931491459175)
                ·
                  rfl

theorem cell20_935066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_935066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935066 prefixEnd_935066 := by exact prefixLift 935066
  have htrace : WordTrace (prefixWord ++ tailWord_935066) baseStart_935066 baseEnd_935066 := by
    simpa [prefixWord, tailWord_935066, baseEnd_935066] using wordTrace_append hprefix tailTrace_935066
  have hstable : (prefixWord ++ tailWord_935066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935066).length < 2 ^ (prefixWord ++ tailWord_935066).sum := by decide
  have hdescent : baseEnd_935066 < baseStart_935066 := by decide
  rcases family_descends (prefixWord ++ tailWord_935066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935076 : List Nat := [2, 3, 1, 2, 3, 1, 3, 3, 2]
def baseStart_935076 : Nat := 118140960795 + 935076 * 2 ^ 59
def prefixEnd_935076 : Nat := 4983230072969 + 3 ^ 40 * 935076 * 2
def baseEnd_935076 : Nat := 426794165763278884044151

theorem tailTrace_935076 : CollatzResearch.WordTrace tailWord_935076 prefixEnd_935076 426794165763278884044151 := by
  unfold tailWord_935076
  simp only [CollatzResearch.WordTrace]
  refine ⟨17052511780193412555840541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22736682373591216741120721 17052511780193412555840541)
  ·
    refine ⟨6394691917572529708440203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17052511780193412555840541 6394691917572529708440203)
    ·
      refine ⟨9592037876358794562660305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6394691917572529708440203 9592037876358794562660305)
      ·
        refine ⟨7194028407269095921995229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9592037876358794562660305 7194028407269095921995229)
        ·
          refine ⟨2697760652725910970748211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7194028407269095921995229 2697760652725910970748211)
          ·
            refine ⟨4046640979088866456122317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697760652725910970748211 4046640979088866456122317)
            ·
              refine ⟨1517490367158324921045869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4046640979088866456122317 1517490367158324921045869)
              ·
                refine ⟨569058887684371845392201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1517490367158324921045869 569058887684371845392201)
                ·
                  refine ⟨426794165763278884044151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569058887684371845392201 426794165763278884044151)
                  ·
                    rfl

theorem cell20_935076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_935076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935076 prefixEnd_935076 := by exact prefixLift 935076
  have htrace : WordTrace (prefixWord ++ tailWord_935076) baseStart_935076 baseEnd_935076 := by
    simpa [prefixWord, tailWord_935076, baseEnd_935076] using wordTrace_append hprefix tailTrace_935076
  have hstable : (prefixWord ++ tailWord_935076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935076).length < 2 ^ (prefixWord ++ tailWord_935076).sum := by decide
  have hdescent : baseEnd_935076 < baseStart_935076 := by decide
  rcases family_descends (prefixWord ++ tailWord_935076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935097 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 4]
def baseStart_935097 : Nat := 118140960795 + 935097 * 2 ^ 59
def prefixEnd_935097 : Nat := 4983230072969 + 3 ^ 40 * 935097 * 2
def baseEnd_935097 : Nat := 426803750735496144344065

theorem tailTrace_935097 : CollatzResearch.WordTrace tailWord_935097 prefixEnd_935097 426803750735496144344065 := by
  unfold tailWord_935097
  simp only [CollatzResearch.WordTrace]
  refine ⟨34105789493310745698195545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22737192995540497132130363 34105789493310745698195545)
  ·
    refine ⟨25579342119983059273646659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34105789493310745698195545 25579342119983059273646659)
    ·
      refine ⟨38369013179974588910469989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25579342119983059273646659 38369013179974588910469989)
      ·
        refine ⟨7194189971245235420713123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38369013179974588910469989 7194189971245235420713123)
        ·
          refine ⟨10791284956867853131069685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7194189971245235420713123 10791284956867853131069685)
          ·
            refine ⟨1011682964706361231037783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10791284956867853131069685 1011682964706361231037783)
            ·
              refine ⟨1517524447059541846556675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011682964706361231037783 1517524447059541846556675)
              ·
                refine ⟨2276286670589312769835013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517524447059541846556675 2276286670589312769835013)
                ·
                  refine ⟨426803750735496144344065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2276286670589312769835013 426803750735496144344065)
                  ·
                    rfl

theorem cell20_935097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_935097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935097 prefixEnd_935097 := by exact prefixLift 935097
  have htrace : WordTrace (prefixWord ++ tailWord_935097) baseStart_935097 baseEnd_935097 := by
    simpa [prefixWord, tailWord_935097, baseEnd_935097] using wordTrace_append hprefix tailTrace_935097
  have hstable : (prefixWord ++ tailWord_935097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935097).length < 2 ^ (prefixWord ++ tailWord_935097).sum := by decide
  have hdescent : baseEnd_935097 < baseStart_935097 := by decide
  rcases family_descends (prefixWord ++ tailWord_935097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935104 : List Nat := [2, 1, 1, 2, 6, 1, 2, 5]
def baseStart_935104 : Nat := 118140960795 + 935104 * 2 ^ 59
def prefixEnd_935104 : Nat := 4983230072969 + 3 ^ 40 * 935104 * 2
def baseEnd_935104 : Nat := 142268981908745077036901

theorem tailTrace_935104 : CollatzResearch.WordTrace tailWord_935104 prefixEnd_935104 142268981908745077036901 := by
  unfold tailWord_935104
  simp only [CollatzResearch.WordTrace]
  refine ⟨17053022402142692946850183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22737363202856923929133577 17053022402142692946850183)
  ·
    refine ⟨25579533603214039420275275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17053022402142692946850183 25579533603214039420275275)
    ·
      refine ⟨38369300404821059130412913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25579533603214039420275275 38369300404821059130412913)
      ·
        refine ⟨28776975303615794347809685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38369300404821059130412913 28776975303615794347809685)
        ·
          refine ⟨1348920717356990360053579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28776975303615794347809685 1348920717356990360053579)
          ·
            refine ⟨2023381076035485540080369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348920717356990360053579 2023381076035485540080369)
            ·
              refine ⟨1517535807026614155060277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023381076035485540080369 1517535807026614155060277)
              ·
                refine ⟨142268981908745077036901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1517535807026614155060277 142268981908745077036901)
                ·
                  rfl

theorem cell20_935104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_935104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935104 prefixEnd_935104 := by exact prefixLift 935104
  have htrace : WordTrace (prefixWord ++ tailWord_935104) baseStart_935104 baseEnd_935104 := by
    simpa [prefixWord, tailWord_935104, baseEnd_935104] using wordTrace_append hprefix tailTrace_935104
  have hstable : (prefixWord ++ tailWord_935104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935104).length < 2 ^ (prefixWord ++ tailWord_935104).sum := by decide
  have hdescent : baseEnd_935104 < baseStart_935104 := by decide
  rcases family_descends (prefixWord ++ tailWord_935104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935166 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_935166 : Nat := 118140960795 + 935166 * 2 ^ 59
def prefixEnd_935166 : Nat := 4983230072969 + 3 ^ 40 * 935166 * 2
def baseEnd_935166 : Nat := 426835244215638571043783

theorem tailTrace_935166 : CollatzResearch.WordTrace tailWord_935166 prefixEnd_935166 426835244215638571043783 := by
  unfold tailWord_935166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4263538266257596310307169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22738870753373846988304901 4263538266257596310307169)
  ·
    refine ⟨3197653699693197232730377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4263538266257596310307169 3197653699693197232730377)
    ·
      refine ⟨2398240274769897924547783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3197653699693197232730377 2398240274769897924547783)
      ·
        refine ⟨3597360412154846886821675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398240274769897924547783 3597360412154846886821675)
        ·
          refine ⟨5396040618232270330232513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597360412154846886821675 5396040618232270330232513)
          ·
            refine ⟨4047030463674202747674385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5396040618232270330232513 4047030463674202747674385)
            ·
              refine ⟨3035272847755652060755789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4047030463674202747674385 3035272847755652060755789)
              ·
                refine ⟨1138227317908369522783421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3035272847755652060755789 1138227317908369522783421)
                ·
                  refine ⟨426835244215638571043783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138227317908369522783421 426835244215638571043783)
                  ·
                    rfl

theorem cell20_935166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_935166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935166 prefixEnd_935166 := by exact prefixLift 935166
  have htrace : WordTrace (prefixWord ++ tailWord_935166) baseStart_935166 baseEnd_935166 := by
    simpa [prefixWord, tailWord_935166, baseEnd_935166] using wordTrace_append hprefix tailTrace_935166
  have hstable : (prefixWord ++ tailWord_935166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935166).length < 2 ^ (prefixWord ++ tailWord_935166).sum := by decide
  have hdescent : baseEnd_935166 < baseStart_935166 := by decide
  rcases family_descends (prefixWord ++ tailWord_935166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935180 : List Nat := [2, 2, 1, 2, 2, 4, 3, 4]
def baseStart_935180 : Nat := 118140960795 + 935180 * 2 ^ 59
def prefixEnd_935180 : Nat := 4983230072969 + 3 ^ 40 * 935180 * 2
def baseEnd_935180 : Nat := 142280544732372248192353

theorem tailTrace_935180 : CollatzResearch.WordTrace tailWord_935180 prefixEnd_935180 142280544732372248192353 := by
  unfold tailWord_935180
  simp only [CollatzResearch.WordTrace]
  refine ⟨17054408376005025436733497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22739211168006700582311329 17054408376005025436733497)
  ·
    refine ⟨12790806282003769077550123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17054408376005025436733497 12790806282003769077550123)
    ·
      refine ⟨19186209423005653616325185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12790806282003769077550123 19186209423005653616325185)
      ·
        refine ⟨14389657067254240212243889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19186209423005653616325185 14389657067254240212243889)
        ·
          refine ⟨10792242800440680159182917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14389657067254240212243889 10792242800440680159182917)
          ·
            refine ⟨2023545525082627529846797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10792242800440680159182917 2023545525082627529846797)
            ·
              refine ⟨758829571905985323692549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2023545525082627529846797 758829571905985323692549)
              ·
                refine ⟨142280544732372248192353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758829571905985323692549 142280544732372248192353)
                ·
                  rfl

theorem cell20_935180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_935180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935180 prefixEnd_935180 := by exact prefixLift 935180
  have htrace : WordTrace (prefixWord ++ tailWord_935180) baseStart_935180 baseEnd_935180 := by
    simpa [prefixWord, tailWord_935180, baseEnd_935180] using wordTrace_append hprefix tailTrace_935180
  have hstable : (prefixWord ++ tailWord_935180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935180).length < 2 ^ (prefixWord ++ tailWord_935180).sum := by decide
  have hdescent : baseEnd_935180 < baseStart_935180 := by decide
  rcases family_descends (prefixWord ++ tailWord_935180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935186 : List Nat := [3, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_935186 : Nat := 118140960795 + 935186 * 2 ^ 59
def prefixEnd_935186 : Nat := 4983230072969 + 3 ^ 40 * 935186 * 2
def baseEnd_935186 : Nat := 426844372760607390377035

theorem tailTrace_935186 : CollatzResearch.WordTrace tailWord_935186 prefixEnd_935186 426844372760607390377035 := by
  unfold tailWord_935186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8527258897497078474546353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22739357059992209265456941 8527258897497078474546353)
  ·
    refine ⟨6395444173122808855909765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8527258897497078474546353 6395444173122808855909765)
    ·
      refine ⟨1199145782460526660483081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6395444173122808855909765 1199145782460526660483081)
      ·
        refine ⟨899359336845394995362311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1199145782460526660483081 899359336845394995362311)
        ·
          refine ⟨1349039005268092493043467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899359336845394995362311 1349039005268092493043467)
          ·
            refine ⟨2023558507902138739565201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349039005268092493043467 2023558507902138739565201)
            ·
              refine ⟨1517668880926604054673901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023558507902138739565201 1517668880926604054673901)
              ·
                refine ⟨569125830347476520502713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1517668880926604054673901 569125830347476520502713)
                ·
                  refine ⟨426844372760607390377035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569125830347476520502713 426844372760607390377035)
                  ·
                    rfl

theorem cell20_935186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_935186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935186 prefixEnd_935186 := by exact prefixLift 935186
  have htrace : WordTrace (prefixWord ++ tailWord_935186) baseStart_935186 baseEnd_935186 := by
    simpa [prefixWord, tailWord_935186, baseEnd_935186] using wordTrace_append hprefix tailTrace_935186
  have hstable : (prefixWord ++ tailWord_935186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935186).length < 2 ^ (prefixWord ++ tailWord_935186).sum := by decide
  have hdescent : baseEnd_935186 < baseStart_935186 := by decide
  rcases family_descends (prefixWord ++ tailWord_935186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935239 : List Nat := [1, 1, 4, 1, 2, 4, 1, 6]
def baseStart_935239 : Nat := 118140960795 + 935239 * 2 ^ 59
def prefixEnd_935239 : Nat := 4983230072969 + 3 ^ 40 * 935239 * 2
def baseEnd_935239 : Nat := 142289521134924920536717

theorem tailTrace_935239 : CollatzResearch.WordTrace tailWord_935239 prefixEnd_935239 142289521134924920536717 := by
  unfold tailWord_935239
  simp only [CollatzResearch.WordTrace]
  refine ⟨34110968658796303949864771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22740645772530869299909847 34110968658796303949864771)
  ·
    refine ⟨51166452988194455924797157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34110968658796303949864771 51166452988194455924797157)
    ·
      refine ⟨9593709935286460485899467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51166452988194455924797157 9593709935286460485899467)
      ·
        refine ⟨14390564902929690728849201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9593709935286460485899467 14390564902929690728849201)
        ·
          refine ⟨10792923677197268046636901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14390564902929690728849201 10792923677197268046636901)
          ·
            refine ⟨2023673189474487758744419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10792923677197268046636901 2023673189474487758744419)
            ·
              refine ⟨3035509784211731638116629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023673189474487758744419 3035509784211731638116629)
              ·
                refine ⟨142289521134924920536717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3035509784211731638116629 142289521134924920536717)
                ·
                  rfl

theorem cell20_935239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_935239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935239 prefixEnd_935239 := by exact prefixLift 935239
  have htrace : WordTrace (prefixWord ++ tailWord_935239) baseStart_935239 baseEnd_935239 := by
    simpa [prefixWord, tailWord_935239, baseEnd_935239] using wordTrace_append hprefix tailTrace_935239
  have hstable : (prefixWord ++ tailWord_935239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935239).length < 2 ^ (prefixWord ++ tailWord_935239).sum := by decide
  have hdescent : baseEnd_935239 < baseStart_935239 := by decide
  rcases family_descends (prefixWord ++ tailWord_935239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935246 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_935246 : Nat := 118140960795 + 935246 * 2 ^ 59
def prefixEnd_935246 : Nat := 4983230072969 + 3 ^ 40 * 935246 * 2
def baseEnd_935246 : Nat := 426871758395513848376789

theorem tailTrace_935246 : CollatzResearch.WordTrace tailWord_935246 prefixEnd_935246 426871758395513848376789 := by
  unfold tailWord_935246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4263902996221368018171199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22740815979847296096913061 4263902996221368018171199)
  ·
    refine ⟨6395854494332052027256799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4263902996221368018171199 6395854494332052027256799)
    ·
      refine ⟨9593781741498078040885199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6395854494332052027256799 9593781741498078040885199)
      ·
        refine ⟨14390672612247117061327799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9593781741498078040885199 14390672612247117061327799)
        ·
          refine ⟨21586008918370675591991699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14390672612247117061327799 21586008918370675591991699)
          ·
            refine ⟨32379013377556013387987549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21586008918370675591991699 32379013377556013387987549)
            ·
              refine ⟨12142130016583505020495331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32379013377556013387987549 12142130016583505020495331)
              ·
                refine ⟨18213195024875257530742997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12142130016583505020495331 18213195024875257530742997)
                ·
                  refine ⟨426871758395513848376789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18213195024875257530742997 426871758395513848376789)
                  ·
                    rfl

theorem cell20_935246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_935246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935246 prefixEnd_935246 := by exact prefixLift 935246
  have htrace : WordTrace (prefixWord ++ tailWord_935246) baseStart_935246 baseEnd_935246 := by
    simpa [prefixWord, tailWord_935246, baseEnd_935246] using wordTrace_append hprefix tailTrace_935246
  have hstable : (prefixWord ++ tailWord_935246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935246).length < 2 ^ (prefixWord ++ tailWord_935246).sum := by decide
  have hdescent : baseEnd_935246 < baseStart_935246 := by decide
  rcases family_descends (prefixWord ++ tailWord_935246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935277 : List Nat := [1, 5, 1, 1, 1, 3, 1, 7]
def baseStart_935277 : Nat := 118140960795 + 935277 * 2 ^ 59
def prefixEnd_935277 : Nat := 4983230072969 + 3 ^ 40 * 935277 * 2
def baseEnd_935277 : Nat := 142295302546738506114443

theorem tailTrace_935277 : CollatzResearch.WordTrace tailWord_935277 prefixEnd_935277 142295302546738506114443 := by
  unfold tailWord_935277
  simp only [CollatzResearch.WordTrace]
  refine ⟨34112354632658636439748085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22741569755105757626498723 34112354632658636439748085)
  ·
    refine ⟨3198033246811747166226383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34112354632658636439748085 3198033246811747166226383)
    ·
      refine ⟨4797049870217620749339575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3198033246811747166226383 4797049870217620749339575)
      ·
        refine ⟨7195574805326431124009363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4797049870217620749339575 7195574805326431124009363)
        ·
          refine ⟨10793362207989646686014045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7195574805326431124009363 10793362207989646686014045)
          ·
            refine ⟨4047510827996117507255267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10793362207989646686014045 4047510827996117507255267)
            ·
              refine ⟨6071266241994176260882901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047510827996117507255267 6071266241994176260882901)
              ·
                refine ⟨142295302546738506114443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6071266241994176260882901 142295302546738506114443)
                ·
                  rfl

theorem cell20_935277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_935277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935277 prefixEnd_935277 := by exact prefixLift 935277
  have htrace : WordTrace (prefixWord ++ tailWord_935277) baseStart_935277 baseEnd_935277 := by
    simpa [prefixWord, tailWord_935277, baseEnd_935277] using wordTrace_append hprefix tailTrace_935277
  have hstable : (prefixWord ++ tailWord_935277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935277).length < 2 ^ (prefixWord ++ tailWord_935277).sum := by decide
  have hdescent : baseEnd_935277 < baseStart_935277 := by decide
  rcases family_descends (prefixWord ++ tailWord_935277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935291 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_935291 : Nat := 118140960795 + 935291 * 2 ^ 59
def prefixEnd_935291 : Nat := 4983230072969 + 3 ^ 40 * 935291 * 2
def baseEnd_935291 : Nat := 426892297621693691876605

theorem tailTrace_935291 : CollatzResearch.WordTrace tailWord_935291 prefixEnd_935291 426892297621693691876605 := by
  unfold tailWord_935291
  simp only [CollatzResearch.WordTrace]
  refine ⟨34112865254607916830757727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22741910169738611220505151 34112865254607916830757727)
  ·
    refine ⟨51169297881911875246136591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34112865254607916830757727 51169297881911875246136591)
    ·
      refine ⟨76753946822867812869204887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51169297881911875246136591 76753946822867812869204887)
      ·
        refine ⟨115130920234301719303807331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76753946822867812869204887 115130920234301719303807331)
        ·
          refine ⟨172696380351452578955710997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115130920234301719303807331 172696380351452578955710997)
          ·
            refine ⟨8095142828974339638548953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172696380351452578955710997 8095142828974339638548953)
            ·
              refine ⟨6071357121730754728911715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8095142828974339638548953 6071357121730754728911715)
              ·
                refine ⟨9107035682596132093367573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071357121730754728911715 9107035682596132093367573)
                ·
                  refine ⟨426892297621693691876605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9107035682596132093367573 426892297621693691876605)
                  ·
                    rfl

theorem cell20_935291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_935291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935291 prefixEnd_935291 := by exact prefixLift 935291
  have htrace : WordTrace (prefixWord ++ tailWord_935291) baseStart_935291 baseEnd_935291 := by
    simpa [prefixWord, tailWord_935291, baseEnd_935291] using wordTrace_append hprefix tailTrace_935291
  have hstable : (prefixWord ++ tailWord_935291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935291).length < 2 ^ (prefixWord ++ tailWord_935291).sum := by decide
  have hdescent : baseEnd_935291 < baseStart_935291 := by decide
  rcases family_descends (prefixWord ++ tailWord_935291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935367 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_935367 : Nat := 118140960795 + 935367 * 2 ^ 59
def prefixEnd_935367 : Nat := 4983230072969 + 3 ^ 40 * 935367 * 2
def baseEnd_935367 : Nat := 426926986092575205342961

theorem tailTrace_935367 : CollatzResearch.WordTrace tailWord_935367 prefixEnd_935367 426926986092575205342961 := by
  unfold tailWord_935367
  simp only [CollatzResearch.WordTrace]
  refine ⟨34115637202332581810524355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22743758134888387873682903 34115637202332581810524355)
  ·
    refine ⟨51173455803498872715786533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34115637202332581810524355 51173455803498872715786533)
    ·
      refine ⟨9595022963156038634209975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51173455803498872715786533 9595022963156038634209975)
      ·
        refine ⟨14392534444734057951314963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9595022963156038634209975 14392534444734057951314963)
        ·
          refine ⟨21588801667101086926972445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14392534444734057951314963 21588801667101086926972445)
          ·
            refine ⟨8095800625162907597614667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21588801667101086926972445 8095800625162907597614667)
            ·
              refine ⟨12143700937744361396422001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8095800625162907597614667 12143700937744361396422001)
              ·
                refine ⟨9107775703308271047316501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12143700937744361396422001 9107775703308271047316501)
                ·
                  refine ⟨426926986092575205342961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9107775703308271047316501 426926986092575205342961)
                  ·
                    rfl

theorem cell20_935367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_935367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935367 prefixEnd_935367 := by exact prefixLift 935367
  have htrace : WordTrace (prefixWord ++ tailWord_935367) baseStart_935367 baseEnd_935367 := by
    simpa [prefixWord, tailWord_935367, baseEnd_935367] using wordTrace_append hprefix tailTrace_935367
  have hstable : (prefixWord ++ tailWord_935367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935367).length < 2 ^ (prefixWord ++ tailWord_935367).sum := by decide
  have hdescent : baseEnd_935367 < baseStart_935367 := by decide
  rcases family_descends (prefixWord ++ tailWord_935367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935408 : List Nat := [2, 1, 1, 1, 3, 6, 2, 4]
def baseStart_935408 : Nat := 118140960795 + 935408 * 2 ^ 59
def prefixEnd_935408 : Nat := 4983230072969 + 3 ^ 40 * 935408 * 2
def baseEnd_935408 : Nat := 142315233203253761658709

theorem tailTrace_935408 : CollatzResearch.WordTrace tailWord_935408 prefixEnd_935408 142315233203253761658709 := by
  unfold tailWord_935408
  simp only [CollatzResearch.WordTrace]
  refine ⟨17058566297592022906383439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22744755063456030541844585 17058566297592022906383439)
  ·
    refine ⟨25587849446388034359575159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17058566297592022906383439 25587849446388034359575159)
    ·
      refine ⟨38381774169582051539362739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25587849446388034359575159 38381774169582051539362739)
      ·
        refine ⟨57572661254373077309044109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38381774169582051539362739 57572661254373077309044109)
        ·
          refine ⟨21589747970389903990891541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57572661254373077309044109 21589747970389903990891541)
          ·
            refine ⟨1012019436112026749573041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21589747970389903990891541 1012019436112026749573041)
            ·
              refine ⟨759014577084020062179781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012019436112026749573041 759014577084020062179781)
              ·
                refine ⟨142315233203253761658709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 759014577084020062179781 142315233203253761658709)
                ·
                  rfl

theorem cell20_935408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_935408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935408 prefixEnd_935408 := by exact prefixLift 935408
  have htrace : WordTrace (prefixWord ++ tailWord_935408) baseStart_935408 baseEnd_935408 := by
    simpa [prefixWord, tailWord_935408, baseEnd_935408] using wordTrace_append hprefix tailTrace_935408
  have hstable : (prefixWord ++ tailWord_935408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935408).length < 2 ^ (prefixWord ++ tailWord_935408).sum := by decide
  have hdescent : baseEnd_935408 < baseStart_935408 := by decide
  rcases family_descends (prefixWord ++ tailWord_935408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935453 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 3]
def baseStart_935453 : Nat := 118140960795 + 935453 * 2 ^ 59
def prefixEnd_935453 : Nat := 4983230072969 + 3 ^ 40 * 935453 * 2
def baseEnd_935453 : Nat := 426966238835941128475943

theorem tailTrace_935453 : CollatzResearch.WordTrace tailWord_935453 prefixEnd_935453 426966238835941128475943 := by
  unfold tailWord_935453
  simp only [CollatzResearch.WordTrace]
  refine ⟨34118773880021018498155013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22745849253347345665436675 34118773880021018498155013)
  ·
    refine ⟨6397270102503940968404065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34118773880021018498155013 6397270102503940968404065)
    ·
      refine ⟨4797952576877955726303049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6397270102503940968404065 4797952576877955726303049)
      ·
        refine ⟨3598464432658466794727287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4797952576877955726303049 3598464432658466794727287)
        ·
          refine ⟨5397696648987700192090931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598464432658466794727287 5397696648987700192090931)
          ·
            refine ⟨8096544973481550288136397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397696648987700192090931 8096544973481550288136397)
            ·
              refine ⟨3036204365055581358051149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8096544973481550288136397 3036204365055581358051149)
              ·
                refine ⟨1138576636895843009269181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3036204365055581358051149 1138576636895843009269181)
                ·
                  refine ⟨426966238835941128475943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138576636895843009269181 426966238835941128475943)
                  ·
                    rfl

theorem cell20_935453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_935453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935453 prefixEnd_935453 := by exact prefixLift 935453
  have htrace : WordTrace (prefixWord ++ tailWord_935453) baseStart_935453 baseEnd_935453 := by
    simpa [prefixWord, tailWord_935453, baseEnd_935453] using wordTrace_append hprefix tailTrace_935453
  have hstable : (prefixWord ++ tailWord_935453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935453).length < 2 ^ (prefixWord ++ tailWord_935453).sum := by decide
  have hdescent : baseEnd_935453 < baseStart_935453 := by decide
  rcases family_descends (prefixWord ++ tailWord_935453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935501 : List Nat := [1, 6, 1, 1, 3, 2, 1, 5]
def baseStart_935501 : Nat := 118140960795 + 935501 * 2 ^ 59
def prefixEnd_935501 : Nat := 4983230072969 + 3 ^ 40 * 935501 * 2
def baseEnd_935501 : Nat := 142329382447955431625249

theorem tailTrace_935501 : CollatzResearch.WordTrace tailWord_935501 prefixEnd_935501 142329382447955431625249 := by
  unfold tailWord_935501
  simp only [CollatzResearch.WordTrace]
  refine ⟨34120524583847122695902357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22747016389231415130601571 34120524583847122695902357)
  ·
    refine ⟨1599399589867833876370423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34120524583847122695902357 1599399589867833876370423)
    ·
      refine ⟨2399099384801750814555635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599399589867833876370423 2399099384801750814555635)
      ·
        refine ⟨3598649077202626221833453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399099384801750814555635 3598649077202626221833453)
        ·
          refine ⟨1349493403950984833187545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3598649077202626221833453 1349493403950984833187545)
          ·
            refine ⟨1012120052963238624890659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1349493403950984833187545 1012120052963238624890659)
            ·
              refine ⟨1518180079444857937335989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012120052963238624890659 1518180079444857937335989)
              ·
                refine ⟨142329382447955431625249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1518180079444857937335989 142329382447955431625249)
                ·
                  rfl

theorem cell20_935501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 5].length) (baseStart_935501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935501 prefixEnd_935501 := by exact prefixLift 935501
  have htrace : WordTrace (prefixWord ++ tailWord_935501) baseStart_935501 baseEnd_935501 := by
    simpa [prefixWord, tailWord_935501, baseEnd_935501] using wordTrace_append hprefix tailTrace_935501
  have hstable : (prefixWord ++ tailWord_935501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935501).length < 2 ^ (prefixWord ++ tailWord_935501).sum := by decide
  have hdescent : baseEnd_935501 < baseStart_935501 := by decide
  rcases family_descends (prefixWord ++ tailWord_935501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935553 : List Nat := [1, 2, 4, 2, 1, 2, 2, 4, 2]
def baseStart_935553 : Nat := 118140960795 + 935553 * 2 ^ 59
def prefixEnd_935553 : Nat := 4983230072969 + 3 ^ 40 * 935553 * 2
def baseEnd_935553 : Nat := 427011881560785225142201

theorem tailTrace_935553 : CollatzResearch.WordTrace tailWord_935553 prefixEnd_935553 427011881560785225142201 := by
  unfold tailWord_935553
  simp only [CollatzResearch.WordTrace]
  refine ⟨34122421179658735576795313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22748280786439157051196875 34122421179658735576795313)
  ·
    refine ⟨25591815884744051682596485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34122421179658735576795313 25591815884744051682596485)
    ·
      refine ⟨4798465478389509690486841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25591815884744051682596485 4798465478389509690486841)
      ·
        refine ⟨3598849108792132267865131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4798465478389509690486841 3598849108792132267865131)
        ·
          refine ⟨5398273663188198401797697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598849108792132267865131 5398273663188198401797697)
          ·
            refine ⟨4048705247391148801348273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5398273663188198401797697 4048705247391148801348273)
            ·
              refine ⟨3036528935543361601011205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048705247391148801348273 3036528935543361601011205)
              ·
                refine ⟨569349175414380300189601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3036528935543361601011205 569349175414380300189601)
                ·
                  refine ⟨427011881560785225142201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569349175414380300189601 427011881560785225142201)
                  ·
                    rfl

theorem cell20_935553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_935553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935553 prefixEnd_935553 := by exact prefixLift 935553
  have htrace : WordTrace (prefixWord ++ tailWord_935553) baseStart_935553 baseEnd_935553 := by
    simpa [prefixWord, tailWord_935553, baseEnd_935553] using wordTrace_append hprefix tailTrace_935553
  have hstable : (prefixWord ++ tailWord_935553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935553).length < 2 ^ (prefixWord ++ tailWord_935553).sum := by decide
  have hdescent : baseEnd_935553 < baseStart_935553 := by decide
  rcases family_descends (prefixWord ++ tailWord_935553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935564 : List Nat := [2, 2, 1, 2, 1, 1, 4, 7]
def baseStart_935564 : Nat := 118140960795 + 935564 * 2 ^ 59
def prefixEnd_935564 : Nat := 4983230072969 + 3 ^ 40 * 935564 * 2
def baseEnd_935564 : Nat := 142338967420172691925163

theorem tailTrace_935564 : CollatzResearch.WordTrace tailWord_935564 prefixEnd_935564 142338967420172691925163 := by
  unfold tailWord_935564
  simp only [CollatzResearch.WordTrace]
  refine ⟨17061411191309442227722873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22748548255079256303630497 17061411191309442227722873)
  ·
    refine ⟨12796058393482081670792155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17061411191309442227722873 12796058393482081670792155)
    ·
      refine ⟨19194087590223122506188233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12796058393482081670792155 19194087590223122506188233)
      ·
        refine ⟨14395565692667341879641175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19194087590223122506188233 14395565692667341879641175)
        ·
          refine ⟨21593348539001012819461763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14395565692667341879641175 21593348539001012819461763)
          ·
            refine ⟨32390022808501519229192645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21593348539001012819461763 32390022808501519229192645)
            ·
              refine ⟨6073129276594034855473621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32390022808501519229192645 6073129276594034855473621)
              ·
                refine ⟨142338967420172691925163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6073129276594034855473621 142338967420172691925163)
                ·
                  rfl

theorem cell20_935564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_935564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935564 prefixEnd_935564 := by exact prefixLift 935564
  have htrace : WordTrace (prefixWord ++ tailWord_935564) baseStart_935564 baseEnd_935564 := by
    simpa [prefixWord, tailWord_935564, baseEnd_935564] using wordTrace_append hprefix tailTrace_935564
  have hstable : (prefixWord ++ tailWord_935564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935564).length < 2 ^ (prefixWord ++ tailWord_935564).sum := by decide
  have hdescent : baseEnd_935564 < baseStart_935564 := by decide
  rcases family_descends (prefixWord ++ tailWord_935564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935571 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_935571 : Nat := 118140960795 + 935571 * 2 ^ 59
def prefixEnd_935571 : Nat := 4983230072969 + 3 ^ 40 * 935571 * 2
def baseEnd_935571 : Nat := 427020097251257162542127

theorem tailTrace_935571 : CollatzResearch.WordTrace tailWord_935571 prefixEnd_935571 427020097251257162542127 := by
  unfold tailWord_935571
  simp only [CollatzResearch.WordTrace]
  refine ⟨34123077693593524650950567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22748718462395683100633711 34123077693593524650950567)
  ·
    refine ⟨51184616540390286976425851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34123077693593524650950567 51184616540390286976425851)
    ·
      refine ⟨76776924810585430464638777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51184616540390286976425851 76776924810585430464638777)
      ·
        refine ⟨57582693607939072848479083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76776924810585430464638777 57582693607939072848479083)
        ·
          refine ⟨86374040411908609272718625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57582693607939072848479083 86374040411908609272718625)
          ·
            refine ⟨64780530308931456954538969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86374040411908609272718625 64780530308931456954538969)
            ·
              refine ⟨48585397731698592715904227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64780530308931456954538969 48585397731698592715904227)
              ·
                refine ⟨72878096597547889073856341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48585397731698592715904227 72878096597547889073856341)
                ·
                  refine ⟨427020097251257162542127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72878096597547889073856341 427020097251257162542127)
                  ·
                    rfl

theorem cell20_935571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_935571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935571 prefixEnd_935571 := by exact prefixLift 935571
  have htrace : WordTrace (prefixWord ++ tailWord_935571) baseStart_935571 baseEnd_935571 := by
    simpa [prefixWord, tailWord_935571, baseEnd_935571] using wordTrace_append hprefix tailTrace_935571
  have hstable : (prefixWord ++ tailWord_935571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935571).length < 2 ^ (prefixWord ++ tailWord_935571).sum := by decide
  have hdescent : baseEnd_935571 < baseStart_935571 := by decide
  rcases family_descends (prefixWord ++ tailWord_935571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935588 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_935588 : Nat := 118140960795 + 935588 * 2 ^ 59
def prefixEnd_935588 : Nat := 4983230072969 + 3 ^ 40 * 935588 * 2
def baseEnd_935588 : Nat := 427027856514480658975391

theorem tailTrace_935588 : CollatzResearch.WordTrace tailWord_935588 prefixEnd_935588 427027856514480658975391 := by
  unfold tailWord_935588
  simp only [CollatzResearch.WordTrace]
  refine ⟨17061848867265968277159709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22749131823021291036212945 17061848867265968277159709)
  ·
    refine ⟨6398193325224738103934891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17061848867265968277159709 6398193325224738103934891)
    ·
      refine ⟨9597289987837107155902337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6398193325224738103934891 9597289987837107155902337)
      ·
        refine ⟨7197967490877830366926753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9597289987837107155902337 7197967490877830366926753)
        ·
          refine ⟨5398475618158372775195065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7197967490877830366926753 5398475618158372775195065)
          ·
            refine ⟨4048856713618779581396299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5398475618158372775195065 4048856713618779581396299)
            ·
              refine ⟨6073285070428169372094449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048856713618779581396299 6073285070428169372094449)
              ·
                refine ⟨4554963802821127029070837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6073285070428169372094449 4554963802821127029070837)
                ·
                  refine ⟨427027856514480658975391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4554963802821127029070837 427027856514480658975391)
                  ·
                    rfl

theorem cell20_935588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_935588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935588 prefixEnd_935588 := by exact prefixLift 935588
  have htrace : WordTrace (prefixWord ++ tailWord_935588) baseStart_935588 baseEnd_935588 := by
    simpa [prefixWord, tailWord_935588, baseEnd_935588] using wordTrace_append hprefix tailTrace_935588
  have hstable : (prefixWord ++ tailWord_935588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935588).length < 2 ^ (prefixWord ++ tailWord_935588).sum := by decide
  have hdescent : baseEnd_935588 < baseStart_935588 := by decide
  rcases family_descends (prefixWord ++ tailWord_935588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935602 : List Nat := [3, 2, 1, 1, 1, 2, 10]
def baseStart_935602 : Nat := 118140960795 + 935602 * 2 ^ 59
def prefixEnd_935602 : Nat := 4983230072969 + 3 ^ 40 * 935602 * 2
def baseEnd_935602 : Nat := 47448249610662092500963

theorem tailTrace_935602 : CollatzResearch.WordTrace tailWord_935602 prefixEnd_935602 47448249610662092500963 := by
  unfold tailWord_935602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8531052089120304236332265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22749472237654144630219373 8531052089120304236332265)
  ·
    refine ⟨6398289066840228177249199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8531052089120304236332265 6398289066840228177249199)
    ·
      refine ⟨9597433600260342265873799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6398289066840228177249199 9597433600260342265873799)
      ·
        refine ⟨14396150400390513398810699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9597433600260342265873799 14396150400390513398810699)
        ·
          refine ⟨21594225600585770098216049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14396150400390513398810699 21594225600585770098216049)
          ·
            refine ⟨16195669200439327573662037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21594225600585770098216049 16195669200439327573662037)
            ·
              refine ⟨47448249610662092500963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16195669200439327573662037 47448249610662092500963)
              ·
                rfl

theorem cell20_935602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 10].length) (baseStart_935602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935602 prefixEnd_935602 := by exact prefixLift 935602
  have htrace : WordTrace (prefixWord ++ tailWord_935602) baseStart_935602 baseEnd_935602 := by
    simpa [prefixWord, tailWord_935602, baseEnd_935602] using wordTrace_append hprefix tailTrace_935602
  have hstable : (prefixWord ++ tailWord_935602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935602).length < 2 ^ (prefixWord ++ tailWord_935602).sum := by decide
  have hdescent : baseEnd_935602 < baseStart_935602 := by decide
  rcases family_descends (prefixWord ++ tailWord_935602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935612 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_935612 : Nat := 118140960795 + 935612 * 2 ^ 59
def prefixEnd_935612 : Nat := 4983230072969 + 3 ^ 40 * 935612 * 2
def baseEnd_935612 : Nat := 427038810768443242175293

theorem tailTrace_935612 : CollatzResearch.WordTrace tailWord_935612 prefixEnd_935612 427038810768443242175293 := by
  unfold tailWord_935612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062286543222494326596545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22749715390963325768795393 17062286543222494326596545)
  ·
    refine ⟨12796714907416870744947409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17062286543222494326596545 12796714907416870744947409)
    ·
      refine ⟨9597536180562653058710557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12796714907416870744947409 9597536180562653058710557)
      ·
        refine ⟨3599076067710994897016459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9597536180562653058710557 3599076067710994897016459)
        ·
          refine ⟨5398614101566492345524689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599076067710994897016459 5398614101566492345524689)
          ·
            refine ⟨4048960576174869259143517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5398614101566492345524689 4048960576174869259143517)
            ·
              refine ⟨1518360216065575972178819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4048960576174869259143517 1518360216065575972178819)
              ·
                refine ⟨2277540324098363958268229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518360216065575972178819 2277540324098363958268229)
                ·
                  refine ⟨427038810768443242175293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2277540324098363958268229 427038810768443242175293)
                  ·
                    rfl

theorem cell20_935612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_935612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935612 prefixEnd_935612 := by exact prefixLift 935612
  have htrace : WordTrace (prefixWord ++ tailWord_935612) baseStart_935612 baseEnd_935612 := by
    simpa [prefixWord, tailWord_935612, baseEnd_935612] using wordTrace_append hprefix tailTrace_935612
  have hstable : (prefixWord ++ tailWord_935612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935612).length < 2 ^ (prefixWord ++ tailWord_935612).sum := by decide
  have hdescent : baseEnd_935612 < baseStart_935612 := by decide
  rcases family_descends (prefixWord ++ tailWord_935612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935618 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_935618 : Nat := 118140960795 + 935618 * 2 ^ 59
def prefixEnd_935618 : Nat := 4983230072969 + 3 ^ 40 * 935618 * 2
def baseEnd_935618 : Nat := 427041549331933887975269

theorem tailTrace_935618 : CollatzResearch.WordTrace tailWord_935618 prefixEnd_935618 427041549331933887975269 := by
  unfold tailWord_935618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8531197981105812919477877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22749861282948834451941005 8531197981105812919477877)
  ·
    refine ⟨799799810728669961201051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8531197981105812919477877 799799810728669961201051)
    ·
      refine ⟨1199699716093004941801577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799799810728669961201051 1199699716093004941801577)
      ·
        refine ⟨899774787069753706351183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1199699716093004941801577 899774787069753706351183)
        ·
          refine ⟨1349662180604630559526775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899774787069753706351183 1349662180604630559526775)
          ·
            refine ⟨2024493270906945839290163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349662180604630559526775 2024493270906945839290163)
            ·
              refine ⟨3036739906360418758935245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024493270906945839290163 3036739906360418758935245)
              ·
                refine ⟨1138777464885157034600717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3036739906360418758935245 1138777464885157034600717)
                ·
                  refine ⟨427041549331933887975269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138777464885157034600717 427041549331933887975269)
                  ·
                    rfl

theorem cell20_935618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_935618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935618 prefixEnd_935618 := by exact prefixLift 935618
  have htrace : WordTrace (prefixWord ++ tailWord_935618) baseStart_935618 baseEnd_935618 := by
    simpa [prefixWord, tailWord_935618, baseEnd_935618] using wordTrace_append hprefix tailTrace_935618
  have hstable : (prefixWord ++ tailWord_935618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935618).length < 2 ^ (prefixWord ++ tailWord_935618).sum := by decide
  have hdescent : baseEnd_935618 < baseStart_935618 := by decide
  rcases family_descends (prefixWord ++ tailWord_935618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935640 : List Nat := [2, 1, 2, 2, 3, 1, 1, 8]
def baseStart_935640 : Nat := 118140960795 + 935640 * 2 ^ 59
def prefixEnd_935640 : Nat := 4983230072969 + 3 ^ 40 * 935640 * 2
def baseEnd_935640 : Nat := 142350530243799863080615

theorem tailTrace_935640 : CollatzResearch.WordTrace tailWord_935640 prefixEnd_935640 142350530243799863080615 := by
  unfold tailWord_935640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062797165171774717606187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22750396220229032956808249 17062797165171774717606187)
  ·
    refine ⟨25594195747757662076409281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17062797165171774717606187 25594195747757662076409281)
    ·
      refine ⟨19195646810818246557306961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25594195747757662076409281 19195646810818246557306961)
      ·
        refine ⟨14396735108113684917980221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19195646810818246557306961 14396735108113684917980221)
        ·
          refine ⟨5398775665542631844242583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14396735108113684917980221 5398775665542631844242583)
          ·
            refine ⟨8098163498313947766363875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398775665542631844242583 8098163498313947766363875)
            ·
              refine ⟨12147245247470921649545813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8098163498313947766363875 12147245247470921649545813)
              ·
                refine ⟨142350530243799863080615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12147245247470921649545813 142350530243799863080615)
                ·
                  rfl

theorem cell20_935640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_935640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935640 prefixEnd_935640 := by exact prefixLift 935640
  have htrace : WordTrace (prefixWord ++ tailWord_935640) baseStart_935640 baseEnd_935640 := by
    simpa [prefixWord, tailWord_935640, baseEnd_935640] using wordTrace_append hprefix tailTrace_935640
  have hstable : (prefixWord ++ tailWord_935640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935640).length < 2 ^ (prefixWord ++ tailWord_935640).sum := by decide
  have hdescent : baseEnd_935640 < baseStart_935640 := by decide
  rcases family_descends (prefixWord ++ tailWord_935640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935667 : List Nat := [1, 1, 1, 2, 2, 3, 6, 2, 2]
def baseStart_935667 : Nat := 118140960795 + 935667 * 2 ^ 59
def prefixEnd_935667 : Nat := 4983230072969 + 3 ^ 40 * 935667 * 2
def baseEnd_935667 : Nat := 427063914267107495341735

theorem tailTrace_935667 : CollatzResearch.WordTrace tailWord_935667 prefixEnd_935667 427063914267107495341735 := by
  unfold tailWord_935667
  simp only [CollatzResearch.WordTrace]
  refine ⟨34126579101245733046445255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22751052734163822030963503 34126579101245733046445255)
  ·
    refine ⟨51189868651868599569667883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34126579101245733046445255 51189868651868599569667883)
    ·
      refine ⟨76784802977802899354501825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51189868651868599569667883 76784802977802899354501825)
      ·
        refine ⟨57588602233352174515876369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76784802977802899354501825 57588602233352174515876369)
        ·
          refine ⟨43191451675014130886907277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57588602233352174515876369 43191451675014130886907277)
          ·
            refine ⟨16196794378130299082590229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43191451675014130886907277 16196794378130299082590229)
            ·
              refine ⟨759224736474857769496417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16196794378130299082590229 759224736474857769496417)
              ·
                refine ⟨569418552356143327122313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759224736474857769496417 569418552356143327122313)
                ·
                  refine ⟨427063914267107495341735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569418552356143327122313 427063914267107495341735)
                  ·
                    rfl

theorem cell20_935667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 2].length) (baseStart_935667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935667 prefixEnd_935667 := by exact prefixLift 935667
  have htrace : WordTrace (prefixWord ++ tailWord_935667) baseStart_935667 baseEnd_935667 := by
    simpa [prefixWord, tailWord_935667, baseEnd_935667] using wordTrace_append hprefix tailTrace_935667
  have hstable : (prefixWord ++ tailWord_935667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935667).length < 2 ^ (prefixWord ++ tailWord_935667).sum := by decide
  have hdescent : baseEnd_935667 < baseStart_935667 := by decide
  rcases family_descends (prefixWord ++ tailWord_935667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935685 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_935685 : Nat := 118140960795 + 935685 * 2 ^ 59
def prefixEnd_935685 : Nat := 4983230072969 + 3 ^ 40 * 935685 * 2
def baseEnd_935685 : Nat := 427072129957579432741661

theorem tailTrace_935685 : CollatzResearch.WordTrace tailWord_935685 prefixEnd_935685 427072129957579432741661 := by
  unfold tailWord_935685
  simp only [CollatzResearch.WordTrace]
  refine ⟨34127235615180522120600509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22751490410120348080400339 34127235615180522120600509)
  ·
    refine ⟨12797713355692695795225191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34127235615180522120600509 12797713355692695795225191)
    ·
      refine ⟨19196570033539043692837787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12797713355692695795225191 19196570033539043692837787)
      ·
        refine ⟨28794855050308565539256681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19196570033539043692837787 28794855050308565539256681)
        ·
          refine ⟨21596141287731424154442511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28794855050308565539256681 21596141287731424154442511)
          ·
            refine ⟨32394211931597136231663767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21596141287731424154442511 32394211931597136231663767)
            ·
              refine ⟨48591317897395704347495651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32394211931597136231663767 48591317897395704347495651)
              ·
                refine ⟨72886976846093556521243477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48591317897395704347495651 72886976846093556521243477)
                ·
                  refine ⟨427072129957579432741661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72886976846093556521243477 427072129957579432741661)
                  ·
                    rfl

theorem cell20_935685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_935685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935685 prefixEnd_935685 := by exact prefixLift 935685
  have htrace : WordTrace (prefixWord ++ tailWord_935685) baseStart_935685 baseEnd_935685 := by
    simpa [prefixWord, tailWord_935685, baseEnd_935685] using wordTrace_append hprefix tailTrace_935685
  have hstable : (prefixWord ++ tailWord_935685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935685).length < 2 ^ (prefixWord ++ tailWord_935685).sum := by decide
  have hdescent : baseEnd_935685 < baseStart_935685 := by decide
  rcases family_descends (prefixWord ++ tailWord_935685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935740 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_935740 : Nat := 118140960795 + 935740 * 2 ^ 59
def prefixEnd_935740 : Nat := 4983230072969 + 3 ^ 40 * 935740 * 2
def baseEnd_935740 : Nat := 427097233456243685908103

theorem tailTrace_935740 : CollatzResearch.WordTrace tailWord_935740 prefixEnd_935740 427097233456243685908103 := by
  unfold tailWord_935740
  simp only [CollatzResearch.WordTrace]
  refine ⟨17064620814990633256926337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22752827753320844342568449 17064620814990633256926337)
  ·
    refine ⟨12798465611242974942694753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17064620814990633256926337 12798465611242974942694753)
    ·
      refine ⟨9598849208432231207021065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12798465611242974942694753 9598849208432231207021065)
      ·
        refine ⟨7199136906324173405265799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9598849208432231207021065 7199136906324173405265799)
        ·
          refine ⟨10798705359486260107898699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199136906324173405265799 10798705359486260107898699)
          ·
            refine ⟨16198058039229390161848049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10798705359486260107898699 16198058039229390161848049)
            ·
              refine ⟨12148543529422042621386037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16198058039229390161848049 12148543529422042621386037)
              ·
                refine ⟨1138925955883316495754941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12148543529422042621386037 1138925955883316495754941)
                ·
                  refine ⟨427097233456243685908103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138925955883316495754941 427097233456243685908103)
                  ·
                    rfl

theorem cell20_935740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_935740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935740 prefixEnd_935740 := by exact prefixLift 935740
  have htrace : WordTrace (prefixWord ++ tailWord_935740) baseStart_935740 baseEnd_935740 := by
    simpa [prefixWord, tailWord_935740, baseEnd_935740] using wordTrace_append hprefix tailTrace_935740
  have hstable : (prefixWord ++ tailWord_935740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935740).length < 2 ^ (prefixWord ++ tailWord_935740).sum := by decide
  have hdescent : baseEnd_935740 < baseStart_935740 := by decide
  rcases family_descends (prefixWord ++ tailWord_935740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935747 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_935747 : Nat := 118140960795 + 935747 * 2 ^ 59
def prefixEnd_935747 : Nat := 4983230072969 + 3 ^ 40 * 935747 * 2
def baseEnd_935747 : Nat := 427100428446982772674741

theorem tailTrace_935747 : CollatzResearch.WordTrace tailWord_935747 prefixEnd_935747 427100428446982772674741 := by
  unfold tailWord_935747
  simp only [CollatzResearch.WordTrace]
  refine ⟨34129496940955906709357495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22752997960637271139571663 34129496940955906709357495)
  ·
    refine ⟨51194245411433860064036243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34129496940955906709357495 51194245411433860064036243)
    ·
      refine ⟨76791368117150790096054365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51194245411433860064036243 76791368117150790096054365)
      ·
        refine ⟨28796763043931546286020387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76791368117150790096054365 28796763043931546286020387)
        ·
          refine ⟨43195144565897319429030581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28796763043931546286020387 43195144565897319429030581)
          ·
            refine ⟨4049544803052873696471617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43195144565897319429030581 4049544803052873696471617)
            ·
              refine ⟨3037158602289655272353713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049544803052873696471617 3037158602289655272353713)
              ·
                refine ⟨2277868951717241454265285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037158602289655272353713 2277868951717241454265285)
                ·
                  refine ⟨427100428446982772674741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2277868951717241454265285 427100428446982772674741)
                  ·
                    rfl

theorem cell20_935747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_935747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935747 prefixEnd_935747 := by exact prefixLift 935747
  have htrace : WordTrace (prefixWord ++ tailWord_935747) baseStart_935747 baseEnd_935747 := by
    simpa [prefixWord, tailWord_935747, baseEnd_935747] using wordTrace_append hprefix tailTrace_935747
  have hstable : (prefixWord ++ tailWord_935747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935747).length < 2 ^ (prefixWord ++ tailWord_935747).sum := by decide
  have hdescent : baseEnd_935747 < baseStart_935747 := by decide
  rcases family_descends (prefixWord ++ tailWord_935747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935754 : List Nat := [3, 1, 2, 1, 1, 1, 5, 6]
def baseStart_935754 : Nat := 118140960795 + 935754 * 2 ^ 59
def prefixEnd_935754 : Nat := 4983230072969 + 3 ^ 40 * 935754 * 2
def baseEnd_935754 : Nat := 142367874479240619813793

theorem tailTrace_935754 : CollatzResearch.WordTrace tailWord_935754 prefixEnd_935754 142367874479240619813793 := by
  unfold tailWord_935754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8532438062982636726215579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22753168167953697936574877 8532438062982636726215579)
  ·
    refine ⟨12798657094473955089323369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8532438062982636726215579 12798657094473955089323369)
    ·
      refine ⟨9598992820855466316992527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12798657094473955089323369 9598992820855466316992527)
      ·
        refine ⟨14398489231283199475488791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9598992820855466316992527 14398489231283199475488791)
        ·
          refine ⟨21597733846924799213233187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14398489231283199475488791 21597733846924799213233187)
          ·
            refine ⟨32396600770387198819849781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21597733846924799213233187 32396600770387198819849781)
            ·
              refine ⟨3037181322223799889360917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32396600770387198819849781 3037181322223799889360917)
              ·
                refine ⟨142367874479240619813793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3037181322223799889360917 142367874479240619813793)
                ·
                  rfl

theorem cell20_935754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_935754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935754 prefixEnd_935754 := by exact prefixLift 935754
  have htrace : WordTrace (prefixWord ++ tailWord_935754) baseStart_935754 baseEnd_935754 := by
    simpa [prefixWord, tailWord_935754, baseEnd_935754] using wordTrace_append hprefix tailTrace_935754
  have hstable : (prefixWord ++ tailWord_935754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935754).length < 2 ^ (prefixWord ++ tailWord_935754).sum := by decide
  have hdescent : baseEnd_935754 < baseStart_935754 := by decide
  rcases family_descends (prefixWord ++ tailWord_935754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935757 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_935757 : Nat := 118140960795 + 935757 * 2 ^ 59
def prefixEnd_935757 : Nat := 4983230072969 + 3 ^ 40 * 935757 * 2
def baseEnd_935757 : Nat := 427104992719467182341367

theorem tailTrace_935757 : CollatzResearch.WordTrace tailWord_935757 prefixEnd_935757 427104992719467182341367 := by
  unfold tailWord_935757
  simp only [CollatzResearch.WordTrace]
  refine ⟨34129861670919678417221525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22753241113946452278147683 34129861670919678417221525)
  ·
    refine ⟨1599837265824359925807259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34129861670919678417221525 1599837265824359925807259)
    ·
      refine ⟨2399755898736539888710889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599837265824359925807259 2399755898736539888710889)
      ·
        refine ⟨1799816924052404916533167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2399755898736539888710889 1799816924052404916533167)
        ·
          refine ⟨2699725386078607374799751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1799816924052404916533167 2699725386078607374799751)
          ·
            refine ⟨4049588079117911062199627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699725386078607374799751 4049588079117911062199627)
            ·
              refine ⟨6074382118676866593299441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049588079117911062199627 6074382118676866593299441)
              ·
                refine ⟨4555786589007649944974581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6074382118676866593299441 4555786589007649944974581)
                ·
                  refine ⟨427104992719467182341367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555786589007649944974581 427104992719467182341367)
                  ·
                    rfl

theorem cell20_935757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_935757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935757 prefixEnd_935757 := by exact prefixLift 935757
  have htrace : WordTrace (prefixWord ++ tailWord_935757) baseStart_935757 baseEnd_935757 := by
    simpa [prefixWord, tailWord_935757, baseEnd_935757] using wordTrace_append hprefix tailTrace_935757
  have hstable : (prefixWord ++ tailWord_935757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935757).length < 2 ^ (prefixWord ++ tailWord_935757).sum := by decide
  have hdescent : baseEnd_935757 < baseStart_935757 := by decide
  rcases family_descends (prefixWord ++ tailWord_935757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935832 : List Nat := [2, 1, 2, 6, 2, 1, 2, 2, 2]
def baseStart_935832 : Nat := 118140960795 + 935832 * 2 ^ 59
def prefixEnd_935832 : Nat := 4983230072969 + 3 ^ 40 * 935832 * 2
def baseEnd_935832 : Nat := 427139224763100254841061

theorem tailTrace_935832 : CollatzResearch.WordTrace tailWord_935832 prefixEnd_935832 427139224763100254841061 := by
  unfold tailWord_935832
  simp only [CollatzResearch.WordTrace]
  refine ⟨17066298572823983113100875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22755064763765310817467833 17066298572823983113100875)
  ·
    refine ⟨25599447859235974669651313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17066298572823983113100875 25599447859235974669651313)
    ·
      refine ⟨19199585894426981002238485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25599447859235974669651313 19199585894426981002238485)
      ·
        refine ⟨899980588801264734479929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19199585894426981002238485 899980588801264734479929)
        ·
          refine ⟨674985441600948550859947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899980588801264734479929 674985441600948550859947)
          ·
            refine ⟨1012478162401422826289921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674985441600948550859947 1012478162401422826289921)
            ·
              refine ⟨759358621801067119717441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012478162401422826289921 759358621801067119717441)
              ·
                refine ⟨569518966350800339788081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759358621801067119717441 569518966350800339788081)
                ·
                  refine ⟨427139224763100254841061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569518966350800339788081 427139224763100254841061)
                  ·
                    rfl

theorem cell20_935832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_935832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935832 prefixEnd_935832 := by exact prefixLift 935832
  have htrace : WordTrace (prefixWord ++ tailWord_935832) baseStart_935832 baseEnd_935832 := by
    simpa [prefixWord, tailWord_935832, baseEnd_935832] using wordTrace_append hprefix tailTrace_935832
  have hstable : (prefixWord ++ tailWord_935832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935832).length < 2 ^ (prefixWord ++ tailWord_935832).sum := by decide
  have hdescent : baseEnd_935832 < baseStart_935832 := by decide
  rcases family_descends (prefixWord ++ tailWord_935832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935836 : List Nat := [2, 2, 3, 3, 1, 1, 4, 2, 2]
def baseStart_935836 : Nat := 118140960795 + 935836 * 2 ^ 59
def prefixEnd_935836 : Nat := 4983230072969 + 3 ^ 40 * 935836 * 2
def baseEnd_935836 : Nat := 427141050472094018707711

theorem tailTrace_935836 : CollatzResearch.WordTrace tailWord_935836 prefixEnd_935836 427141050472094018707711 := by
  unfold tailWord_935836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17066371518816737454673681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22755162025088983272898241 17066371518816737454673681)
  ·
    refine ⟨12799778639112553091005261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17066371518816737454673681 12799778639112553091005261)
    ·
      refine ⟨4799916989667207409126973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12799778639112553091005261 4799916989667207409126973)
      ·
        refine ⟨1799968871125202778422615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4799916989667207409126973 1799968871125202778422615)
        ·
          refine ⟨2699953306687804167633923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1799968871125202778422615 2699953306687804167633923)
          ·
            refine ⟨4049929960031706251450885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699953306687804167633923 4049929960031706251450885)
            ·
              refine ⟨759361867505944922147041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4049929960031706251450885 759361867505944922147041)
              ·
                refine ⟨569521400629458691610281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759361867505944922147041 569521400629458691610281)
                ·
                  refine ⟨427141050472094018707711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569521400629458691610281 427141050472094018707711)
                  ·
                    rfl

theorem cell20_935836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_935836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935836 prefixEnd_935836 := by exact prefixLift 935836
  have htrace : WordTrace (prefixWord ++ tailWord_935836) baseStart_935836 baseEnd_935836 := by
    simpa [prefixWord, tailWord_935836, baseEnd_935836] using wordTrace_append hprefix tailTrace_935836
  have hstable : (prefixWord ++ tailWord_935836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935836).length < 2 ^ (prefixWord ++ tailWord_935836).sum := by decide
  have hdescent : baseEnd_935836 < baseStart_935836 := by decide
  rcases family_descends (prefixWord ++ tailWord_935836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935847 : List Nat := [1, 1, 6, 1, 2, 1, 3, 5]
def baseStart_935847 : Nat := 118140960795 + 935847 * 2 ^ 59
def prefixEnd_935847 : Nat := 4983230072969 + 3 ^ 40 * 935847 * 2
def baseEnd_935847 : Nat := 142382023723942289780333

theorem tailTrace_935847 : CollatzResearch.WordTrace tailWord_935847 prefixEnd_935847 142382023723942289780333 := by
  unfold tailWord_935847
  simp only [CollatzResearch.WordTrace]
  refine ⟨34133144240593623787997795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22755429493729082525331863 34133144240593623787997795)
  ·
    refine ⟨51199716360890435681996693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34133144240593623787997795 51199716360890435681996693)
    ·
      refine ⟨2399986704416739172593595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51199716360890435681996693 2399986704416739172593595)
      ·
        refine ⟨3599980056625108758890393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399986704416739172593595 3599980056625108758890393)
        ·
          refine ⟨2699985042468831569167795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3599980056625108758890393 2699985042468831569167795)
          ·
            refine ⟨4049977563703247353751693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699985042468831569167795 4049977563703247353751693)
            ·
              refine ⟨1518741586388717757656885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4049977563703247353751693 1518741586388717757656885)
              ·
                refine ⟨142382023723942289780333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1518741586388717757656885 142382023723942289780333)
                ·
                  rfl

theorem cell20_935847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_935847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935847 prefixEnd_935847 := by exact prefixLift 935847
  have htrace : WordTrace (prefixWord ++ tailWord_935847) baseStart_935847 baseEnd_935847 := by
    simpa [prefixWord, tailWord_935847, baseEnd_935847] using wordTrace_append hprefix tailTrace_935847
  have hstable : (prefixWord ++ tailWord_935847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935847).length < 2 ^ (prefixWord ++ tailWord_935847).sum := by decide
  have hdescent : baseEnd_935847 < baseStart_935847 := by decide
  rcases family_descends (prefixWord ++ tailWord_935847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935861 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_935861 : Nat := 118140960795 + 935861 * 2 ^ 59
def prefixEnd_935861 : Nat := 4983230072969 + 3 ^ 40 * 935861 * 2
def baseEnd_935861 : Nat := 427152461153305042874275

theorem tailTrace_935861 : CollatzResearch.WordTrace tailWord_935861 prefixEnd_935861 427152461153305042874275 := by
  unfold tailWord_935861
  simp only [CollatzResearch.WordTrace]
  refine ⟨34133654862542904179007437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22755769908361936119338291 34133654862542904179007437)
  ·
    refine ⟨12800120573453589067127789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34133654862542904179007437 12800120573453589067127789)
    ·
      refine ⟨4800045215045095900172921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12800120573453589067127789 4800045215045095900172921)
      ·
        refine ⟨3600033911283821925129691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4800045215045095900172921 3600033911283821925129691)
        ·
          refine ⟨5400050866925732887694537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600033911283821925129691 5400050866925732887694537)
          ·
            refine ⟨4050038150194299665770903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5400050866925732887694537 4050038150194299665770903)
            ·
              refine ⟨6075057225291449498656355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050038150194299665770903 6075057225291449498656355)
              ·
                refine ⟨9112585837937174247984533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6075057225291449498656355 9112585837937174247984533)
                ·
                  refine ⟨427152461153305042874275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9112585837937174247984533 427152461153305042874275)
                  ·
                    rfl

theorem cell20_935861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_935861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935861 prefixEnd_935861 := by exact prefixLift 935861
  have htrace : WordTrace (prefixWord ++ tailWord_935861) baseStart_935861 baseEnd_935861 := by
    simpa [prefixWord, tailWord_935861, baseEnd_935861] using wordTrace_append hprefix tailTrace_935861
  have hstable : (prefixWord ++ tailWord_935861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935861).length < 2 ^ (prefixWord ++ tailWord_935861).sum := by decide
  have hdescent : baseEnd_935861 < baseStart_935861 := by decide
  rcases family_descends (prefixWord ++ tailWord_935861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935892 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_935892 : Nat := 118140960795 + 935892 * 2 ^ 59
def prefixEnd_935892 : Nat := 4983230072969 + 3 ^ 40 * 935892 * 2
def baseEnd_935892 : Nat := 427166610398006712840815

theorem tailTrace_935892 : CollatzResearch.WordTrace tailWord_935892 prefixEnd_935892 427166610398006712840815 := by
  unfold tailWord_935892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17067392762715298236692965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22756523683620397648923953 17067392762715298236692965)
  ·
    refine ⟨3200136143009118419379931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17067392762715298236692965 3200136143009118419379931)
    ·
      refine ⟨4800204214513677629069897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200136143009118419379931 4800204214513677629069897)
      ·
        refine ⟨3600153160885258221802423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4800204214513677629069897 3600153160885258221802423)
        ·
          refine ⟨5400229741327887332703635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600153160885258221802423 5400229741327887332703635)
          ·
            refine ⟨8100344611991830999055453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400229741327887332703635 8100344611991830999055453)
            ·
              refine ⟨3037629229496936624645795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8100344611991830999055453 3037629229496936624645795)
              ·
                refine ⟨4556443844245404936968693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037629229496936624645795 4556443844245404936968693)
                ·
                  refine ⟨427166610398006712840815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4556443844245404936968693 427166610398006712840815)
                  ·
                    rfl

theorem cell20_935892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_935892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935892 prefixEnd_935892 := by exact prefixLift 935892
  have htrace : WordTrace (prefixWord ++ tailWord_935892) baseStart_935892 baseEnd_935892 := by
    simpa [prefixWord, tailWord_935892, baseEnd_935892] using wordTrace_append hprefix tailTrace_935892
  have hstable : (prefixWord ++ tailWord_935892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935892).length < 2 ^ (prefixWord ++ tailWord_935892).sum := by decide
  have hdescent : baseEnd_935892 < baseStart_935892 := by decide
  rcases family_descends (prefixWord ++ tailWord_935892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935940 : List Nat := [2, 3, 2, 4, 1, 2, 6]
def baseStart_935940 : Nat := 118140960795 + 935940 * 2 ^ 59
def prefixEnd_935940 : Nat := 4983230072969 + 3 ^ 40 * 935940 * 2
def baseEnd_935940 : Nat := 47465390989547986582291

theorem tailTrace_935940 : CollatzResearch.WordTrace tailWord_935940 prefixEnd_935940 47465390989547986582291 := by
  unfold tailWord_935940
  simp only [CollatzResearch.WordTrace]
  refine ⟨17068268114628350335566637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22757690819504467114088849 17068268114628350335566637)
  ·
    refine ⟨6400600542985631375837489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17068268114628350335566637 6400600542985631375837489)
    ·
      refine ⟨4800450407239223531878117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6400600542985631375837489 4800450407239223531878117)
      ·
        refine ⟨900084451357354412227147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4800450407239223531878117 900084451357354412227147)
        ·
          refine ⟨1350126677036031618340721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900084451357354412227147 1350126677036031618340721)
          ·
            refine ⟨1012595007777023713755541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350126677036031618340721 1012595007777023713755541)
            ·
              refine ⟨47465390989547986582291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1012595007777023713755541 47465390989547986582291)
              ·
                rfl

theorem cell20_935940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 6].length) (baseStart_935940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935940 prefixEnd_935940 := by exact prefixLift 935940
  have htrace : WordTrace (prefixWord ++ tailWord_935940) baseStart_935940 baseEnd_935940 := by
    simpa [prefixWord, tailWord_935940, baseEnd_935940] using wordTrace_append hprefix tailTrace_935940
  have hstable : (prefixWord ++ tailWord_935940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935940).length < 2 ^ (prefixWord ++ tailWord_935940).sum := by decide
  have hdescent : baseEnd_935940 < baseStart_935940 := by decide
  rcases family_descends (prefixWord ++ tailWord_935940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935964 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 3]
def baseStart_935964 : Nat := 118140960795 + 935964 * 2 ^ 59
def prefixEnd_935964 : Nat := 4983230072969 + 3 ^ 40 * 935964 * 2
def baseEnd_935964 : Nat := 427199473159894462440521

theorem tailTrace_935964 : CollatzResearch.WordTrace tailWord_935964 prefixEnd_935964 427199473159894462440521 := by
  unfold tailWord_935964
  simp only [CollatzResearch.WordTrace]
  refine ⟨17068705790584876385003473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22758274387446501846671297 17068705790584876385003473)
  ·
    refine ⟨12801529342938657288752605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17068705790584876385003473 12801529342938657288752605)
    ·
      refine ⟨4800573503601996483282227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12801529342938657288752605 4800573503601996483282227)
      ·
        refine ⟨7200860255402994724923341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800573503601996483282227 7200860255402994724923341)
        ·
          refine ⟨2700322595776123021846253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7200860255402994724923341 2700322595776123021846253)
          ·
            refine ⟨1012620973416046133192345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2700322595776123021846253 1012620973416046133192345)
            ·
              refine ⟨759465730062034599894259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012620973416046133192345 759465730062034599894259)
              ·
                refine ⟨1139198595093051899841389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759465730062034599894259 1139198595093051899841389)
                ·
                  refine ⟨427199473159894462440521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139198595093051899841389 427199473159894462440521)
                  ·
                    rfl

theorem cell20_935964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_935964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935964 prefixEnd_935964 := by exact prefixLift 935964
  have htrace : WordTrace (prefixWord ++ tailWord_935964) baseStart_935964 baseEnd_935964 := by
    simpa [prefixWord, tailWord_935964, baseEnd_935964] using wordTrace_append hprefix tailTrace_935964
  have hstable : (prefixWord ++ tailWord_935964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935964).length < 2 ^ (prefixWord ++ tailWord_935964).sum := by decide
  have hdescent : baseEnd_935964 < baseStart_935964 := by decide
  rcases family_descends (prefixWord ++ tailWord_935964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935989 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_935989 : Nat := 118140960795 + 935989 * 2 ^ 59
def prefixEnd_935989 : Nat := 4983230072969 + 3 ^ 40 * 935989 * 2
def baseEnd_935989 : Nat := 427210883841105486607085

theorem tailTrace_935989 : CollatzResearch.WordTrace tailWord_935989 prefixEnd_935989 427210883841105486607085 := by
  unfold tailWord_935989
  simp only [CollatzResearch.WordTrace]
  refine ⟨34138323406079182039667021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22758882270719454693111347 34138323406079182039667021)
  ·
    refine ⟨12801871277279693264875133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34138323406079182039667021 12801871277279693264875133)
    ·
      refine ⟨4800701728979884974328175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12801871277279693264875133 4800701728979884974328175)
      ·
        refine ⟨7201052593469827461492263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800701728979884974328175 7201052593469827461492263)
        ·
          refine ⟨10801578890204741192238395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201052593469827461492263 10801578890204741192238395)
          ·
            refine ⟨16202368335307111788357593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10801578890204741192238395 16202368335307111788357593)
            ·
              refine ⟨12151776251480333841268195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16202368335307111788357593 12151776251480333841268195)
              ·
                refine ⟨18227664377220500761902293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12151776251480333841268195 18227664377220500761902293)
                ·
                  refine ⟨427210883841105486607085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18227664377220500761902293 427210883841105486607085)
                  ·
                    rfl

theorem cell20_935989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_935989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_935989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_935989 prefixEnd_935989 := by exact prefixLift 935989
  have htrace : WordTrace (prefixWord ++ tailWord_935989) baseStart_935989 baseEnd_935989 := by
    simpa [prefixWord, tailWord_935989, baseEnd_935989] using wordTrace_append hprefix tailTrace_935989
  have hstable : (prefixWord ++ tailWord_935989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935989).length < 2 ^ (prefixWord ++ tailWord_935989).sum := by decide
  have hdescent : baseEnd_935989 < baseStart_935989 := by decide
  rcases family_descends (prefixWord ++ tailWord_935989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936037 : List Nat := [1, 3, 1, 3, 2, 3, 3, 4]
def baseStart_936037 : Nat := 118140960795 + 936037 * 2 ^ 59
def prefixEnd_936037 : Nat := 4983230072969 + 3 ^ 40 * 936037 * 2
def baseEnd_936037 : Nat := 142410930783010217668963

theorem tailTrace_936037 : CollatzResearch.WordTrace tailWord_936037 prefixEnd_936037 142410930783010217668963 := by
  unfold tailWord_936037
  simp only [CollatzResearch.WordTrace]
  refine ⟨34140074109905286237414365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22760049406603524158276243 34140074109905286237414365)
  ·
    refine ⟨12802527791214482339030387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34140074109905286237414365 12802527791214482339030387)
    ·
      refine ⟨19203791686821723508545581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12802527791214482339030387 19203791686821723508545581)
      ·
        refine ⟨7201421882558146315704593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19203791686821723508545581 7201421882558146315704593)
        ·
          refine ⟨5401066411918609736778445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7201421882558146315704593 5401066411918609736778445)
          ·
            refine ⟨2025399904469478651291917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5401066411918609736778445 2025399904469478651291917)
            ·
              refine ⟨759524964176054494234469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2025399904469478651291917 759524964176054494234469)
              ·
                refine ⟨142410930783010217668963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 759524964176054494234469 142410930783010217668963)
                ·
                  rfl

theorem cell20_936037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4].length) (baseStart_936037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936037 prefixEnd_936037 := by exact prefixLift 936037
  have htrace : WordTrace (prefixWord ++ tailWord_936037) baseStart_936037 baseEnd_936037 := by
    simpa [prefixWord, tailWord_936037, baseEnd_936037] using wordTrace_append hprefix tailTrace_936037
  have hstable : (prefixWord ++ tailWord_936037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936037).length < 2 ^ (prefixWord ++ tailWord_936037).sum := by decide
  have hdescent : baseEnd_936037 < baseStart_936037 := by decide
  rcases family_descends (prefixWord ++ tailWord_936037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936061 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 3]
def baseStart_936061 : Nat := 118140960795 + 936061 * 2 ^ 59
def prefixEnd_936061 : Nat := 4983230072969 + 3 ^ 40 * 936061 * 2
def baseEnd_936061 : Nat := 427243746602993236206791

theorem tailTrace_936061 : CollatzResearch.WordTrace tailWord_936061 prefixEnd_936061 427243746602993236206791 := by
  unfold tailWord_936061
  simp only [CollatzResearch.WordTrace]
  refine ⟨34140949461818338336288037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22760632974545558890858691 34140949461818338336288037)
  ·
    refine ⟨6401428024090938438054007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34140949461818338336288037 6401428024090938438054007)
    ·
      refine ⟨9602142036136407657081011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6401428024090938438054007 9602142036136407657081011)
      ·
        refine ⟨14403213054204611485621517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9602142036136407657081011 14403213054204611485621517)
        ·
          refine ⟨5401204895326729307108069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14403213054204611485621517 5401204895326729307108069)
          ·
            refine ⟨1012725917873761745082763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5401204895326729307108069 1012725917873761745082763)
            ·
              refine ⟨1519088876810642617624145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012725917873761745082763 1519088876810642617624145)
              ·
                refine ⟨1139316657607981963218109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519088876810642617624145 1139316657607981963218109)
                ·
                  refine ⟨427243746602993236206791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139316657607981963218109 427243746602993236206791)
                  ·
                    rfl

theorem cell20_936061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_936061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936061 prefixEnd_936061 := by exact prefixLift 936061
  have htrace : WordTrace (prefixWord ++ tailWord_936061) baseStart_936061 baseEnd_936061 := by
    simpa [prefixWord, tailWord_936061, baseEnd_936061] using wordTrace_append hprefix tailTrace_936061
  have hstable : (prefixWord ++ tailWord_936061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936061).length < 2 ^ (prefixWord ++ tailWord_936061).sum := by decide
  have hdescent : baseEnd_936061 < baseStart_936061 := by decide
  rcases family_descends (prefixWord ++ tailWord_936061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936068 : List Nat := [2, 3, 2, 1, 2, 1, 1, 6, 2]
def baseStart_936068 : Nat := 118140960795 + 936068 * 2 ^ 59
def prefixEnd_936068 : Nat := 4983230072969 + 3 ^ 40 * 936068 * 2
def baseEnd_936068 : Nat := 427246941593732322973429

theorem tailTrace_936068 : CollatzResearch.WordTrace tailWord_936068 prefixEnd_936068 427246941593732322973429 := by
  unfold tailWord_936068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17070602386396489265896429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22760803181861985687861905 17070602386396489265896429)
  ·
    refine ⟨6401475894898683474711161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17070602386396489265896429 6401475894898683474711161)
    ·
      refine ⟨4801106921174012606033371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6401475894898683474711161 4801106921174012606033371)
      ·
        refine ⟨7201660381761018909050057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4801106921174012606033371 7201660381761018909050057)
        ·
          refine ⟨5401245286320764181787543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7201660381761018909050057 5401245286320764181787543)
          ·
            refine ⟨8101867929481146272681315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401245286320764181787543 8101867929481146272681315)
            ·
              refine ⟨12152801894221719409021973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8101867929481146272681315 12152801894221719409021973)
              ·
                refine ⟨569662588791643097297905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12152801894221719409021973 569662588791643097297905)
                ·
                  refine ⟨427246941593732322973429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569662588791643097297905 427246941593732322973429)
                  ·
                    rfl

theorem cell20_936068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_936068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936068 prefixEnd_936068 := by exact prefixLift 936068
  have htrace : WordTrace (prefixWord ++ tailWord_936068) baseStart_936068 baseEnd_936068 := by
    simpa [prefixWord, tailWord_936068, baseEnd_936068] using wordTrace_append hprefix tailTrace_936068
  have hstable : (prefixWord ++ tailWord_936068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936068).length < 2 ^ (prefixWord ++ tailWord_936068).sum := by decide
  have hdescent : baseEnd_936068 < baseStart_936068 := by decide
  rcases family_descends (prefixWord ++ tailWord_936068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936078 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_936078 : Nat := 118140960795 + 936078 * 2 ^ 59
def prefixEnd_936078 : Nat := 4983230072969 + 3 ^ 40 * 936078 * 2
def baseEnd_936078 : Nat := 427251505866216732640055

theorem tailTrace_936078 : CollatzResearch.WordTrace tailWord_936078 prefixEnd_936078 427251505866216732640055 := by
  unfold tailWord_936078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267696187844593779957111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22761046335171166826437925 4267696187844593779957111)
  ·
    refine ⟨6401544281766890669935667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4267696187844593779957111 6401544281766890669935667)
    ·
      refine ⟨9602316422650336004903501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6401544281766890669935667 9602316422650336004903501)
      ·
        refine ⟨3600868658493876001838813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9602316422650336004903501 3600868658493876001838813)
        ·
          refine ⟨1350325746935203500689555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3600868658493876001838813 1350325746935203500689555)
          ·
            refine ⟨2025488620402805251034333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350325746935203500689555 2025488620402805251034333)
            ·
              refine ⟨759558232651051969137875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2025488620402805251034333 759558232651051969137875)
              ·
                refine ⟨1139337348976577953706813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759558232651051969137875 1139337348976577953706813)
                ·
                  refine ⟨427251505866216732640055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139337348976577953706813 427251505866216732640055)
                  ·
                    rfl

theorem cell20_936078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_936078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936078 prefixEnd_936078 := by exact prefixLift 936078
  have htrace : WordTrace (prefixWord ++ tailWord_936078) baseStart_936078 baseEnd_936078 := by
    simpa [prefixWord, tailWord_936078, baseEnd_936078] using wordTrace_append hprefix tailTrace_936078
  have hstable : (prefixWord ++ tailWord_936078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936078).length < 2 ^ (prefixWord ++ tailWord_936078).sum := by decide
  have hdescent : baseEnd_936078 < baseStart_936078 := by decide
  rcases family_descends (prefixWord ++ tailWord_936078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936096 : List Nat := [2, 1, 1, 4, 2, 3, 1, 6]
def baseStart_936096 : Nat := 118140960795 + 936096 * 2 ^ 59
def prefixEnd_936096 : Nat := 4983230072969 + 3 ^ 40 * 936096 * 2
def baseEnd_936096 : Nat := 142419907185562890013327

theorem tailTrace_936096 : CollatzResearch.WordTrace tailWord_936096 prefixEnd_936096 142419907185562890013327 := by
  unfold tailWord_936096
  simp only [CollatzResearch.WordTrace]
  refine ⟨17071113008345769656906071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22761484011127692875874761 17071113008345769656906071)
  ·
    refine ⟨25606669512518654485359107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17071113008345769656906071 25606669512518654485359107)
    ·
      refine ⟨38410004268777981728038661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25606669512518654485359107 38410004268777981728038661)
      ·
        refine ⟨7201875800395871574007249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38410004268777981728038661 7201875800395871574007249)
        ·
          refine ⟨5401406850296903680505437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7201875800395871574007249 5401406850296903680505437)
          ·
            refine ⟨2025527568861338880189539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5401406850296903680505437 2025527568861338880189539)
            ·
              refine ⟨3038291353292008320284309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025527568861338880189539 3038291353292008320284309)
              ·
                refine ⟨142419907185562890013327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3038291353292008320284309 142419907185562890013327)
                ·
                  rfl

theorem cell20_936096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_936096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936096 prefixEnd_936096 := by exact prefixLift 936096
  have htrace : WordTrace (prefixWord ++ tailWord_936096) baseStart_936096 baseEnd_936096 := by
    simpa [prefixWord, tailWord_936096, baseEnd_936096] using wordTrace_append hprefix tailTrace_936096
  have hstable : (prefixWord ++ tailWord_936096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936096).length < 2 ^ (prefixWord ++ tailWord_936096).sum := by decide
  have hdescent : baseEnd_936096 < baseStart_936096 := by decide
  rcases family_descends (prefixWord ++ tailWord_936096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936113 : List Nat := [1, 2, 2, 5, 2, 2, 6]
def baseStart_936113 : Nat := 118140960795 + 936113 * 2 ^ 59
def prefixEnd_936113 : Nat := 4983230072969 + 3 ^ 40 * 936113 * 2
def baseEnd_936113 : Nat := 47474164535545796274805

theorem tailTrace_936113 : CollatzResearch.WordTrace tailWord_936113 prefixEnd_936113 47474164535545796274805 := by
  unfold tailWord_936113
  simp only [CollatzResearch.WordTrace]
  refine ⟨34142846057629951217180993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22761897371753300811453995 34142846057629951217180993)
  ·
    refine ⟨25607134543222463412885745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34142846057629951217180993 25607134543222463412885745)
    ·
      refine ⟨19205350907416847559664309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25607134543222463412885745 19205350907416847559664309)
      ·
        refine ⟨1800501647570329458718529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19205350907416847559664309 1800501647570329458718529)
        ·
          refine ⟨1350376235677747094038897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800501647570329458718529 1350376235677747094038897)
          ·
            refine ⟨1012782176758310320529173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350376235677747094038897 1012782176758310320529173)
            ·
              refine ⟨47474164535545796274805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1012782176758310320529173 47474164535545796274805)
              ·
                rfl

theorem cell20_936113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 6].length) (baseStart_936113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936113 prefixEnd_936113 := by exact prefixLift 936113
  have htrace : WordTrace (prefixWord ++ tailWord_936113) baseStart_936113 baseEnd_936113 := by
    simpa [prefixWord, tailWord_936113, baseEnd_936113] using wordTrace_append hprefix tailTrace_936113
  have hstable : (prefixWord ++ tailWord_936113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936113).length < 2 ^ (prefixWord ++ tailWord_936113).sum := by decide
  have hdescent : baseEnd_936113 < baseStart_936113 := by decide
  rcases family_descends (prefixWord ++ tailWord_936113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936130 : List Nat := [3, 5, 1, 1, 1, 1, 1, 7]
def baseStart_936130 : Nat := 118140960795 + 936130 * 2 ^ 59
def prefixEnd_936130 : Nat := 4983230072969 + 3 ^ 40 * 936130 * 2
def baseEnd_936130 : Nat := 142425080027711887635503

theorem tailTrace_936130 : CollatzResearch.WordTrace tailWord_936130 prefixEnd_936130 142425080027711887635503 := by
  unfold tailWord_936130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535866524642090780137461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22762310732378908747033229 8535866524642090780137461)
  ·
    refine ⟨800237486685196010637887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8535866524642090780137461 800237486685196010637887)
    ·
      refine ⟨1200356230027794015956831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800237486685196010637887 1200356230027794015956831)
      ·
        refine ⟨1800534345041691023935247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200356230027794015956831 1800534345041691023935247)
        ·
          refine ⟨2700801517562536535902871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800534345041691023935247 2700801517562536535902871)
          ·
            refine ⟨4051202276343804803854307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700801517562536535902871 4051202276343804803854307)
            ·
              refine ⟨6076803414515707205781461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051202276343804803854307 6076803414515707205781461)
              ·
                refine ⟨142425080027711887635503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6076803414515707205781461 142425080027711887635503)
                ·
                  rfl

theorem cell20_936130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_936130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936130 prefixEnd_936130 := by exact prefixLift 936130
  have htrace : WordTrace (prefixWord ++ tailWord_936130) baseStart_936130 baseEnd_936130 := by
    simpa [prefixWord, tailWord_936130, baseEnd_936130] using wordTrace_append hprefix tailTrace_936130
  have hstable : (prefixWord ++ tailWord_936130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936130).length < 2 ^ (prefixWord ++ tailWord_936130).sum := by decide
  have hdescent : baseEnd_936130 < baseStart_936130 := by decide
  rcases family_descends (prefixWord ++ tailWord_936130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936178 : List Nat := [3, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_936178 : Nat := 118140960795 + 936178 * 2 ^ 59
def prefixEnd_936178 : Nat := 4983230072969 + 3 ^ 40 * 936178 * 2
def baseEnd_936178 : Nat := 427297148591060829306313

theorem tailTrace_936178 : CollatzResearch.WordTrace tailWord_936178 prefixEnd_936178 427297148591060829306313 := by
  unfold tailWord_936178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8536304200598616829574297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22763477868262978212198125 8536304200598616829574297)
  ·
    refine ⟨6402228150448962622180723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8536304200598616829574297 6402228150448962622180723)
    ·
      refine ⟨9603342225673443933271085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402228150448962622180723 9603342225673443933271085)
      ·
        refine ⟨3601253334627541474976657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9603342225673443933271085 3601253334627541474976657)
        ·
          refine ⟨2700940000970656106232493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3601253334627541474976657 2700940000970656106232493)
          ·
            refine ⟨1012852500363996039837185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2700940000970656106232493 1012852500363996039837185)
            ·
              refine ⟨759639375272997029877889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012852500363996039837185 759639375272997029877889)
              ·
                refine ⟨569729531454747772408417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759639375272997029877889 569729531454747772408417)
                ·
                  refine ⟨427297148591060829306313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569729531454747772408417 427297148591060829306313)
                  ·
                    rfl

theorem cell20_936178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_936178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936178 prefixEnd_936178 := by exact prefixLift 936178
  have htrace : WordTrace (prefixWord ++ tailWord_936178) baseStart_936178 baseEnd_936178 := by
    simpa [prefixWord, tailWord_936178, baseEnd_936178] using wordTrace_append hprefix tailTrace_936178
  have hstable : (prefixWord ++ tailWord_936178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936178).length < 2 ^ (prefixWord ++ tailWord_936178).sum := by decide
  have hdescent : baseEnd_936178 < baseStart_936178 := by decide
  rcases family_descends (prefixWord ++ tailWord_936178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936237 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 4]
def baseStart_936237 : Nat := 118140960795 + 936237 * 2 ^ 59
def prefixEnd_936237 : Nat := 4983230072969 + 3 ^ 40 * 936237 * 2
def baseEnd_936237 : Nat := 427324077798718846339405

theorem tailTrace_936237 : CollatzResearch.WordTrace tailWord_936237 prefixEnd_936237 427324077798718846339405 := by
  unfold tailWord_936237
  simp only [CollatzResearch.WordTrace]
  refine ⟨34147368709180720394694965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22764912472787146929796643 34147368709180720394694965)
  ·
    refine ⟨3201315816485692537002653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34147368709180720394694965 3201315816485692537002653)
    ·
      refine ⟨1200493431182134701375995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3201315816485692537002653 1200493431182134701375995)
      ·
        refine ⟨1800740146773202052063993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200493431182134701375995 1800740146773202052063993)
        ·
          refine ⟨1350555110079901539047995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800740146773202052063993 1350555110079901539047995)
          ·
            refine ⟨2025832665119852308571993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350555110079901539047995 2025832665119852308571993)
            ·
              refine ⟨1519374498839889231428995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025832665119852308571993 1519374498839889231428995)
              ·
                refine ⟨2279061748259833847143493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519374498839889231428995 2279061748259833847143493)
                ·
                  refine ⟨427324077798718846339405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2279061748259833847143493 427324077798718846339405)
                  ·
                    rfl

theorem cell20_936237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_936237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936237 prefixEnd_936237 := by exact prefixLift 936237
  have htrace : WordTrace (prefixWord ++ tailWord_936237) baseStart_936237 baseEnd_936237 := by
    simpa [prefixWord, tailWord_936237, baseEnd_936237] using wordTrace_append hprefix tailTrace_936237
  have hstable : (prefixWord ++ tailWord_936237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936237).length < 2 ^ (prefixWord ++ tailWord_936237).sum := by decide
  have hdescent : baseEnd_936237 < baseStart_936237 := by decide
  rcases family_descends (prefixWord ++ tailWord_936237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936293 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_936293 : Nat := 118140960795 + 936293 * 2 ^ 59
def prefixEnd_936293 : Nat := 4983230072969 + 3 ^ 40 * 936293 * 2
def baseEnd_936293 : Nat := 427349637724631540472509

theorem tailTrace_936293 : CollatzResearch.WordTrace tailWord_936293 prefixEnd_936293 427349637724631540472509 := by
  unfold tailWord_936293
  simp only [CollatzResearch.WordTrace]
  refine ⟨34149411196977841958733533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22766274131318561305822355 34149411196977841958733533)
  ·
    refine ⟨12806029198866690734525075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34149411196977841958733533 12806029198866690734525075)
    ·
      refine ⟨19209043798300036101787613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12806029198866690734525075 19209043798300036101787613)
      ·
        refine ⟨7203391424362513538170355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19209043798300036101787613 7203391424362513538170355)
        ·
          refine ⟨10805087136543770307255533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203391424362513538170355 10805087136543770307255533)
          ·
            refine ⟨4051907676203913865220825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10805087136543770307255533 4051907676203913865220825)
            ·
              refine ⟨3038930757152935398915619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4051907676203913865220825 3038930757152935398915619)
              ·
                refine ⟨4558396135729403098373429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038930757152935398915619 4558396135729403098373429)
                ·
                  refine ⟨427349637724631540472509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4558396135729403098373429 427349637724631540472509)
                  ·
                    rfl

theorem cell20_936293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_936293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936293 prefixEnd_936293 := by exact prefixLift 936293
  have htrace : WordTrace (prefixWord ++ tailWord_936293) baseStart_936293 baseEnd_936293 := by
    simpa [prefixWord, tailWord_936293, baseEnd_936293] using wordTrace_append hprefix tailTrace_936293
  have hstable : (prefixWord ++ tailWord_936293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936293).length < 2 ^ (prefixWord ++ tailWord_936293).sum := by decide
  have hdescent : baseEnd_936293 < baseStart_936293 := by decide
  rcases family_descends (prefixWord ++ tailWord_936293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936296 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 4]
def baseStart_936296 : Nat := 118140960795 + 936296 * 2 ^ 59
def prefixEnd_936296 : Nat := 4983230072969 + 3 ^ 40 * 936296 * 2
def baseEnd_936296 : Nat := 427351007006376863372497

theorem tailTrace_936296 : CollatzResearch.WordTrace tailWord_936296 prefixEnd_936296 427351007006376863372497 := by
  unfold tailWord_936296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17074760307983486735546371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22766347077311315647395161 17074760307983486735546371)
  ·
    refine ⟨25612140461975230103319557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17074760307983486735546371 25612140461975230103319557)
    ·
      refine ⟨4802276336620355644372417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25612140461975230103319557 4802276336620355644372417)
      ·
        refine ⟨3601707252465266733279313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4802276336620355644372417 3601707252465266733279313)
        ·
          refine ⟨2701280439348950049959485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3601707252465266733279313 2701280439348950049959485)
          ·
            refine ⟨1012980164755856268734807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2701280439348950049959485 1012980164755856268734807)
            ·
              refine ⟨1519470247133784403102211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012980164755856268734807 1519470247133784403102211)
              ·
                refine ⟨2279205370700676604653317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519470247133784403102211 2279205370700676604653317)
                ·
                  refine ⟨427351007006376863372497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2279205370700676604653317 427351007006376863372497)
                  ·
                    rfl

theorem cell20_936296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_936296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936296 prefixEnd_936296 := by exact prefixLift 936296
  have htrace : WordTrace (prefixWord ++ tailWord_936296) baseStart_936296 baseEnd_936296 := by
    simpa [prefixWord, tailWord_936296, baseEnd_936296] using wordTrace_append hprefix tailTrace_936296
  have hstable : (prefixWord ++ tailWord_936296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936296).length < 2 ^ (prefixWord ++ tailWord_936296).sum := by decide
  have hdescent : baseEnd_936296 < baseStart_936296 := by decide
  rcases family_descends (prefixWord ++ tailWord_936296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936385 : List Nat := [1, 2, 7, 1, 1, 1, 2, 3, 2]
def baseStart_936385 : Nat := 118140960795 + 936385 * 2 ^ 59
def prefixEnd_936385 : Nat := 4983230072969 + 3 ^ 40 * 936385 * 2
def baseEnd_936385 : Nat := 427391629031488109405467

theorem tailTrace_936385 : CollatzResearch.WordTrace tailWord_936385 prefixEnd_936385 427391629031488109405467 := by
  unfold tailWord_936385
  simp only [CollatzResearch.WordTrace]
  refine ⟨34152766712644541671082609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22768511141763027780721739 34152766712644541671082609)
  ·
    refine ⟨25614575034483406253311957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34152766712644541671082609 25614575034483406253311957)
    ·
      refine ⟨600341602370704834061999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25614575034483406253311957 600341602370704834061999)
      ·
        refine ⟨900512403556057251092999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600341602370704834061999 900512403556057251092999)
        ·
          refine ⟨1350768605334085876639499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900512403556057251092999 1350768605334085876639499)
          ·
            refine ⟨2026152908001128814959249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350768605334085876639499 2026152908001128814959249)
            ·
              refine ⟨1519614681000846611219437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026152908001128814959249 1519614681000846611219437)
              ·
                refine ⟨569855505375317479207289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1519614681000846611219437 569855505375317479207289)
                ·
                  refine ⟨427391629031488109405467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569855505375317479207289 427391629031488109405467)
                  ·
                    rfl

theorem cell20_936385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_936385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936385 prefixEnd_936385 := by exact prefixLift 936385
  have htrace : WordTrace (prefixWord ++ tailWord_936385) baseStart_936385 baseEnd_936385 := by
    simpa [prefixWord, tailWord_936385, baseEnd_936385] using wordTrace_append hprefix tailTrace_936385
  have hstable : (prefixWord ++ tailWord_936385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936385).length < 2 ^ (prefixWord ++ tailWord_936385).sum := by decide
  have hdescent : baseEnd_936385 < baseStart_936385 := by decide
  rcases family_descends (prefixWord ++ tailWord_936385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936393 : List Nat := [1, 2, 1, 1, 2, 1, 5, 5, 2]
def baseStart_936393 : Nat := 118140960795 + 936393 * 2 ^ 59
def prefixEnd_936393 : Nat := 4983230072969 + 3 ^ 40 * 936393 * 2
def baseEnd_936393 : Nat := 427395280449475637138767

theorem tailTrace_936393 : CollatzResearch.WordTrace tailWord_936393 prefixEnd_936393 427395280449475637138767 := by
  unfold tailWord_936393
  simp only [CollatzResearch.WordTrace]
  refine ⟨34153058496615559037373833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22768705664410372691582555 34153058496615559037373833)
  ·
    refine ⟨25614793872461669278030375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34153058496615559037373833 25614793872461669278030375)
    ·
      refine ⟨38422190808692503917045563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25614793872461669278030375 38422190808692503917045563)
      ·
        refine ⟨57633286213038755875568345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38422190808692503917045563 57633286213038755875568345)
        ·
          refine ⟨43224964659779066906676259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57633286213038755875568345 43224964659779066906676259)
          ·
            refine ⟨64837446989668600360014389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43224964659779066906676259 64837446989668600360014389)
            ·
              refine ⟨6078510655281431283751349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64837446989668600360014389 6078510655281431283751349)
              ·
                refine ⟨569860373932634182851689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6078510655281431283751349 569860373932634182851689)
                ·
                  refine ⟨427395280449475637138767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569860373932634182851689 427395280449475637138767)
                  ·
                    rfl

theorem cell20_936393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_936393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936393 prefixEnd_936393 := by exact prefixLift 936393
  have htrace : WordTrace (prefixWord ++ tailWord_936393) baseStart_936393 baseEnd_936393 := by
    simpa [prefixWord, tailWord_936393, baseEnd_936393] using wordTrace_append hprefix tailTrace_936393
  have hstable : (prefixWord ++ tailWord_936393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936393).length < 2 ^ (prefixWord ++ tailWord_936393).sum := by decide
  have hdescent : baseEnd_936393 < baseStart_936393 := by decide
  rcases family_descends (prefixWord ++ tailWord_936393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936434 : List Nat := [3, 2, 1, 4, 2, 2, 2, 4]
def baseStart_936434 : Nat := 118140960795 + 936434 * 2 ^ 59
def prefixEnd_936434 : Nat := 4983230072969 + 3 ^ 40 * 936434 * 2
def baseEnd_936434 : Nat := 142471331322220572257311

theorem tailTrace_936434 : CollatzResearch.WordTrace tailWord_936434 prefixEnd_936434 142471331322220572257311 := by
  unfold tailWord_936434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8538638472366755759904089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22769702592978015359744237 8538638472366755759904089)
  ·
    refine ⟨6403978854275066819928067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8538638472366755759904089 6403978854275066819928067)
    ·
      refine ⟨9605968281412600229892101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6403978854275066819928067 9605968281412600229892101)
      ·
        refine ⟨1801119052764862543104769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9605968281412600229892101 1801119052764862543104769)
        ·
          refine ⟨1350839289573646907328577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1801119052764862543104769 1350839289573646907328577)
          ·
            refine ⟨1013129467180235180496433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350839289573646907328577 1013129467180235180496433)
            ·
              refine ⟨759847100385176385372325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013129467180235180496433 759847100385176385372325)
              ·
                refine ⟨142471331322220572257311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 759847100385176385372325 142471331322220572257311)
                ·
                  rfl

theorem cell20_936434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_936434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936434 prefixEnd_936434 := by exact prefixLift 936434
  have htrace : WordTrace (prefixWord ++ tailWord_936434) baseStart_936434 baseEnd_936434 := by
    simpa [prefixWord, tailWord_936434, baseEnd_936434] using wordTrace_append hprefix tailTrace_936434
  have hstable : (prefixWord ++ tailWord_936434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936434).length < 2 ^ (prefixWord ++ tailWord_936434).sum := by decide
  have hdescent : baseEnd_936434 < baseStart_936434 := by decide
  rcases family_descends (prefixWord ++ tailWord_936434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936438 : List Nat := [5, 1, 1, 1, 2, 1, 3, 6]
def baseStart_936438 : Nat := 118140960795 + 936438 * 2 ^ 59
def prefixEnd_936438 : Nat := 4983230072969 + 3 ^ 40 * 936438 * 2
def baseEnd_936438 : Nat := 142471939891885160212861

theorem tailTrace_936438 : CollatzResearch.WordTrace tailWord_936438 prefixEnd_936438 142471939891885160212861 := by
  unfold tailWord_936438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134668736340783232672623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22769799854301687815174645 2134668736340783232672623)
  ·
    refine ⟨3202003104511174849008935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2134668736340783232672623 3202003104511174849008935)
    ·
      refine ⟨4803004656766762273513403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3202003104511174849008935 4803004656766762273513403)
      ·
        refine ⟨7204506985150143410270105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803004656766762273513403 7204506985150143410270105)
        ·
          refine ⟨5403380238862607557702579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7204506985150143410270105 5403380238862607557702579)
          ·
            refine ⟨8105070358293911336553869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403380238862607557702579 8105070358293911336553869)
            ·
              refine ⟨3039401384360216751207701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8105070358293911336553869 3039401384360216751207701)
              ·
                refine ⟨142471939891885160212861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3039401384360216751207701 142471939891885160212861)
                ·
                  rfl

theorem cell20_936438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_936438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936438 prefixEnd_936438 := by exact prefixLift 936438
  have htrace : WordTrace (prefixWord ++ tailWord_936438) baseStart_936438 baseEnd_936438 := by
    simpa [prefixWord, tailWord_936438, baseEnd_936438] using wordTrace_append hprefix tailTrace_936438
  have hstable : (prefixWord ++ tailWord_936438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936438).length < 2 ^ (prefixWord ++ tailWord_936438).sum := by decide
  have hdescent : baseEnd_936438 < baseStart_936438 := by decide
  rcases family_descends (prefixWord ++ tailWord_936438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936455 : List Nat := [1, 1, 4, 3, 4, 1, 6]
def baseStart_936455 : Nat := 118140960795 + 936455 * 2 ^ 59
def prefixEnd_936455 : Nat := 4983230072969 + 3 ^ 40 * 936455 * 2
def baseEnd_936455 : Nat := 47491508770986553007983

theorem tailTrace_936455 : CollatzResearch.WordTrace tailWord_936455 prefixEnd_936455 47491508770986553007983 := by
  unfold tailWord_936455
  simp only [CollatzResearch.WordTrace]
  refine ⟨34155319822390943626130819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22770213214927295750753879 34155319822390943626130819)
  ·
    refine ⟨51232979733586415439196229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34155319822390943626130819 51232979733586415439196229)
    ·
      refine ⟨9606183700047452894849293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51232979733586415439196229 9606183700047452894849293)
      ·
        refine ⟨3602318887517794835568485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9606183700047452894849293 3602318887517794835568485)
        ·
          refine ⟨675434791409586531669091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3602318887517794835568485 675434791409586531669091)
          ·
            refine ⟨1013152187114379797503637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675434791409586531669091 1013152187114379797503637)
            ·
              refine ⟨47491508770986553007983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1013152187114379797503637 47491508770986553007983)
              ·
                rfl

theorem cell20_936455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 6].length) (baseStart_936455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936455 prefixEnd_936455 := by exact prefixLift 936455
  have htrace : WordTrace (prefixWord ++ tailWord_936455) baseStart_936455 baseEnd_936455 := by
    simpa [prefixWord, tailWord_936455, baseEnd_936455] using wordTrace_append hprefix tailTrace_936455
  have hstable : (prefixWord ++ tailWord_936455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936455).length < 2 ^ (prefixWord ++ tailWord_936455).sum := by decide
  have hdescent : baseEnd_936455 < baseStart_936455 := by decide
  rcases family_descends (prefixWord ++ tailWord_936455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936459 : List Nat := [1, 1, 1, 1, 7, 1, 8]
def baseStart_936459 : Nat := 118140960795 + 936459 * 2 ^ 59
def prefixEnd_936459 : Nat := 4983230072969 + 3 ^ 40 * 936459 * 2
def baseEnd_936459 : Nat := 47491711627541415659833

theorem tailTrace_936459 : CollatzResearch.WordTrace tailWord_936459 prefixEnd_936459 47491711627541415659833 := by
  unfold tailWord_936459
  simp only [CollatzResearch.WordTrace]
  refine ⟨34155465714376452309276431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22770310476250968206184287 34155465714376452309276431)
  ·
    refine ⟨51233198571564678463914647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34155465714376452309276431 51233198571564678463914647)
    ·
      refine ⟨76849797857347017695871971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51233198571564678463914647 76849797857347017695871971)
      ·
        refine ⟨115274696786020526543807957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76849797857347017695871971 115274696786020526543807957)
        ·
          refine ⟨2701750705922356090870499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 115274696786020526543807957 2701750705922356090870499)
          ·
            refine ⟨4052626058883534136305749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701750705922356090870499 4052626058883534136305749)
            ·
              refine ⟨47491711627541415659833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4052626058883534136305749 47491711627541415659833)
              ·
                rfl

theorem cell20_936459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 8].length) (baseStart_936459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936459 prefixEnd_936459 := by exact prefixLift 936459
  have htrace : WordTrace (prefixWord ++ tailWord_936459) baseStart_936459 baseEnd_936459 := by
    simpa [prefixWord, tailWord_936459, baseEnd_936459] using wordTrace_append hprefix tailTrace_936459
  have hstable : (prefixWord ++ tailWord_936459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936459).length < 2 ^ (prefixWord ++ tailWord_936459).sum := by decide
  have hdescent : baseEnd_936459 < baseStart_936459 := by decide
  rcases family_descends (prefixWord ++ tailWord_936459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936461 : List Nat := [1, 7, 1, 1, 1, 2, 3, 2, 2]
def baseStart_936461 : Nat := 118140960795 + 936461 * 2 ^ 59
def prefixEnd_936461 : Nat := 4983230072969 + 3 ^ 40 * 936461 * 2
def baseEnd_936461 : Nat := 427426317502369622871823

theorem tailTrace_936461 : CollatzResearch.WordTrace tailWord_936461 prefixEnd_936461 427426317502369622871823 := by
  unfold tailWord_936461
  simp only [CollatzResearch.WordTrace]
  refine ⟨34155538660369206650849237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22770359106912804433899491 34155538660369206650849237)
  ·
    refine ⟨800520437352403280879279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 34155538660369206650849237 800520437352403280879279)
    ·
      refine ⟨1200780656028604921318919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800520437352403280879279 1200780656028604921318919)
      ·
        refine ⟨1801170984042907381978379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200780656028604921318919 1801170984042907381978379)
        ·
          refine ⟨2701756476064361072967569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801170984042907381978379 2701756476064361072967569)
          ·
            refine ⟨2026317357048270804725677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701756476064361072967569 2026317357048270804725677)
            ·
              refine ⟨759869008893101551772129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2026317357048270804725677 759869008893101551772129)
              ·
                refine ⟨569901756669826163829097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759869008893101551772129 569901756669826163829097)
                ·
                  refine ⟨427426317502369622871823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569901756669826163829097 427426317502369622871823)
                  ·
                    rfl

theorem cell20_936461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_936461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936461 prefixEnd_936461 := by exact prefixLift 936461
  have htrace : WordTrace (prefixWord ++ tailWord_936461) baseStart_936461 baseEnd_936461 := by
    simpa [prefixWord, tailWord_936461, baseEnd_936461] using wordTrace_append hprefix tailTrace_936461
  have hstable : (prefixWord ++ tailWord_936461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936461).length < 2 ^ (prefixWord ++ tailWord_936461).sum := by decide
  have hdescent : baseEnd_936461 < baseStart_936461 := by decide
  rcases family_descends (prefixWord ++ tailWord_936461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936476 : List Nat := [2, 2, 3, 1, 2, 3, 2, 5]
def baseStart_936476 : Nat := 118140960795 + 936476 * 2 ^ 59
def prefixEnd_936476 : Nat := 4983230072969 + 3 ^ 40 * 936476 * 2
def baseEnd_936476 : Nat := 142477721303698745790587

theorem tailTrace_936476 : CollatzResearch.WordTrace tailWord_936476 prefixEnd_936476 142477721303698745790587 := by
  unfold tailWord_936476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17078042877657432106322641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22770723836876576141763521 17078042877657432106322641)
  ·
    refine ⟨12808532158243074079741981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17078042877657432106322641 12808532158243074079741981)
    ·
      refine ⟨4803199559341152779903243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12808532158243074079741981 4803199559341152779903243)
      ·
        refine ⟨7204799339011729169854865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803199559341152779903243 7204799339011729169854865)
        ·
          refine ⟨5403599504258796877391149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7204799339011729169854865 5403599504258796877391149)
          ·
            refine ⟨2026349814097048829021681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5403599504258796877391149 2026349814097048829021681)
            ·
              refine ⟨1519762360572786621766261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026349814097048829021681 1519762360572786621766261)
              ·
                refine ⟨142477721303698745790587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1519762360572786621766261 142477721303698745790587)
                ·
                  rfl

theorem cell20_936476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_936476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936476 prefixEnd_936476 := by exact prefixLift 936476
  have htrace : WordTrace (prefixWord ++ tailWord_936476) baseStart_936476 baseEnd_936476 := by
    simpa [prefixWord, tailWord_936476, baseEnd_936476] using wordTrace_append hprefix tailTrace_936476
  have hstable : (prefixWord ++ tailWord_936476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936476).length < 2 ^ (prefixWord ++ tailWord_936476).sum := by decide
  have hdescent : baseEnd_936476 < baseStart_936476 := by decide
  rcases family_descends (prefixWord ++ tailWord_936476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936497 : List Nat := [1, 2, 2, 3, 1, 1, 4, 6]
def baseStart_936497 : Nat := 118140960795 + 936497 * 2 ^ 59
def prefixEnd_936497 : Nat := 4983230072969 + 3 ^ 40 * 936497 * 2
def baseEnd_936497 : Nat := 142480916294437832557225

theorem tailTrace_936497 : CollatzResearch.WordTrace tailWord_936497 prefixEnd_936497 142480916294437832557225 := by
  unfold tailWord_936497
  simp only [CollatzResearch.WordTrace]
  refine ⟨34156851688238784799159745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22771234458825856532773163 34156851688238784799159745)
  ·
    refine ⟨25617638766179088599369809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34156851688238784799159745 25617638766179088599369809)
    ·
      refine ⟨19213229074634316449527357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25617638766179088599369809 19213229074634316449527357)
      ·
        refine ⟨7204960902987868668572759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19213229074634316449527357 7204960902987868668572759)
        ·
          refine ⟨10807441354481803002859139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7204960902987868668572759 10807441354481803002859139)
          ·
            refine ⟨16211162031722704504288709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10807441354481803002859139 16211162031722704504288709)
            ·
              refine ⟨3039592880948007094554133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16211162031722704504288709 3039592880948007094554133)
              ·
                refine ⟨142480916294437832557225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3039592880948007094554133 142480916294437832557225)
                ·
                  rfl

theorem cell20_936497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_936497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936497 prefixEnd_936497 := by exact prefixLift 936497
  have htrace : WordTrace (prefixWord ++ tailWord_936497) baseStart_936497 baseEnd_936497 := by
    simpa [prefixWord, tailWord_936497, baseEnd_936497] using wordTrace_append hprefix tailTrace_936497
  have hstable : (prefixWord ++ tailWord_936497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936497).length < 2 ^ (prefixWord ++ tailWord_936497).sum := by decide
  have hdescent : baseEnd_936497 < baseStart_936497 := by decide
  rcases family_descends (prefixWord ++ tailWord_936497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936516 : List Nat := [2, 3, 5, 1, 1, 2, 2, 2, 2]
def baseStart_936516 : Nat := 118140960795 + 936516 * 2 ^ 59
def prefixEnd_936516 : Nat := 4983230072969 + 3 ^ 40 * 936516 * 2
def baseEnd_936516 : Nat := 427451421001033876038265

theorem tailTrace_936516 : CollatzResearch.WordTrace tailWord_936516 prefixEnd_936516 427451421001033876038265 := by
  unfold tailWord_936516
  simp only [CollatzResearch.WordTrace]
  refine ⟨17078772337584975522050701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22771696450113300696067601 17078772337584975522050701)
  ·
    refine ⟨6404539626594365820769013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17078772337584975522050701 6404539626594365820769013)
    ·
      refine ⟨600425589993221795697095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6404539626594365820769013 600425589993221795697095)
      ·
        refine ⟨900638384989832693545643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600425589993221795697095 900638384989832693545643)
        ·
          refine ⟨1350957577484749040318465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900638384989832693545643 1350957577484749040318465)
          ·
            refine ⟨1013218183113561780238849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350957577484749040318465 1013218183113561780238849)
            ·
              refine ⟨759913637335171335179137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013218183113561780238849 759913637335171335179137)
              ·
                refine ⟨569935228001378501384353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759913637335171335179137 569935228001378501384353)
                ·
                  refine ⟨427451421001033876038265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569935228001378501384353 427451421001033876038265)
                  ·
                    rfl

theorem cell20_936516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_936516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936516 prefixEnd_936516 := by exact prefixLift 936516
  have htrace : WordTrace (prefixWord ++ tailWord_936516) baseStart_936516 baseEnd_936516 := by
    simpa [prefixWord, tailWord_936516, baseEnd_936516] using wordTrace_append hprefix tailTrace_936516
  have hstable : (prefixWord ++ tailWord_936516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936516).length < 2 ^ (prefixWord ++ tailWord_936516).sum := by decide
  have hdescent : baseEnd_936516 < baseStart_936516 := by decide
  rcases family_descends (prefixWord ++ tailWord_936516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936576 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 3]
def baseStart_936576 : Nat := 118140960795 + 936576 * 2 ^ 59
def prefixEnd_936576 : Nat := 4983230072969 + 3 ^ 40 * 936576 * 2
def baseEnd_936576 : Nat := 427478806635940334038019

theorem tailTrace_936576 : CollatzResearch.WordTrace tailWord_936576 prefixEnd_936576 427478806635940334038019 := by
  unfold tailWord_936576
  simp only [CollatzResearch.WordTrace]
  refine ⟨17079866527476290645642791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22773155369968387527523721 17079866527476290645642791)
  ·
    refine ⟨25619799791214435968464187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17079866527476290645642791 25619799791214435968464187)
    ·
      refine ⟨38429699686821653952696281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25619799791214435968464187 38429699686821653952696281)
      ·
        refine ⟨28822274765116240464522211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38429699686821653952696281 28822274765116240464522211)
        ·
          refine ⟨43233412147674360696783317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28822274765116240464522211 43233412147674360696783317)
          ·
            refine ⟨1013283097211117828830859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43233412147674360696783317 1013283097211117828830859)
            ·
              refine ⟨1519924645816676743246289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013283097211117828830859 1519924645816676743246289)
              ·
                refine ⟨1139943484362507557434717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519924645816676743246289 1139943484362507557434717)
                ·
                  refine ⟨427478806635940334038019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139943484362507557434717 427478806635940334038019)
                  ·
                    rfl

theorem cell20_936576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_936576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936576 prefixEnd_936576 := by exact prefixLift 936576
  have htrace : WordTrace (prefixWord ++ tailWord_936576) baseStart_936576 baseEnd_936576 := by
    simpa [prefixWord, tailWord_936576, baseEnd_936576] using wordTrace_append hprefix tailTrace_936576
  have hstable : (prefixWord ++ tailWord_936576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936576).length < 2 ^ (prefixWord ++ tailWord_936576).sum := by decide
  have hdescent : baseEnd_936576 < baseStart_936576 := by decide
  rcases family_descends (prefixWord ++ tailWord_936576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936583 : List Nat := [1, 1, 4, 2, 1, 2, 1, 6, 2]
def baseStart_936583 : Nat := 118140960795 + 936583 * 2 ^ 59
def prefixEnd_936583 : Nat := 4983230072969 + 3 ^ 40 * 936583 * 2
def baseEnd_936583 : Nat := 427482001626679420804657

theorem tailTrace_936583 : CollatzResearch.WordTrace tailWord_936583 prefixEnd_936583 427482001626679420804657 := by
  unfold tailWord_936583
  simp only [CollatzResearch.WordTrace]
  refine ⟨34159988365927221486790403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22773325577284814324526935 34159988365927221486790403)
  ·
    refine ⟨51239982548890832230185605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34159988365927221486790403 51239982548890832230185605)
    ·
      refine ⟨9607496727917031043159801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51239982548890832230185605 9607496727917031043159801)
      ·
        refine ⟨7205622545937773282369851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9607496727917031043159801 7205622545937773282369851)
        ·
          refine ⟨10808433818906659923554777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205622545937773282369851 10808433818906659923554777)
          ·
            refine ⟨8106325364179994942666083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10808433818906659923554777 8106325364179994942666083)
            ·
              refine ⟨12159488046269992413999125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8106325364179994942666083 12159488046269992413999125)
              ·
                refine ⟨569976002168905894406209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12159488046269992413999125 569976002168905894406209)
                ·
                  refine ⟨427482001626679420804657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569976002168905894406209 427482001626679420804657)
                  ·
                    rfl

theorem cell20_936583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 2].length) (baseStart_936583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936583 prefixEnd_936583 := by exact prefixLift 936583
  have htrace : WordTrace (prefixWord ++ tailWord_936583) baseStart_936583 baseEnd_936583 := by
    simpa [prefixWord, tailWord_936583, baseEnd_936583] using wordTrace_append hprefix tailTrace_936583
  have hstable : (prefixWord ++ tailWord_936583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936583).length < 2 ^ (prefixWord ++ tailWord_936583).sum := by decide
  have hdescent : baseEnd_936583 < baseStart_936583 := by decide
  rcases family_descends (prefixWord ++ tailWord_936583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936652 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_936652 : Nat := 118140960795 + 936652 * 2 ^ 59
def prefixEnd_936652 : Nat := 4983230072969 + 3 ^ 40 * 936652 * 2
def baseEnd_936652 : Nat := 427513495106821847504375

theorem tailTrace_936652 : CollatzResearch.WordTrace tailWord_936652 prefixEnd_936652 427513495106821847504375 := by
  unfold tailWord_936652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17081252501338623135526105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22775003335118164180701473 17081252501338623135526105)
  ·
    refine ⟨12810939376003967351644579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17081252501338623135526105 12810939376003967351644579)
    ·
      refine ⟨19216409064005951027466869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12810939376003967351644579 19216409064005951027466869)
      ·
        refine ⟨1801538349750557908825019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19216409064005951027466869 1801538349750557908825019)
        ·
          refine ⟨2702307524625836863237529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801538349750557908825019 2702307524625836863237529)
          ·
            refine ⟨2026730643469377647428147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2702307524625836863237529 2026730643469377647428147)
            ·
              refine ⟨3040095965204066471142221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026730643469377647428147 3040095965204066471142221)
              ·
                refine ⟨1140035986951524926678333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3040095965204066471142221 1140035986951524926678333)
                ·
                  refine ⟨427513495106821847504375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140035986951524926678333 427513495106821847504375)
                  ·
                    rfl

theorem cell20_936652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_936652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936652 prefixEnd_936652 := by exact prefixLift 936652
  have htrace : WordTrace (prefixWord ++ tailWord_936652) baseStart_936652 baseEnd_936652 := by
    simpa [prefixWord, tailWord_936652, baseEnd_936652] using wordTrace_append hprefix tailTrace_936652
  have hstable : (prefixWord ++ tailWord_936652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936652).length < 2 ^ (prefixWord ++ tailWord_936652).sum := by decide
  have hdescent : baseEnd_936652 < baseStart_936652 := by decide
  rcases family_descends (prefixWord ++ tailWord_936652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936690 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_936690 : Nat := 118140960795 + 936690 * 2 ^ 59
def prefixEnd_936690 : Nat := 4983230072969 + 3 ^ 40 * 936690 * 2
def baseEnd_936690 : Nat := 427530839342262604237553

theorem tailTrace_936690 : CollatzResearch.WordTrace tailWord_936690 prefixEnd_936690 427530839342262604237553 := by
  unfold tailWord_936690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540972744134894690233881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22775927317693052507290349 8540972744134894690233881)
  ·
    refine ⟨6405729558101171017675411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8540972744134894690233881 6405729558101171017675411)
    ·
      refine ⟨9608594337151756526513117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6405729558101171017675411 9608594337151756526513117)
      ·
        refine ⟨3603222876431908697442419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9608594337151756526513117 3603222876431908697442419)
        ·
          refine ⟨5404834314647863046163629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603222876431908697442419 5404834314647863046163629)
          ·
            refine ⟨2026812867992948642311361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5404834314647863046163629 2026812867992948642311361)
            ·
              refine ⟨1520109650994711481733521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026812867992948642311361 1520109650994711481733521)
              ·
                refine ⟨1140082238246033611300141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520109650994711481733521 1140082238246033611300141)
                ·
                  refine ⟨427530839342262604237553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140082238246033611300141 427530839342262604237553)
                  ·
                    rfl

theorem cell20_936690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_936690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936690 prefixEnd_936690 := by exact prefixLift 936690
  have htrace : WordTrace (prefixWord ++ tailWord_936690) baseStart_936690 baseEnd_936690 := by
    simpa [prefixWord, tailWord_936690, baseEnd_936690] using wordTrace_append hprefix tailTrace_936690
  have hstable : (prefixWord ++ tailWord_936690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936690).length < 2 ^ (prefixWord ++ tailWord_936690).sum := by decide
  have hdescent : baseEnd_936690 < baseStart_936690 := by decide
  rcases family_descends (prefixWord ++ tailWord_936690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936735 : List Nat := [1, 1, 2, 4, 2, 2, 1, 5, 2]
def baseStart_936735 : Nat := 118140960795 + 936735 * 2 ^ 59
def prefixEnd_936735 : Nat := 4983230072969 + 3 ^ 40 * 936735 * 2
def baseEnd_936735 : Nat := 427551378568442447737369

theorem tailTrace_936735 : CollatzResearch.WordTrace tailWord_936735 prefixEnd_936735 427551378568442447737369 := by
  unfold tailWord_936735
  simp only [CollatzResearch.WordTrace]
  refine ⟨34165532261376551446323659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22777021507584367630882439 34165532261376551446323659)
  ·
    refine ⟨51248298392064827169485489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34165532261376551446323659 51248298392064827169485489)
    ·
      refine ⟨38436223794048620377114117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51248298392064827169485489 38436223794048620377114117)
      ·
        refine ⟨7206791961384116320708897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38436223794048620377114117 7206791961384116320708897)
        ·
          refine ⟨5405093971038087240531673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7206791961384116320708897 5405093971038087240531673)
          ·
            refine ⟨4053820478278565430398755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5405093971038087240531673 4053820478278565430398755)
            ·
              refine ⟨6080730717417848145598133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4053820478278565430398755 6080730717417848145598133)
              ·
                refine ⟨570068504757923263649825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6080730717417848145598133 570068504757923263649825)
                ·
                  refine ⟨427551378568442447737369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570068504757923263649825 427551378568442447737369)
                  ·
                    rfl

theorem cell20_936735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 2].length) (baseStart_936735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936735 prefixEnd_936735 := by exact prefixLift 936735
  have htrace : WordTrace (prefixWord ++ tailWord_936735) baseStart_936735 baseEnd_936735 := by
    simpa [prefixWord, tailWord_936735, baseEnd_936735] using wordTrace_append hprefix tailTrace_936735
  have hstable : (prefixWord ++ tailWord_936735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936735).length < 2 ^ (prefixWord ++ tailWord_936735).sum := by decide
  have hdescent : baseEnd_936735 < baseStart_936735 := by decide
  rcases family_descends (prefixWord ++ tailWord_936735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936739 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_936739 : Nat := 118140960795 + 936739 * 2 ^ 59
def prefixEnd_936739 : Nat := 4983230072969 + 3 ^ 40 * 936739 * 2
def baseEnd_936739 : Nat := 427553204277436211604019

theorem tailTrace_936739 : CollatzResearch.WordTrace tailWord_936739 prefixEnd_936739 427553204277436211604019 := by
  unfold tailWord_936739
  simp only [CollatzResearch.WordTrace]
  refine ⟨34165678153362060129469271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22777118768908040086312847 34165678153362060129469271)
  ·
    refine ⟨51248517230043090194203907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34165678153362060129469271 51248517230043090194203907)
    ·
      refine ⟨76872775845064635291305861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51248517230043090194203907 76872775845064635291305861)
      ·
        refine ⟨14413645470949619117119849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76872775845064635291305861 14413645470949619117119849)
        ·
          refine ⟨10810234103212214337839887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14413645470949619117119849 10810234103212214337839887)
          ·
            refine ⟨16215351154818321506759831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10810234103212214337839887 16215351154818321506759831)
            ·
              refine ⟨24323026732227482260139747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16215351154818321506759831 24323026732227482260139747)
              ·
                refine ⟨36484540098341223390209621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24323026732227482260139747 36484540098341223390209621)
                ·
                  refine ⟨427553204277436211604019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36484540098341223390209621 427553204277436211604019)
                  ·
                    rfl

theorem cell20_936739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_936739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936739 prefixEnd_936739 := by exact prefixLift 936739
  have htrace : WordTrace (prefixWord ++ tailWord_936739) baseStart_936739 baseEnd_936739 := by
    simpa [prefixWord, tailWord_936739, baseEnd_936739] using wordTrace_append hprefix tailTrace_936739
  have hstable : (prefixWord ++ tailWord_936739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936739).length < 2 ^ (prefixWord ++ tailWord_936739).sum := by decide
  have hdescent : baseEnd_936739 < baseStart_936739 := by decide
  rcases family_descends (prefixWord ++ tailWord_936739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936780 : List Nat := [2, 2, 1, 3, 3, 1, 4, 4]
def baseStart_936780 : Nat := 118140960795 + 936780 * 2 ^ 59
def prefixEnd_936780 : Nat := 4983230072969 + 3 ^ 40 * 936780 * 2
def baseEnd_936780 : Nat := 142523972598207430412395

theorem tailTrace_936780 : CollatzResearch.WordTrace tailWord_936780 prefixEnd_936780 142523972598207430412395 := by
  unfold tailWord_936780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17083586773106762065855897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22778115697475682754474529 17083586773106762065855897)
  ·
    refine ⟨12812690079830071549391923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17083586773106762065855897 12812690079830071549391923)
    ·
      refine ⟨19219035119745107324087885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12812690079830071549391923 19219035119745107324087885)
      ·
        refine ⟨7207138169904415246532957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19219035119745107324087885 7207138169904415246532957)
        ·
          refine ⟨2702676813714155717449859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7207138169904415246532957 2702676813714155717449859)
          ·
            refine ⟨4054015220571233576174789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702676813714155717449859 4054015220571233576174789)
            ·
              refine ⟨760127853857106295532773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4054015220571233576174789 760127853857106295532773)
              ·
                refine ⟨142523972598207430412395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 760127853857106295532773 142523972598207430412395)
                ·
                  rfl

theorem cell20_936780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_936780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936780 prefixEnd_936780 := by exact prefixLift 936780
  have htrace : WordTrace (prefixWord ++ tailWord_936780) baseStart_936780 baseEnd_936780 := by
    simpa [prefixWord, tailWord_936780, baseEnd_936780] using wordTrace_append hprefix tailTrace_936780
  have hstable : (prefixWord ++ tailWord_936780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936780).length < 2 ^ (prefixWord ++ tailWord_936780).sum := by decide
  have hdescent : baseEnd_936780 < baseStart_936780 := by decide
  rcases family_descends (prefixWord ++ tailWord_936780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936821 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 3]
def baseStart_936821 : Nat := 118140960795 + 936821 * 2 ^ 59
def prefixEnd_936821 : Nat := 4983230072969 + 3 ^ 40 * 936821 * 2
def baseEnd_936821 : Nat := 427590631311808370870351

theorem tailTrace_936821 : CollatzResearch.WordTrace tailWord_936821 prefixEnd_936821 427590631311808370870351 := by
  unfold tailWord_936821
  simp only [CollatzResearch.WordTrace]
  refine ⟨34168668939064988133954317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22779112626043325422636211 34168668939064988133954317)
  ·
    refine ⟨12813250852149370550232869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34168668939064988133954317 12813250852149370550232869)
    ·
      refine ⟨2402484534778006978168663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12813250852149370550232869 2402484534778006978168663)
      ·
        refine ⟨3603726802167010467252995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402484534778006978168663 3603726802167010467252995)
        ·
          refine ⟨5405590203250515700879493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603726802167010467252995 5405590203250515700879493)
          ·
            refine ⟨1013548163109471693914905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5405590203250515700879493 1013548163109471693914905)
            ·
              refine ⟨760161122332103770436179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013548163109471693914905 760161122332103770436179)
              ·
                refine ⟨1140241683498155655654269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760161122332103770436179 1140241683498155655654269)
                ·
                  refine ⟨427590631311808370870351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140241683498155655654269 427590631311808370870351)
                  ·
                    rfl

theorem cell20_936821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_936821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936821 prefixEnd_936821 := by exact prefixLift 936821
  have htrace : WordTrace (prefixWord ++ tailWord_936821) baseStart_936821 baseEnd_936821 := by
    simpa [prefixWord, tailWord_936821, baseEnd_936821] using wordTrace_append hprefix tailTrace_936821
  have hstable : (prefixWord ++ tailWord_936821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936821).length < 2 ^ (prefixWord ++ tailWord_936821).sum := by decide
  have hdescent : baseEnd_936821 < baseStart_936821 := by decide
  rcases family_descends (prefixWord ++ tailWord_936821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936825 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 3]
def baseStart_936825 : Nat := 118140960795 + 936825 * 2 ^ 59
def prefixEnd_936825 : Nat := 4983230072969 + 3 ^ 40 * 936825 * 2
def baseEnd_936825 : Nat := 427592457020802134737001

theorem tailTrace_936825 : CollatzResearch.WordTrace tailWord_936825 prefixEnd_936825 427592457020802134737001 := by
  unfold tailWord_936825
  simp only [CollatzResearch.WordTrace]
  refine ⟨34168814831050496817099929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22779209887366997878066619 34168814831050496817099929)
  ·
    refine ⟨25626611123287872612824947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34168814831050496817099929 25626611123287872612824947)
    ·
      refine ⟨38439916684931808919237421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25626611123287872612824947 38439916684931808919237421)
      ·
        refine ⟨14414968756849428344714033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38439916684931808919237421 14414968756849428344714033)
        ·
          refine ⟨10811226567637071258535525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14414968756849428344714033 10811226567637071258535525)
          ·
            refine ⟨2027104981431950860975411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10811226567637071258535525 2027104981431950860975411)
            ·
              refine ⟨3040657472147926291463117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027104981431950860975411 3040657472147926291463117)
              ·
                refine ⟨1140246552055472359298669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3040657472147926291463117 1140246552055472359298669)
                ·
                  refine ⟨427592457020802134737001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140246552055472359298669 427592457020802134737001)
                  ·
                    rfl

theorem cell20_936825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_936825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936825 prefixEnd_936825 := by exact prefixLift 936825
  have htrace : WordTrace (prefixWord ++ tailWord_936825) baseStart_936825 baseEnd_936825 := by
    simpa [prefixWord, tailWord_936825, baseEnd_936825] using wordTrace_append hprefix tailTrace_936825
  have hstable : (prefixWord ++ tailWord_936825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936825).length < 2 ^ (prefixWord ++ tailWord_936825).sum := by decide
  have hdescent : baseEnd_936825 < baseStart_936825 := by decide
  rcases family_descends (prefixWord ++ tailWord_936825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936839 : List Nat := [1, 1, 4, 2, 3, 1, 2, 6]
def baseStart_936839 : Nat := 118140960795 + 936839 * 2 ^ 59
def prefixEnd_936839 : Nat := 4983230072969 + 3 ^ 40 * 936839 * 2
def baseEnd_936839 : Nat := 142532949000760102756759

theorem tailTrace_936839 : CollatzResearch.WordTrace tailWord_936839 prefixEnd_936839 142532949000760102756759 := by
  unfold tailWord_936839
  simp only [CollatzResearch.WordTrace]
  refine ⟨34169325452999777208109571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22779550301999851472073047 34169325452999777208109571)
  ·
    refine ⟨51253988179499665812164357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34169325452999777208109571 51253988179499665812164357)
    ·
      refine ⟨9610122783656187339780817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51253988179499665812164357 9610122783656187339780817)
      ·
        refine ⟨7207592087742140504835613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9610122783656187339780817 7207592087742140504835613)
        ·
          refine ⟨2702847032903302689313355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7207592087742140504835613 2702847032903302689313355)
          ·
            refine ⟨4054270549354954033970033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702847032903302689313355 4054270549354954033970033)
            ·
              refine ⟨3040702912016215525477525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4054270549354954033970033 3040702912016215525477525)
              ·
                refine ⟨142532949000760102756759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3040702912016215525477525 142532949000760102756759)
                ·
                  rfl

theorem cell20_936839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_936839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936839 prefixEnd_936839 := by exact prefixLift 936839
  have htrace : WordTrace (prefixWord ++ tailWord_936839) baseStart_936839 baseEnd_936839 := by
    simpa [prefixWord, tailWord_936839, baseEnd_936839] using wordTrace_append hprefix tailTrace_936839
  have hstable : (prefixWord ++ tailWord_936839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936839).length < 2 ^ (prefixWord ++ tailWord_936839).sum := by decide
  have hdescent : baseEnd_936839 < baseStart_936839 := by decide
  rcases family_descends (prefixWord ++ tailWord_936839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936863 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 3]
def baseStart_936863 : Nat := 118140960795 + 936863 * 2 ^ 59
def prefixEnd_936863 : Nat := 4983230072969 + 3 ^ 40 * 936863 * 2
def baseEnd_936863 : Nat := 427609801256242891470179

theorem tailTrace_936863 : CollatzResearch.WordTrace tailWord_936863 prefixEnd_936863 427609801256242891470179 := by
  unfold tailWord_936863
  simp only [CollatzResearch.WordTrace]
  refine ⟨34170200804912829306983243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22780133869941886204655495 34170200804912829306983243)
  ·
    refine ⟨51255301207369243960474865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34170200804912829306983243 51255301207369243960474865)
    ·
      refine ⟨38441475905526932970356149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51255301207369243960474865 38441475905526932970356149)
      ·
        refine ⟨3603888366143149965970889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38441475905526932970356149 3603888366143149965970889)
        ·
          refine ⟨2702916274607362474478167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3603888366143149965970889 2702916274607362474478167)
          ·
            refine ⟨4054374411911043711717251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702916274607362474478167 4054374411911043711717251)
            ·
              refine ⟨6081561617866565567575877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054374411911043711717251 6081561617866565567575877)
              ·
                refine ⟨1140292803349981043920477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6081561617866565567575877 1140292803349981043920477)
                ·
                  refine ⟨427609801256242891470179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140292803349981043920477 427609801256242891470179)
                  ·
                    rfl

theorem cell20_936863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_936863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936863 prefixEnd_936863 := by exact prefixLift 936863
  have htrace : WordTrace (prefixWord ++ tailWord_936863) baseStart_936863 baseEnd_936863 := by
    simpa [prefixWord, tailWord_936863, baseEnd_936863] using wordTrace_append hprefix tailTrace_936863
  have hstable : (prefixWord ++ tailWord_936863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936863).length < 2 ^ (prefixWord ++ tailWord_936863).sum := by decide
  have hdescent : baseEnd_936863 < baseStart_936863 := by decide
  rcases family_descends (prefixWord ++ tailWord_936863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936866 : List Nat := [3, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_936866 : Nat := 118140960795 + 936866 * 2 ^ 59
def prefixEnd_936866 : Nat := 4983230072969 + 3 ^ 40 * 936866 * 2
def baseEnd_936866 : Nat := 427611170537988214370167

theorem tailTrace_936866 : CollatzResearch.WordTrace tailWord_936866 prefixEnd_936866 427611170537988214370167 := by
  unfold tailWord_936866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542577555975490204835613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22780206815934640546228301 8542577555975490204835613)
  ·
    refine ⟨3203466583490808826813355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8542577555975490204835613 3203466583490808826813355)
    ·
      refine ⟨4805199875236213240220033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3203466583490808826813355 4805199875236213240220033)
      ·
        refine ⟨3603899906427159930165025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4805199875236213240220033 3603899906427159930165025)
        ·
          refine ⟨2702924929820369947623769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3603899906427159930165025 2702924929820369947623769)
          ·
            refine ⟨2027193697365277460717827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2702924929820369947623769 2027193697365277460717827)
            ·
              refine ⟨3040790546047916191076741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027193697365277460717827 3040790546047916191076741)
              ·
                refine ⟨570148227383984285826889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3040790546047916191076741 570148227383984285826889)
                ·
                  refine ⟨427611170537988214370167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570148227383984285826889 427611170537988214370167)
                  ·
                    rfl

theorem cell20_936866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_936866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936866 prefixEnd_936866 := by exact prefixLift 936866
  have htrace : WordTrace (prefixWord ++ tailWord_936866) baseStart_936866 baseEnd_936866 := by
    simpa [prefixWord, tailWord_936866, baseEnd_936866] using wordTrace_append hprefix tailTrace_936866
  have hstable : (prefixWord ++ tailWord_936866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936866).length < 2 ^ (prefixWord ++ tailWord_936866).sum := by decide
  have hdescent : baseEnd_936866 < baseStart_936866 := by decide
  rcases family_descends (prefixWord ++ tailWord_936866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936894 : List Nat := [4, 2, 1, 1, 1, 2, 5, 4]
def baseStart_936894 : Nat := 118140960795 + 936894 * 2 ^ 59
def prefixEnd_936894 : Nat := 4983230072969 + 3 ^ 40 * 936894 * 2
def baseEnd_936894 : Nat := 142541316833648187145573

theorem tailTrace_936894 : CollatzResearch.WordTrace tailWord_936894 prefixEnd_936894 142541316833648187145573 := by
  unfold tailWord_936894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4271416433475065200170217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22780887645200347734241157 4271416433475065200170217)
  ·
    refine ⟨3203562325106298900127663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4271416433475065200170217 3203562325106298900127663)
    ·
      refine ⟨4805343487659448350191495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3203562325106298900127663 4805343487659448350191495)
      ·
        refine ⟨7208015231489172525287243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4805343487659448350191495 7208015231489172525287243)
        ·
          refine ⟨10812022847233758787930865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7208015231489172525287243 10812022847233758787930865)
          ·
            refine ⟨8109017135425319090948149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10812022847233758787930865 8109017135425319090948149)
            ·
              refine ⟨760220356446123664776389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8109017135425319090948149 760220356446123664776389)
              ·
                refine ⟨142541316833648187145573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 760220356446123664776389 142541316833648187145573)
                ·
                  rfl

theorem cell20_936894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_936894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936894 prefixEnd_936894 := by exact prefixLift 936894
  have htrace : WordTrace (prefixWord ++ tailWord_936894) baseStart_936894 baseEnd_936894 := by
    simpa [prefixWord, tailWord_936894, baseEnd_936894] using wordTrace_append hprefix tailTrace_936894
  have hstable : (prefixWord ++ tailWord_936894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936894).length < 2 ^ (prefixWord ++ tailWord_936894).sum := by decide
  have hdescent : baseEnd_936894 < baseStart_936894 := by decide
  rcases family_descends (prefixWord ++ tailWord_936894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936904 : List Nat := [2, 1, 3, 1, 5, 1, 2, 3, 2]
def baseStart_936904 : Nat := 118140960795 + 936904 * 2 ^ 59
def prefixEnd_936904 : Nat := 4983230072969 + 3 ^ 40 * 936904 * 2
def baseEnd_936904 : Nat := 427628514773428971103345

theorem tailTrace_936904 : CollatzResearch.WordTrace tailWord_936904 prefixEnd_936904 427628514773428971103345 := by
  unfold tailWord_936904
  simp only [CollatzResearch.WordTrace]
  refine ⟨17085848098882146654612883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22781130798509528872817177 17085848098882146654612883)
  ·
    refine ⟨25628772148323219981919325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17085848098882146654612883 25628772148323219981919325)
    ·
      refine ⟨9610789555621207493219747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25628772148323219981919325 9610789555621207493219747)
      ·
        refine ⟨14416184333431811239829621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9610789555621207493219747 14416184333431811239829621)
        ·
          refine ⟨1351517281259232303734027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14416184333431811239829621 1351517281259232303734027)
          ·
            refine ⟨2027275921888848455601041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351517281259232303734027 2027275921888848455601041)
            ·
              refine ⟨1520456941416636341700781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027275921888848455601041 1520456941416636341700781)
              ·
                refine ⟨570171353031238628137793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1520456941416636341700781 570171353031238628137793)
                ·
                  refine ⟨427628514773428971103345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570171353031238628137793 427628514773428971103345)
                  ·
                    rfl

theorem cell20_936904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_936904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936904 prefixEnd_936904 := by exact prefixLift 936904
  have htrace : WordTrace (prefixWord ++ tailWord_936904) baseStart_936904 baseEnd_936904 := by
    simpa [prefixWord, tailWord_936904, baseEnd_936904] using wordTrace_append hprefix tailTrace_936904
  have hstable : (prefixWord ++ tailWord_936904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936904).length < 2 ^ (prefixWord ++ tailWord_936904).sum := by decide
  have hdescent : baseEnd_936904 < baseStart_936904 := by decide
  rcases family_descends (prefixWord ++ tailWord_936904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936918 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_936918 : Nat := 118140960795 + 936918 * 2 ^ 59
def prefixEnd_936918 : Nat := 4983230072969 + 3 ^ 40 * 936918 * 2
def baseEnd_936918 : Nat := 427634904754907144636621

theorem tailTrace_936918 : CollatzResearch.WordTrace tailWord_936918 prefixEnd_936918 427634904754907144636621 := by
  unfold tailWord_936918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135762926232098356264713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22781471213142382466823605 2135762926232098356264713)
  ·
    refine ⟨1601822194674073767198535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2135762926232098356264713 1601822194674073767198535)
    ·
      refine ⟨2402733292011110650797803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1601822194674073767198535 2402733292011110650797803)
      ·
        refine ⟨3604099938016665976196705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402733292011110650797803 3604099938016665976196705)
        ·
          refine ⟨2703074953512499482147529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3604099938016665976196705 2703074953512499482147529)
          ·
            refine ⟨2027306215134374611610647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2703074953512499482147529 2027306215134374611610647)
            ·
              refine ⟨3040959322701561917415971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027306215134374611610647 3040959322701561917415971)
              ·
                refine ⟨4561438984052342876123957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040959322701561917415971 4561438984052342876123957)
                ·
                  refine ⟨427634904754907144636621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4561438984052342876123957 427634904754907144636621)
                  ·
                    rfl

theorem cell20_936918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_936918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936918 prefixEnd_936918 := by exact prefixLift 936918
  have htrace : WordTrace (prefixWord ++ tailWord_936918) baseStart_936918 baseEnd_936918 := by
    simpa [prefixWord, tailWord_936918, baseEnd_936918] using wordTrace_append hprefix tailTrace_936918
  have hstable : (prefixWord ++ tailWord_936918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936918).length < 2 ^ (prefixWord ++ tailWord_936918).sum := by decide
  have hdescent : baseEnd_936918 < baseStart_936918 := by decide
  rcases family_descends (prefixWord ++ tailWord_936918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936925 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_936925 : Nat := 118140960795 + 936925 * 2 ^ 59
def prefixEnd_936925 : Nat := 4983230072969 + 3 ^ 40 * 936925 * 2
def baseEnd_936925 : Nat := 427638099745646231403259

theorem tailTrace_936925 : CollatzResearch.WordTrace tailWord_936925 prefixEnd_936925 427638099745646231403259 := by
  unfold tailWord_936925
  simp only [CollatzResearch.WordTrace]
  refine ⟨34172462130688213895740229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22781641420458809263826819 34172462130688213895740229)
  ·
    refine ⟨6407336649504040105451293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34172462130688213895740229 6407336649504040105451293)
    ·
      refine ⟨2402751243564015039544235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6407336649504040105451293 2402751243564015039544235)
      ·
        refine ⟨3604126865346022559316353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402751243564015039544235 3604126865346022559316353)
        ·
          refine ⟨2703095149009516919487265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3604126865346022559316353 2703095149009516919487265)
          ·
            refine ⟨2027321361757137689615449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2703095149009516919487265 2027321361757137689615449)
            ·
              refine ⟨1520491021317853267211587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027321361757137689615449 1520491021317853267211587)
              ·
                refine ⟨2280736531976779900817381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520491021317853267211587 2280736531976779900817381)
                ·
                  refine ⟨427638099745646231403259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280736531976779900817381 427638099745646231403259)
                  ·
                    rfl

theorem cell20_936925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_936925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936925 prefixEnd_936925 := by exact prefixLift 936925
  have htrace : WordTrace (prefixWord ++ tailWord_936925) baseStart_936925 baseEnd_936925 := by
    simpa [prefixWord, tailWord_936925, baseEnd_936925] using wordTrace_append hprefix tailTrace_936925
  have hstable : (prefixWord ++ tailWord_936925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936925).length < 2 ^ (prefixWord ++ tailWord_936925).sum := by decide
  have hdescent : baseEnd_936925 < baseStart_936925 := by decide
  rcases family_descends (prefixWord ++ tailWord_936925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936949 : List Nat := [1, 3, 5, 2, 1, 1, 1, 6]
def baseStart_936949 : Nat := 118140960795 + 936949 * 2 ^ 59
def prefixEnd_936949 : Nat := 4983230072969 + 3 ^ 40 * 936949 * 2
def baseEnd_936949 : Nat := 142549684666536271534387

theorem tailTrace_936949 : CollatzResearch.WordTrace tailWord_936949 prefixEnd_936949 142549684666536271534387 := by
  unfold tailWord_936949
  simp only [CollatzResearch.WordTrace]
  refine ⟨34173337482601265994613901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22782224988400843996409267 34173337482601265994613901)
  ·
    refine ⟨12815001555975474747980213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34173337482601265994613901 12815001555975474747980213)
    ·
      refine ⟨1201406395872700757623145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12815001555975474747980213 1201406395872700757623145)
      ·
        refine ⟨901054796904525568217359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1201406395872700757623145 901054796904525568217359)
        ·
          refine ⟨1351582195356788352326039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901054796904525568217359 1351582195356788352326039)
          ·
            refine ⟨2027373293035182528489059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351582195356788352326039 2027373293035182528489059)
            ·
              refine ⟨3041059939552773792733589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027373293035182528489059 3041059939552773792733589)
              ·
                refine ⟨142549684666536271534387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3041059939552773792733589 142549684666536271534387)
                ·
                  rfl

theorem cell20_936949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 6].length) (baseStart_936949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936949 prefixEnd_936949 := by exact prefixLift 936949
  have htrace : WordTrace (prefixWord ++ tailWord_936949) baseStart_936949 baseEnd_936949 := by
    simpa [prefixWord, tailWord_936949, baseEnd_936949] using wordTrace_append hprefix tailTrace_936949
  have hstable : (prefixWord ++ tailWord_936949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936949).length < 2 ^ (prefixWord ++ tailWord_936949).sum := by decide
  have hdescent : baseEnd_936949 < baseStart_936949 := by decide
  rcases family_descends (prefixWord ++ tailWord_936949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936984 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_936984 : Nat := 118140960795 + 936984 * 2 ^ 59
def prefixEnd_936984 : Nat := 4983230072969 + 3 ^ 40 * 936984 * 2
def baseEnd_936984 : Nat := 427665028953304248436351

theorem tailTrace_936984 : CollatzResearch.WordTrace tailWord_936984 prefixEnd_936984 427665028953304248436351 := by
  unfold tailWord_936984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17087307018737233486069003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22783076024982977981425337 17087307018737233486069003)
  ·
    refine ⟨25630960528105850229103505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17087307018737233486069003 25630960528105850229103505)
    ·
      refine ⟨19223220396079387671827629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25630960528105850229103505 19223220396079387671827629)
      ·
        refine ⟨7208707648529770376935361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19223220396079387671827629 7208707648529770376935361)
        ·
          refine ⟨5406530736397327782701521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7208707648529770376935361 5406530736397327782701521)
          ·
            refine ⟨4054898052297995837026141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5406530736397327782701521 4054898052297995837026141)
            ·
              refine ⟨1520586769611748438884803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4054898052297995837026141 1520586769611748438884803)
              ·
                refine ⟨2280880154417622658327205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520586769611748438884803 2280880154417622658327205)
                ·
                  refine ⟨427665028953304248436351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280880154417622658327205 427665028953304248436351)
                  ·
                    rfl

theorem cell20_936984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_936984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936984 prefixEnd_936984 := by exact prefixLift 936984
  have htrace : WordTrace (prefixWord ++ tailWord_936984) baseStart_936984 baseEnd_936984 := by
    simpa [prefixWord, tailWord_936984, baseEnd_936984] using wordTrace_append hprefix tailTrace_936984
  have hstable : (prefixWord ++ tailWord_936984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936984).length < 2 ^ (prefixWord ++ tailWord_936984).sum := by decide
  have hdescent : baseEnd_936984 < baseStart_936984 := by decide
  rcases family_descends (prefixWord ++ tailWord_936984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936991 : List Nat := [1, 1, 2, 4, 1, 4, 2, 5]
def baseStart_936991 : Nat := 118140960795 + 936991 * 2 ^ 59
def prefixEnd_936991 : Nat := 4983230072969 + 3 ^ 40 * 936991 * 2
def baseEnd_936991 : Nat := 142556074648014445067663

theorem tailTrace_936991 : CollatzResearch.WordTrace tailWord_936991 prefixEnd_936991 142556074648014445067663 := by
  unfold tailWord_936991
  simp only [CollatzResearch.WordTrace]
  refine ⟨34174869348449107167642827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22783246232299404778428551 34174869348449107167642827)
  ·
    refine ⟨51262304022673660751464241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34174869348449107167642827 51262304022673660751464241)
    ·
      refine ⟨38446728017005245563598181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51262304022673660751464241 38446728017005245563598181)
      ·
        refine ⟨7208761503188483543174659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38446728017005245563598181 7208761503188483543174659)
        ·
          refine ⟨10813142254782725314761989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7208761503188483543174659 10813142254782725314761989)
          ·
            refine ⟨2027464172771760996517873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10813142254782725314761989 2027464172771760996517873)
            ·
              refine ⟨1520598129578820747388405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027464172771760996517873 1520598129578820747388405)
              ·
                refine ⟨142556074648014445067663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1520598129578820747388405 142556074648014445067663)
                ·
                  rfl

theorem cell20_936991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_936991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936991 prefixEnd_936991 := by exact prefixLift 936991
  have htrace : WordTrace (prefixWord ++ tailWord_936991) baseStart_936991 baseEnd_936991 := by
    simpa [prefixWord, tailWord_936991, baseEnd_936991] using wordTrace_append hprefix tailTrace_936991
  have hstable : (prefixWord ++ tailWord_936991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936991).length < 2 ^ (prefixWord ++ tailWord_936991).sum := by decide
  have hdescent : baseEnd_936991 < baseStart_936991 := by decide
  rcases family_descends (prefixWord ++ tailWord_936991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936994 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_936994 : Nat := 118140960795 + 936994 * 2 ^ 59
def prefixEnd_936994 : Nat := 4983230072969 + 3 ^ 40 * 936994 * 2
def baseEnd_936994 : Nat := 427669593225788658102977

theorem tailTrace_936994 : CollatzResearch.WordTrace tailWord_936994 prefixEnd_936994 427669593225788658102977 := by
  unfold tailWord_936994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8543744691859559670000509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22783319178292159120001357 8543744691859559670000509)
  ·
    refine ⟨3203904259447334876250191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8543744691859559670000509 3203904259447334876250191)
    ·
      refine ⟨4805856389171002314375287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3203904259447334876250191 4805856389171002314375287)
      ·
        refine ⟨7208784583756503471562931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4805856389171002314375287 7208784583756503471562931)
        ·
          refine ⟨10813176875634755207344397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7208784583756503471562931 10813176875634755207344397)
          ·
            refine ⟨4054941328363033202754149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10813176875634755207344397 4054941328363033202754149)
            ·
              refine ⟨760301499068068725516403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4054941328363033202754149 760301499068068725516403)
              ·
                refine ⟨1140452248602103088274605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760301499068068725516403 1140452248602103088274605)
                ·
                  refine ⟨427669593225788658102977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140452248602103088274605 427669593225788658102977)
                  ·
                    rfl

theorem cell20_936994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_936994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_936994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_936994 prefixEnd_936994 := by exact prefixLift 936994
  have htrace : WordTrace (prefixWord ++ tailWord_936994) baseStart_936994 baseEnd_936994 := by
    simpa [prefixWord, tailWord_936994, baseEnd_936994] using wordTrace_append hprefix tailTrace_936994
  have hstable : (prefixWord ++ tailWord_936994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936994).length < 2 ^ (prefixWord ++ tailWord_936994).sum := by decide
  have hdescent : baseEnd_936994 < baseStart_936994 := by decide
  rcases family_descends (prefixWord ++ tailWord_936994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937050 : List Nat := [3, 1, 1, 2, 1, 1, 2, 9]
def baseStart_937050 : Nat := 118140960795 + 937050 * 2 ^ 59
def prefixEnd_937050 : Nat := 4983230072969 + 3 ^ 40 * 937050 * 2
def baseEnd_937050 : Nat := 142565051050567117412027

theorem tailTrace_937050 : CollatzResearch.WordTrace tailWord_937050 prefixEnd_937050 142565051050567117412027 := by
  unfold tailWord_937050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544255313808840061010151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22784680836823573496027069 8544255313808840061010151)
  ·
    refine ⟨12816382970713260091515227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8544255313808840061010151 12816382970713260091515227)
    ·
      refine ⟨19224574456069890137272841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12816382970713260091515227 19224574456069890137272841)
      ·
        refine ⟨14418430842052417602954631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19224574456069890137272841 14418430842052417602954631)
        ·
          refine ⟨21627646263078626404431947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14418430842052417602954631 21627646263078626404431947)
          ·
            refine ⟨32441469394617939606647921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21627646263078626404431947 32441469394617939606647921)
            ·
              refine ⟨24331102045963454704985941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32441469394617939606647921 24331102045963454704985941)
              ·
                refine ⟨142565051050567117412027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24331102045963454704985941 142565051050567117412027)
                ·
                  rfl

theorem cell20_937050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_937050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937050 prefixEnd_937050 := by exact prefixLift 937050
  have htrace : WordTrace (prefixWord ++ tailWord_937050) baseStart_937050 baseEnd_937050 := by
    simpa [prefixWord, tailWord_937050, baseEnd_937050] using wordTrace_append hprefix tailTrace_937050
  have hstable : (prefixWord ++ tailWord_937050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937050).length < 2 ^ (prefixWord ++ tailWord_937050).sum := by decide
  have hdescent : baseEnd_937050 < baseStart_937050 := by decide
  rcases family_descends (prefixWord ++ tailWord_937050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937074 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_937074 : Nat := 118140960795 + 937074 * 2 ^ 59
def prefixEnd_937074 : Nat := 4983230072969 + 3 ^ 40 * 937074 * 2
def baseEnd_937074 : Nat := 427706107405663935435983

theorem tailTrace_937074 : CollatzResearch.WordTrace tailWord_937074 prefixEnd_937074 427706107405663935435983 := by
  unfold tailWord_937074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544474151787103085728569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22785264404765608228609517 8544474151787103085728569)
  ·
    refine ⟨6408355613840327314296427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8544474151787103085728569 6408355613840327314296427)
    ·
      refine ⟨9612533420760490971444641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6408355613840327314296427 9612533420760490971444641)
      ·
        refine ⟨7209400065570368228583481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9612533420760490971444641 7209400065570368228583481)
        ·
          refine ⟨5407050049177776171437611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7209400065570368228583481 5407050049177776171437611)
          ·
            refine ⟨8110575073766664257156417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407050049177776171437611 8110575073766664257156417)
            ·
              refine ⟨6082931305324998192867313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8110575073766664257156417 6082931305324998192867313)
              ·
                refine ⟨4562198478993748644650485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6082931305324998192867313 4562198478993748644650485)
                ·
                  refine ⟨427706107405663935435983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4562198478993748644650485 427706107405663935435983)
                  ·
                    rfl

theorem cell20_937074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_937074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937074 prefixEnd_937074 := by exact prefixLift 937074
  have htrace : WordTrace (prefixWord ++ tailWord_937074) baseStart_937074 baseEnd_937074 := by
    simpa [prefixWord, tailWord_937074, baseEnd_937074] using wordTrace_append hprefix tailTrace_937074
  have hstable : (prefixWord ++ tailWord_937074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937074).length < 2 ^ (prefixWord ++ tailWord_937074).sum := by decide
  have hdescent : baseEnd_937074 < baseStart_937074 := by decide
  rcases family_descends (prefixWord ++ tailWord_937074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937098 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_937098 : Nat := 118140960795 + 937098 * 2 ^ 59
def prefixEnd_937098 : Nat := 4983230072969 + 3 ^ 40 * 937098 * 2
def baseEnd_937098 : Nat := 427717061659626518635885

theorem tailTrace_937098 : CollatzResearch.WordTrace tailWord_937098 prefixEnd_937098 427717061659626518635885 := by
  unfold tailWord_937098
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544692989765366110446987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22785847972707642961191965 8544692989765366110446987)
  ·
    refine ⟨12817039484648049165670481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8544692989765366110446987 12817039484648049165670481)
    ·
      refine ⟨9612779613486036874252861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12817039484648049165670481 9612779613486036874252861)
      ·
        refine ⟨3604792355057263827844823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9612779613486036874252861 3604792355057263827844823)
        ·
          refine ⟨5407188532585895741767235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3604792355057263827844823 5407188532585895741767235)
          ·
            refine ⟨8110782798878843612650853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407188532585895741767235 8110782798878843612650853)
            ·
              refine ⟨1520771774789783177372035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8110782798878843612650853 1520771774789783177372035)
              ·
                refine ⟨2281157662184674766058053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520771774789783177372035 2281157662184674766058053)
                ·
                  refine ⟨427717061659626518635885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281157662184674766058053 427717061659626518635885)
                  ·
                    rfl

theorem cell20_937098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_937098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937098 prefixEnd_937098 := by exact prefixLift 937098
  have htrace : WordTrace (prefixWord ++ tailWord_937098) baseStart_937098 baseEnd_937098 := by
    simpa [prefixWord, tailWord_937098, baseEnd_937098] using wordTrace_append hprefix tailTrace_937098
  have hstable : (prefixWord ++ tailWord_937098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937098).length < 2 ^ (prefixWord ++ tailWord_937098).sum := by decide
  have hdescent : baseEnd_937098 < baseStart_937098 := by decide
  rcases family_descends (prefixWord ++ tailWord_937098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937122 : List Nat := [3, 3, 1, 3, 2, 1, 1, 6]
def baseStart_937122 : Nat := 118140960795 + 937122 * 2 ^ 59
def prefixEnd_937122 : Nat := 4983230072969 + 3 ^ 40 * 937122 * 2
def baseEnd_937122 : Nat := 142576005304529700611929

theorem tailTrace_937122 : CollatzResearch.WordTrace tailWord_937122 prefixEnd_937122 142576005304529700611929 := by
  unfold tailWord_937122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544911827743629135165405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22786431540649677693774413 8544911827743629135165405)
  ·
    refine ⟨3204341935403860925687027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8544911827743629135165405 3204341935403860925687027)
    ·
      refine ⟨4806512903105791388530541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3204341935403860925687027 4806512903105791388530541)
      ·
        refine ⟨1802442338664671770698953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4806512903105791388530541 1802442338664671770698953)
        ·
          refine ⟨1351831753998503828024215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802442338664671770698953 1351831753998503828024215)
          ·
            refine ⟨2027747630997755742036323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351831753998503828024215 2027747630997755742036323)
            ·
              refine ⟨3041621446496633613054485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027747630997755742036323 3041621446496633613054485)
              ·
                refine ⟨142576005304529700611929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3041621446496633613054485 142576005304529700611929)
                ·
                  rfl

theorem cell20_937122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_937122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937122 prefixEnd_937122 := by exact prefixLift 937122
  have htrace : WordTrace (prefixWord ++ tailWord_937122) baseStart_937122 baseEnd_937122 := by
    simpa [prefixWord, tailWord_937122, baseEnd_937122] using wordTrace_append hprefix tailTrace_937122
  have hstable : (prefixWord ++ tailWord_937122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937122).length < 2 ^ (prefixWord ++ tailWord_937122).sum := by decide
  have hdescent : baseEnd_937122 < baseStart_937122 := by decide
  rcases family_descends (prefixWord ++ tailWord_937122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937153 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 4]
def baseStart_937153 : Nat := 118140960795 + 937153 * 2 ^ 59
def prefixEnd_937153 : Nat := 4983230072969 + 3 ^ 40 * 937153 * 2
def baseEnd_937153 : Nat := 427742165158290771802327

theorem tailTrace_937153 : CollatzResearch.WordTrace tailWord_937153 prefixEnd_937153 427742165158290771802327 := by
  unfold tailWord_937153
  simp only [CollatzResearch.WordTrace]
  refine ⟨34180777973862208835040113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22787185315908139223360075 34180777973862208835040113)
  ·
    refine ⟨25635583480396656626280085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34180777973862208835040113 25635583480396656626280085)
    ·
      refine ⟨1201667975643593279356879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25635583480396656626280085 1201667975643593279356879)
      ·
        refine ⟨1802501963465389919035319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201667975643593279356879 1802501963465389919035319)
        ·
          refine ⟨2703752945198084878552979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802501963465389919035319 2703752945198084878552979)
          ·
            refine ⟨4055629417797127317829469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703752945198084878552979 4055629417797127317829469)
            ·
              refine ⟨1520861031673922744186051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4055629417797127317829469 1520861031673922744186051)
              ·
                refine ⟨2281291547510884116279077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520861031673922744186051 2281291547510884116279077)
                ·
                  refine ⟨427742165158290771802327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281291547510884116279077 427742165158290771802327)
                  ·
                    rfl

theorem cell20_937153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_937153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937153 prefixEnd_937153 := by exact prefixLift 937153
  have htrace : WordTrace (prefixWord ++ tailWord_937153) baseStart_937153 baseEnd_937153 := by
    simpa [prefixWord, tailWord_937153, baseEnd_937153] using wordTrace_append hprefix tailTrace_937153
  have hstable : (prefixWord ++ tailWord_937153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937153).length < 2 ^ (prefixWord ++ tailWord_937153).sum := by decide
  have hdescent : baseEnd_937153 < baseStart_937153 := by decide
  rcases family_descends (prefixWord ++ tailWord_937153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937202 : List Nat := [3, 2, 1, 3, 11]
def baseStart_937202 : Nat := 118140960795 + 937202 * 2 ^ 59
def prefixEnd_937202 : Nat := 4983230072969 + 3 ^ 40 * 937202 * 2
def baseEnd_937202 : Nat := 5281043581400794804553

theorem tailTrace_937202 : CollatzResearch.WordTrace tailWord_937202 prefixEnd_937202 5281043581400794804553 := by
  unfold tailWord_937202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8545641287671172550893465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22788376767123126802382573 8545641287671172550893465)
  ·
    refine ⟨6409230965753379413170099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8545641287671172550893465 6409230965753379413170099)
    ·
      refine ⟨9613846448630069119755149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6409230965753379413170099 9613846448630069119755149)
      ·
        refine ⟨3605192418236275919908181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9613846448630069119755149 3605192418236275919908181)
        ·
          refine ⟨5281043581400794804553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3605192418236275919908181 5281043581400794804553)
          ·
            rfl

theorem cell20_937202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 11].length) (baseStart_937202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937202 prefixEnd_937202 := by exact prefixLift 937202
  have htrace : WordTrace (prefixWord ++ tailWord_937202) baseStart_937202 baseEnd_937202 := by
    simpa [prefixWord, tailWord_937202, baseEnd_937202] using wordTrace_append hprefix tailTrace_937202
  have hstable : (prefixWord ++ tailWord_937202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937202).length < 2 ^ (prefixWord ++ tailWord_937202).sum := by decide
  have hdescent : baseEnd_937202 < baseStart_937202 := by decide
  rcases family_descends (prefixWord ++ tailWord_937202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937204 : List Nat := [2, 6, 1, 2, 1, 1, 1, 4, 2]
def baseStart_937204 : Nat := 118140960795 + 937204 * 2 ^ 59
def prefixEnd_937204 : Nat := 4983230072969 + 3 ^ 40 * 937204 * 2
def baseEnd_937204 : Nat := 427765442947961261102119

theorem tailTrace_937204 : CollatzResearch.WordTrace tailWord_937204 prefixEnd_937204 427765442947961261102119 := by
  unfold tailWord_937204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17091319048338722272573333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22788425397784963030097777 17091319048338722272573333)
  ·
    refine ⟨801155580390877606526875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17091319048338722272573333 801155580390877606526875)
    ·
      refine ⟨1201733370586316409790313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801155580390877606526875 1201733370586316409790313)
      ·
        refine ⟨901300027939737307342735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1201733370586316409790313 901300027939737307342735)
        ·
          refine ⟨1351950041909605961014103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901300027939737307342735 1351950041909605961014103)
          ·
            refine ⟨2027925062864408941521155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351950041909605961014103 2027925062864408941521155)
            ·
              refine ⟨3041887594296613412281733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027925062864408941521155 3041887594296613412281733)
              ·
                refine ⟨570353923930615014802825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3041887594296613412281733 570353923930615014802825)
                ·
                  refine ⟨427765442947961261102119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570353923930615014802825 427765442947961261102119)
                  ·
                    rfl

theorem cell20_937204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_937204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937204 prefixEnd_937204 := by exact prefixLift 937204
  have htrace : WordTrace (prefixWord ++ tailWord_937204) baseStart_937204 baseEnd_937204 := by
    simpa [prefixWord, tailWord_937204, baseEnd_937204] using wordTrace_append hprefix tailTrace_937204
  have hstable : (prefixWord ++ tailWord_937204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937204).length < 2 ^ (prefixWord ++ tailWord_937204).sum := by decide
  have hdescent : baseEnd_937204 < baseStart_937204 := by decide
  rcases family_descends (prefixWord ++ tailWord_937204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937219 : List Nat := [1, 1, 1, 3, 2, 6, 1, 5]
def baseStart_937219 : Nat := 118140960795 + 937219 * 2 ^ 59
def prefixEnd_937219 : Nat := 4983230072969 + 3 ^ 40 * 937219 * 2
def baseEnd_937219 : Nat := 142590763118895958534019

theorem tailTrace_937219 : CollatzResearch.WordTrace tailWord_937219 prefixEnd_937219 142590763118895958534019 := by
  unfold tailWord_937219
  simp only [CollatzResearch.WordTrace]
  refine ⟨34183185191623102106942711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22788790127748734737961807 34183185191623102106942711)
  ·
    refine ⟨51274777787434653160414067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34183185191623102106942711 51274777787434653160414067)
    ·
      refine ⟨76912166681151979740621101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51274777787434653160414067 76912166681151979740621101)
      ·
        refine ⟨28842062505431992402732913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76912166681151979740621101 28842062505431992402732913)
        ·
          refine ⟨21631546879073994302049685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28842062505431992402732913 21631546879073994302049685)
          ·
            refine ⟨1013978759956593482908579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21631546879073994302049685 1013978759956593482908579)
            ·
              refine ⟨1520968139934890224362869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013978759956593482908579 1520968139934890224362869)
              ·
                refine ⟨142590763118895958534019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1520968139934890224362869 142590763118895958534019)
                ·
                  rfl

theorem cell20_937219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 5].length) (baseStart_937219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937219 prefixEnd_937219 := by exact prefixLift 937219
  have htrace : WordTrace (prefixWord ++ tailWord_937219) baseStart_937219 baseEnd_937219 := by
    simpa [prefixWord, tailWord_937219, baseEnd_937219] using wordTrace_append hprefix tailTrace_937219
  have hstable : (prefixWord ++ tailWord_937219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937219).length < 2 ^ (prefixWord ++ tailWord_937219).sum := by decide
  have hdescent : baseEnd_937219 < baseStart_937219 := by decide
  rcases family_descends (prefixWord ++ tailWord_937219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937233 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_937233 : Nat := 118140960795 + 937233 * 2 ^ 59
def prefixEnd_937233 : Nat := 4983230072969 + 3 ^ 40 * 937233 * 2
def baseEnd_937233 : Nat := 427778679338166049135333

theorem tailTrace_937233 : CollatzResearch.WordTrace tailWord_937233 prefixEnd_937233 427778679338166049135333 := by
  unfold tailWord_937233
  simp only [CollatzResearch.WordTrace]
  refine ⟨34183695813572382497952353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22789130542381588331968235 34183695813572382497952353)
  ·
    refine ⟨25637771860179286873464265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34183695813572382497952353 25637771860179286873464265)
    ·
      refine ⟨19228328895134465155098199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25637771860179286873464265 19228328895134465155098199)
      ·
        refine ⟨28842493342701697732647299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19228328895134465155098199 28842493342701697732647299)
        ·
          refine ⟨43263740014052546598970949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28842493342701697732647299 43263740014052546598970949)
          ·
            refine ⟨8111951252634852487307053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43263740014052546598970949 8111951252634852487307053)
            ·
              refine ⟨3041981719738069682740145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8111951252634852487307053 3041981719738069682740145)
              ·
                refine ⟨2281486289803552262055109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041981719738069682740145 2281486289803552262055109)
                ·
                  refine ⟨427778679338166049135333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281486289803552262055109 427778679338166049135333)
                  ·
                    rfl

theorem cell20_937233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_937233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937233 prefixEnd_937233 := by exact prefixLift 937233
  have htrace : WordTrace (prefixWord ++ tailWord_937233) baseStart_937233 baseEnd_937233 := by
    simpa [prefixWord, tailWord_937233, baseEnd_937233] using wordTrace_append hprefix tailTrace_937233
  have hstable : (prefixWord ++ tailWord_937233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937233).length < 2 ^ (prefixWord ++ tailWord_937233).sum := by decide
  have hdescent : baseEnd_937233 < baseStart_937233 := by decide
  rcases family_descends (prefixWord ++ tailWord_937233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937277 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 3]
def baseStart_937277 : Nat := 118140960795 + 937277 * 2 ^ 59
def prefixEnd_937277 : Nat := 4983230072969 + 3 ^ 40 * 937277 * 2
def baseEnd_937277 : Nat := 427798762137097451668487

theorem tailTrace_937277 : CollatzResearch.WordTrace tailWord_937277 prefixEnd_937277 427798762137097451668487 := by
  unfold tailWord_937277
  simp only [CollatzResearch.WordTrace]
  refine ⟨34185300625412978012554085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22790200416941985341702723 34185300625412978012554085)
  ·
    refine ⟨6409743867264933377353891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34185300625412978012554085 6409743867264933377353891)
    ·
      refine ⟨9614615800897400066030837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6409743867264933377353891 9614615800897400066030837)
      ·
        refine ⟨901370231334131256190391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9614615800897400066030837 901370231334131256190391)
        ·
          refine ⟨1352055347001196884285587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901370231334131256190391 1352055347001196884285587)
          ·
            refine ⟨2028083020501795326428381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352055347001196884285587 2028083020501795326428381)
            ·
              refine ⟨760531132688173247410643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2028083020501795326428381 760531132688173247410643)
              ·
                refine ⟨1140796699032259871115965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760531132688173247410643 1140796699032259871115965)
                ·
                  refine ⟨427798762137097451668487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140796699032259871115965 427798762137097451668487)
                  ·
                    rfl

theorem cell20_937277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_937277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937277 prefixEnd_937277 := by exact prefixLift 937277
  have htrace : WordTrace (prefixWord ++ tailWord_937277) baseStart_937277 baseEnd_937277 := by
    simpa [prefixWord, tailWord_937277, baseEnd_937277] using wordTrace_append hprefix tailTrace_937277
  have hstable : (prefixWord ++ tailWord_937277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937277).length < 2 ^ (prefixWord ++ tailWord_937277).sum := by decide
  have hdescent : baseEnd_937277 < baseStart_937277 := by decide
  rcases family_descends (prefixWord ++ tailWord_937277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937316 : List Nat := [2, 3, 1, 1, 3, 2, 8]
def baseStart_937316 : Nat := 118140960795 + 937316 * 2 ^ 59
def prefixEnd_937316 : Nat := 4983230072969 + 3 ^ 40 * 937316 * 2
def baseEnd_937316 : Nat := 47535173644420738818703

theorem tailTrace_937316 : CollatzResearch.WordTrace tailWord_937316 prefixEnd_937316 47535173644420738818703 := by
  unfold tailWord_937316
  simp only [CollatzResearch.WordTrace]
  refine ⟨17093361536135843836611901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22791148714847791782149201 17093361536135843836611901)
  ·
    refine ⟨6410010576050941438729463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17093361536135843836611901 6410010576050941438729463)
    ·
      refine ⟨9615015864076412158094195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6410010576050941438729463 9615015864076412158094195)
      ·
        refine ⟨14422523796114618237141293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9615015864076412158094195 14422523796114618237141293)
        ·
          refine ⟨5408446423542981838927985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14422523796114618237141293 5408446423542981838927985)
          ·
            refine ⟨4056334817657236379195989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5408446423542981838927985 4056334817657236379195989)
            ·
              refine ⟨47535173644420738818703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4056334817657236379195989 47535173644420738818703)
              ·
                rfl

theorem cell20_937316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 8].length) (baseStart_937316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937316 prefixEnd_937316 := by exact prefixLift 937316
  have htrace : WordTrace (prefixWord ++ tailWord_937316) baseStart_937316 baseEnd_937316 := by
    simpa [prefixWord, tailWord_937316, baseEnd_937316] using wordTrace_append hprefix tailTrace_937316
  have hstable : (prefixWord ++ tailWord_937316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937316).length < 2 ^ (prefixWord ++ tailWord_937316).sum := by decide
  have hdescent : baseEnd_937316 < baseStart_937316 := by decide
  rcases family_descends (prefixWord ++ tailWord_937316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937322 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_937322 : Nat := 118140960795 + 937322 * 2 ^ 59
def prefixEnd_937322 : Nat := 4983230072969 + 3 ^ 40 * 937322 * 2
def baseEnd_937322 : Nat := 427819301363277295168303

theorem tailTrace_937322 : CollatzResearch.WordTrace tailWord_937322 prefixEnd_937322 427819301363277295168303 := by
  unfold tailWord_937322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8546735477562487674485555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22791294606833300465294813 8546735477562487674485555)
  ·
    refine ⟨12820103216343731511728333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8546735477562487674485555 12820103216343731511728333)
    ·
      refine ⟨4807538706128899316898125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12820103216343731511728333 4807538706128899316898125)
      ·
        refine ⟨1802827014798337243836797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4807538706128899316898125 1802827014798337243836797)
        ·
          refine ⟨676060130549376466438799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1802827014798337243836797 676060130549376466438799)
          ·
            refine ⟨1014090195824064699658199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676060130549376466438799 1014090195824064699658199)
            ·
              refine ⟨1521135293736097049487299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014090195824064699658199 1521135293736097049487299)
              ·
                refine ⟨2281702940604145574230949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521135293736097049487299 2281702940604145574230949)
                ·
                  refine ⟨427819301363277295168303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281702940604145574230949 427819301363277295168303)
                  ·
                    rfl

theorem cell20_937322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_937322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937322 prefixEnd_937322 := by exact prefixLift 937322
  have htrace : WordTrace (prefixWord ++ tailWord_937322) baseStart_937322 baseEnd_937322 := by
    simpa [prefixWord, tailWord_937322, baseEnd_937322] using wordTrace_append hprefix tailTrace_937322
  have hstable : (prefixWord ++ tailWord_937322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937322).length < 2 ^ (prefixWord ++ tailWord_937322).sum := by decide
  have hdescent : baseEnd_937322 < baseStart_937322 := by decide
  rcases family_descends (prefixWord ++ tailWord_937322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937340 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_937340 : Nat := 118140960795 + 937340 * 2 ^ 59
def prefixEnd_937340 : Nat := 4983230072969 + 3 ^ 40 * 937340 * 2
def baseEnd_937340 : Nat := 427827517053749232568229

theorem tailTrace_937340 : CollatzResearch.WordTrace tailWord_937340 prefixEnd_937340 427827517053749232568229 := by
  unfold tailWord_937340
  simp only [CollatzResearch.WordTrace]
  refine ⟨17093799212092369886048737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22791732282789826514731649 17093799212092369886048737)
  ·
    refine ⟨12820349409069277414536553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17093799212092369886048737 12820349409069277414536553)
    ·
      refine ⟨9615262056801958060902415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12820349409069277414536553 9615262056801958060902415)
      ·
        refine ⟨14422893085202937091353623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9615262056801958060902415 14422893085202937091353623)
        ·
          refine ⟨21634339627804405637030435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14422893085202937091353623 21634339627804405637030435)
          ·
            refine ⟨32451509441706608455545653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21634339627804405637030435 32451509441706608455545653)
            ·
              refine ⟨3042329010159994542707405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32451509441706608455545653 3042329010159994542707405)
              ·
                refine ⟨1140873378809997953515277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3042329010159994542707405 1140873378809997953515277)
                ·
                  refine ⟨427827517053749232568229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140873378809997953515277 427827517053749232568229)
                  ·
                    rfl

theorem cell20_937340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_937340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937340 prefixEnd_937340 := by exact prefixLift 937340
  have htrace : WordTrace (prefixWord ++ tailWord_937340) baseStart_937340 baseEnd_937340 := by
    simpa [prefixWord, tailWord_937340, baseEnd_937340] using wordTrace_append hprefix tailTrace_937340
  have hstable : (prefixWord ++ tailWord_937340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937340).length < 2 ^ (prefixWord ++ tailWord_937340).sum := by decide
  have hdescent : baseEnd_937340 < baseStart_937340 := by decide
  rcases family_descends (prefixWord ++ tailWord_937340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937433 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 3]
def baseStart_937433 : Nat := 118140960795 + 937433 * 2 ^ 59
def prefixEnd_937433 : Nat := 4983230072969 + 3 ^ 40 * 937433 * 2
def baseEnd_937433 : Nat := 427869964787854242467849

theorem tailTrace_937433 : CollatzResearch.WordTrace tailWord_937433 prefixEnd_937433 427869964787854242467849 := by
  unfold tailWord_937433
  simp only [CollatzResearch.WordTrace]
  refine ⟨34190990412847816655232953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22793993608565211103488635 34190990412847816655232953)
  ·
    refine ⟨25643242809635862491424715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34190990412847816655232953 25643242809635862491424715)
    ·
      refine ⟨38464864214453793737137073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25643242809635862491424715 38464864214453793737137073)
      ·
        refine ⟨28848648160840345302852805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38464864214453793737137073 28848648160840345302852805)
        ·
          refine ⟨5409121530157564744284901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28848648160840345302852805 5409121530157564744284901)
          ·
            refine ⟨1014210286904543389553419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5409121530157564744284901 1014210286904543389553419)
            ·
              refine ⟨1521315430356815084330129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014210286904543389553419 1521315430356815084330129)
              ·
                refine ⟨1140986572767611313247597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521315430356815084330129 1140986572767611313247597)
                ·
                  refine ⟨427869964787854242467849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140986572767611313247597 427869964787854242467849)
                  ·
                    rfl

theorem cell20_937433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_937433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937433 prefixEnd_937433 := by exact prefixLift 937433
  have htrace : WordTrace (prefixWord ++ tailWord_937433) baseStart_937433 baseEnd_937433 := by
    simpa [prefixWord, tailWord_937433, baseEnd_937433] using wordTrace_append hprefix tailTrace_937433
  have hstable : (prefixWord ++ tailWord_937433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937433).length < 2 ^ (prefixWord ++ tailWord_937433).sum := by decide
  have hdescent : baseEnd_937433 < baseStart_937433 := by decide
  rcases family_descends (prefixWord ++ tailWord_937433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937450 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_937450 : Nat := 118140960795 + 937450 * 2 ^ 59
def prefixEnd_937450 : Nat := 4983230072969 + 3 ^ 40 * 937450 * 2
def baseEnd_937450 : Nat := 427877724051077738901113

theorem tailTrace_937450 : CollatzResearch.WordTrace tailWord_937450 prefixEnd_937450 427877724051077738901113 := by
  unfold tailWord_937450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547902613446557139650451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22794406969190819039067869 8547902613446557139650451)
  ·
    refine ⟨12821853920169835709475677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8547902613446557139650451 12821853920169835709475677)
    ·
      refine ⟨4808195220063688391053379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12821853920169835709475677 4808195220063688391053379)
      ·
        refine ⟨7212292830095532586580069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808195220063688391053379 7212292830095532586580069)
        ·
          refine ⟨1352304905642912359983763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7212292830095532586580069 1352304905642912359983763)
          ·
            refine ⟨2028457358464368539975645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352304905642912359983763 2028457358464368539975645)
            ·
              refine ⟨760671509424138202490867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2028457358464368539975645 760671509424138202490867)
              ·
                refine ⟨1141007264136207303736301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760671509424138202490867 1141007264136207303736301)
                ·
                  refine ⟨427877724051077738901113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141007264136207303736301 427877724051077738901113)
                  ·
                    rfl

theorem cell20_937450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_937450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937450 prefixEnd_937450 := by exact prefixLift 937450
  have htrace : WordTrace (prefixWord ++ tailWord_937450) baseStart_937450 baseEnd_937450 := by
    simpa [prefixWord, tailWord_937450, baseEnd_937450] using wordTrace_append hprefix tailTrace_937450
  have hstable : (prefixWord ++ tailWord_937450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937450).length < 2 ^ (prefixWord ++ tailWord_937450).sum := by decide
  have hdescent : baseEnd_937450 < baseStart_937450 := by decide
  rcases family_descends (prefixWord ++ tailWord_937450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937470 : List Nat := [4, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_937470 : Nat := 118140960795 + 937470 * 2 ^ 59
def prefixEnd_937470 : Nat := 4983230072969 + 3 ^ 40 * 937470 * 2
def baseEnd_937470 : Nat := 427886852596046558234365

theorem tailTrace_937470 : CollatzResearch.WordTrace tailWord_937470 prefixEnd_937470 427886852596046558234365 := by
  unfold tailWord_937470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4274042489214221496791233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22794893275809181316219909 4274042489214221496791233)
  ·
    refine ⟨3205531866910666122593425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4274042489214221496791233 3205531866910666122593425)
    ·
      refine ⟨2404148900182999591945069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3205531866910666122593425 2404148900182999591945069)
      ·
        refine ⟨901555837568624846979401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2404148900182999591945069 901555837568624846979401)
        ·
          refine ⟨676166878176468635234551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901555837568624846979401 676166878176468635234551)
          ·
            refine ⟨1014250317264702952851827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676166878176468635234551 1014250317264702952851827)
            ·
              refine ⟨1521375475897054429277741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014250317264702952851827 1521375475897054429277741)
              ·
                refine ⟨570515803461395410979153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1521375475897054429277741 570515803461395410979153)
                ·
                  refine ⟨427886852596046558234365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570515803461395410979153 427886852596046558234365)
                  ·
                    rfl

theorem cell20_937470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_937470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937470 prefixEnd_937470 := by exact prefixLift 937470
  have htrace : WordTrace (prefixWord ++ tailWord_937470) baseStart_937470 baseEnd_937470 := by
    simpa [prefixWord, tailWord_937470, baseEnd_937470] using wordTrace_append hprefix tailTrace_937470
  have hstable : (prefixWord ++ tailWord_937470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937470).length < 2 ^ (prefixWord ++ tailWord_937470).sum := by decide
  have hdescent : baseEnd_937470 < baseStart_937470 := by decide
  rcases family_descends (prefixWord ++ tailWord_937470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937474 : List Nat := [3, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_937474 : Nat := 118140960795 + 937474 * 2 ^ 59
def prefixEnd_937474 : Nat := 4983230072969 + 3 ^ 40 * 937474 * 2
def baseEnd_937474 : Nat := 427888678305040322101015

theorem tailTrace_937474 : CollatzResearch.WordTrace tailWord_937474 prefixEnd_937474 427888678305040322101015 := by
  unfold tailWord_937474
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548121451424820164368869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22794990537132853771650317 8548121451424820164368869)
  ·
    refine ⟨1602772772142153780819163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8548121451424820164368869 1602772772142153780819163)
    ·
      refine ⟨2404159158213230671228745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602772772142153780819163 2404159158213230671228745)
      ·
        refine ⟨1803119368659923003421559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2404159158213230671228745 1803119368659923003421559)
        ·
          refine ⟨2704679052989884505132339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803119368659923003421559 2704679052989884505132339)
          ·
            refine ⟨4057018579484826757698509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704679052989884505132339 4057018579484826757698509)
            ·
              refine ⟨1521381967306810034136941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4057018579484826757698509 1521381967306810034136941)
              ·
                refine ⟨570518237740053762801353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1521381967306810034136941 570518237740053762801353)
                ·
                  refine ⟨427888678305040322101015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570518237740053762801353 427888678305040322101015)
                  ·
                    rfl

theorem cell20_937474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_937474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937474 prefixEnd_937474 := by exact prefixLift 937474
  have htrace : WordTrace (prefixWord ++ tailWord_937474) baseStart_937474 baseEnd_937474 := by
    simpa [prefixWord, tailWord_937474, baseEnd_937474] using wordTrace_append hprefix tailTrace_937474
  have hstable : (prefixWord ++ tailWord_937474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937474).length < 2 ^ (prefixWord ++ tailWord_937474).sum := by decide
  have hdescent : baseEnd_937474 < baseStart_937474 := by decide
  rcases family_descends (prefixWord ++ tailWord_937474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937506 : List Nat := [3, 3, 1, 1, 1, 1, 3, 7]
def baseStart_937506 : Nat := 118140960795 + 937506 * 2 ^ 59
def prefixEnd_937506 : Nat := 4983230072969 + 3 ^ 40 * 937506 * 2
def baseEnd_937506 : Nat := 142634427992330144344739

theorem tailTrace_937506 : CollatzResearch.WordTrace tailWord_937506 prefixEnd_937506 142634427992330144344739 := by
  unfold tailWord_937506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548413235395837530660093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22795768627722233415093581 8548413235395837530660093)
  ·
    refine ⟨3205654963273439073997535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8548413235395837530660093 3205654963273439073997535)
    ·
      refine ⟨4808482444910158610996303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205654963273439073997535 4808482444910158610996303)
      ·
        refine ⟨7212723667365237916494455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808482444910158610996303 7212723667365237916494455)
        ·
          refine ⟨10819085501047856874741683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212723667365237916494455 10819085501047856874741683)
          ·
            refine ⟨16228628251571785312112525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819085501047856874741683 16228628251571785312112525)
            ·
              refine ⟨6085735594339419492042197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16228628251571785312112525 6085735594339419492042197)
              ·
                refine ⟨142634427992330144344739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6085735594339419492042197 142634427992330144344739)
                ·
                  rfl

theorem cell20_937506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_937506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937506 prefixEnd_937506 := by exact prefixLift 937506
  have htrace : WordTrace (prefixWord ++ tailWord_937506) baseStart_937506 baseEnd_937506 := by
    simpa [prefixWord, tailWord_937506, baseEnd_937506] using wordTrace_append hprefix tailTrace_937506
  have hstable : (prefixWord ++ tailWord_937506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937506).length < 2 ^ (prefixWord ++ tailWord_937506).sum := by decide
  have hdescent : baseEnd_937506 < baseStart_937506 := by decide
  rcases family_descends (prefixWord ++ tailWord_937506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
