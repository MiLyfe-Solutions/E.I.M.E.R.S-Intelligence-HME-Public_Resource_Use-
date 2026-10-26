import V185TrunkScan22Chunk391

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3497045 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3497045 : Nat := 118140960795 + 3497045 * 2 ^ 59
def prefixEnd_3497045 : Nat := 4983230072969 + 3 ^ 40 * 3497045 * 2
def baseEnd_3497045 : Nat := 1197109970268250352703259

theorem tailTrace_3497045 : CollatzResearch.WordTrace tailWord_3497045 prefixEnd_3497045 1197109970268250352703259 := by
  unfold tailWord_3497045
  simp only [CollatzResearch.WordTrace]
  refine ⟨127547709615810687581788589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85031806410540458387859059 127547709615810687581788589)
  ·
    refine ⟨47830391105929007843170721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127547709615810687581788589 47830391105929007843170721)
    ·
      refine ⟨35872793329446755882378041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47830391105929007843170721 35872793329446755882378041)
      ·
        refine ⟨26904594997085066911783531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35872793329446755882378041 26904594997085066911783531)
        ·
          refine ⟨40356892495627600367675297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26904594997085066911783531 40356892495627600367675297)
          ·
            refine ⟨30267669371720700275756473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40356892495627600367675297 30267669371720700275756473)
            ·
              refine ⟨22700752028790525206817355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30267669371720700275756473 22700752028790525206817355)
              ·
                refine ⟨34051128043185787810226033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22700752028790525206817355 34051128043185787810226033)
                ·
                  refine ⟨25538346032389340857669525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34051128043185787810226033 25538346032389340857669525)
                  ·
                    refine ⟨1197109970268250352703259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25538346032389340857669525 1197109970268250352703259)
                    ·
                      rfl

theorem cell22_3497045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3497045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497045 prefixEnd_3497045 := by exact prefixLift 3497045
  have htrace : WordTrace (prefixWord ++ tailWord_3497045) baseStart_3497045 baseEnd_3497045 := by
    simpa [prefixWord, tailWord_3497045, baseEnd_3497045] using wordTrace_append hprefix tailTrace_3497045
  have hstable : (prefixWord ++ tailWord_3497045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497045).length < 2 ^ (prefixWord ++ tailWord_3497045).sum := by decide
  have hdescent : baseEnd_3497045 < baseStart_3497045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497184 : List Nat := [2, 1, 1, 3, 1, 6, 2, 6]
def baseStart_3497184 : Nat := 118140960795 + 3497184 * 2 ^ 59
def prefixEnd_3497184 : Nat := 4983230072969 + 3 ^ 40 * 3497184 * 2
def baseEnd_3497184 : Nat := 133017505867655591497537

theorem tailTrace_3497184 : CollatzResearch.WordTrace tailWord_3497184 prefixEnd_3497184 133017505867655591497537 := by
  unfold tailWord_3497184
  simp only [CollatzResearch.WordTrace]
  refine ⟨63776389681153557160549303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85035186241538076214065737 63776389681153557160549303)
  ·
    refine ⟨95664584521730335740823955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63776389681153557160549303 95664584521730335740823955)
    ·
      refine ⟨143496876782595503611235933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95664584521730335740823955 143496876782595503611235933)
      ·
        refine ⟨53811328793473313854213475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143496876782595503611235933 53811328793473313854213475)
        ·
          refine ⟨80716993190209970781320213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53811328793473313854213475 80716993190209970781320213)
          ·
            refine ⟨3783609055791092380374385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80716993190209970781320213 3783609055791092380374385)
            ·
              refine ⟨2837706791843319285280789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3783609055791092380374385 2837706791843319285280789)
              ·
                refine ⟨133017505867655591497537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2837706791843319285280789 133017505867655591497537)
                ·
                  rfl

theorem cell22_3497184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 6].length) (baseStart_3497184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497184 prefixEnd_3497184 := by exact prefixLift 3497184
  have htrace : WordTrace (prefixWord ++ tailWord_3497184) baseStart_3497184 baseEnd_3497184 := by
    simpa [prefixWord, tailWord_3497184, baseEnd_3497184] using wordTrace_append hprefix tailTrace_3497184
  have hstable : (prefixWord ++ tailWord_3497184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497184).length < 2 ^ (prefixWord ++ tailWord_3497184).sum := by decide
  have hdescent : baseEnd_3497184 < baseStart_3497184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497272 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_3497272 : Nat := 118140960795 + 3497272 * 2 ^ 59
def prefixEnd_3497272 : Nat := 4983230072969 + 3 ^ 40 * 3497272 * 2
def baseEnd_3497272 : Nat := 1197187677007297427277563

theorem tailTrace_3497272 : CollatzResearch.WordTrace tailWord_3497272 prefixEnd_3497272 1197187677007297427277563 := by
  unfold tailWord_3497272
  simp only [CollatzResearch.WordTrace]
  refine ⟨63777994492994152675151035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85037325990658870233534713 63777994492994152675151035)
  ·
    refine ⟨95666991739491229012726553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63777994492994152675151035 95666991739491229012726553)
    ·
      refine ⟨71750243804618421759544915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95666991739491229012726553 71750243804618421759544915)
      ·
        refine ⟨107625365706927632639317373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71750243804618421759544915 107625365706927632639317373)
        ·
          refine ⟨40359512140097862239744015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107625365706927632639317373 40359512140097862239744015)
          ·
            refine ⟨60539268210146793359616023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40359512140097862239744015 60539268210146793359616023)
            ·
              refine ⟨90808902315220190039424035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60539268210146793359616023 90808902315220190039424035)
              ·
                refine ⟨136213353472830285059136053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90808902315220190039424035 136213353472830285059136053)
                ·
                  refine ⟨12770001888077839224294005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136213353472830285059136053 12770001888077839224294005)
                  ·
                    refine ⟨1197187677007297427277563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12770001888077839224294005 1197187677007297427277563)
                    ·
                      rfl

theorem cell22_3497272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_3497272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497272 prefixEnd_3497272 := by exact prefixLift 3497272
  have htrace : WordTrace (prefixWord ++ tailWord_3497272) baseStart_3497272 baseEnd_3497272 := by
    simpa [prefixWord, tailWord_3497272, baseEnd_3497272] using wordTrace_append hprefix tailTrace_3497272
  have hstable : (prefixWord ++ tailWord_3497272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497272).length < 2 ^ (prefixWord ++ tailWord_3497272).sum := by decide
  have hdescent : baseEnd_3497272 < baseStart_3497272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497319 : List Nat := [1, 1, 5, 1, 4, 1, 9]
def baseStart_3497319 : Nat := 118140960795 + 3497319 * 2 ^ 59
def prefixEnd_3497319 : Nat := 4983230072969 + 3 ^ 40 * 3497319 * 2
def baseEnd_3497319 : Nat := 44340880224733517457497

theorem tailTrace_3497319 : CollatzResearch.WordTrace tailWord_3497319 prefixEnd_3497319 44340880224733517457497 := by
  unfold tailWord_3497319
  simp only [CollatzResearch.WordTrace]
  refine ⟨127557703216818032377263011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85038468811212021584842007 127557703216818032377263011)
  ·
    refine ⟨191336554825227048565894517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127557703216818032377263011 191336554825227048565894517)
    ·
      refine ⟨17937802014865035803052611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191336554825227048565894517 17937802014865035803052611)
      ·
        refine ⟨26906703022297553704578917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17937802014865035803052611 26906703022297553704578917)
        ·
          refine ⟨5045006816680791319608547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26906703022297553704578917 5045006816680791319608547)
          ·
            refine ⟨7567510225021186979412821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045006816680791319608547 7567510225021186979412821)
            ·
              refine ⟨44340880224733517457497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7567510225021186979412821 44340880224733517457497)
              ·
                rfl

theorem cell22_3497319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 9].length) (baseStart_3497319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497319 prefixEnd_3497319 := by exact prefixLift 3497319
  have htrace : WordTrace (prefixWord ++ tailWord_3497319) baseStart_3497319 baseEnd_3497319 := by
    simpa [prefixWord, tailWord_3497319, baseEnd_3497319] using wordTrace_append hprefix tailTrace_3497319
  have hstable : (prefixWord ++ tailWord_3497319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497319).length < 2 ^ (prefixWord ++ tailWord_3497319).sum := by decide
  have hdescent : baseEnd_3497319 < baseStart_3497319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497351 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 3, 3]
def baseStart_3497351 : Nat := 118140960795 + 3497351 * 2 ^ 59
def prefixEnd_3497351 : Nat := 4983230072969 + 3 ^ 40 * 3497351 * 2
def baseEnd_3497351 : Nat := 1197214720321767554552321

theorem tailTrace_3497351 : CollatzResearch.WordTrace tailWord_3497351 prefixEnd_3497351 1197214720321767554552321 := by
  unfold tailWord_3497351
  simp only [CollatzResearch.WordTrace]
  refine ⟨127558870352702101842427907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85039246901801401228285271 127558870352702101842427907)
  ·
    refine ⟨191338305529053152763641861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127558870352702101842427907 191338305529053152763641861)
    ·
      refine ⟨35875932286697466143182849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191338305529053152763641861 35875932286697466143182849)
      ·
        refine ⟨26906949215023099607387137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35875932286697466143182849 26906949215023099607387137)
        ·
          refine ⟨20180211911267324705540353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26906949215023099607387137 20180211911267324705540353)
          ·
            refine ⟨15135158933450493529155265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20180211911267324705540353 15135158933450493529155265)
            ·
              refine ⟨11351369200087870146866449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15135158933450493529155265 11351369200087870146866449)
              ·
                refine ⟨8513526900065902610149837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11351369200087870146866449 8513526900065902610149837)
                ·
                  refine ⟨3192572587524713478806189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8513526900065902610149837 3192572587524713478806189)
                  ·
                    refine ⟨1197214720321767554552321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3192572587524713478806189 1197214720321767554552321)
                    ·
                      rfl

theorem cell22_3497351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_3497351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497351 prefixEnd_3497351 := by exact prefixLift 3497351
  have htrace : WordTrace (prefixWord ++ tailWord_3497351) baseStart_3497351 baseEnd_3497351 := by
    simpa [prefixWord, tailWord_3497351, baseEnd_3497351] using wordTrace_append hprefix tailTrace_3497351
  have hstable : (prefixWord ++ tailWord_3497351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497351).length < 2 ^ (prefixWord ++ tailWord_3497351).sum := by decide
  have hdescent : baseEnd_3497351 < baseStart_3497351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497353 : List Nat := [1, 2, 1, 1, 8, 1, 2, 6]
def baseStart_3497353 : Nat := 118140960795 + 3497353 * 2 ^ 59
def prefixEnd_3497353 : Nat := 4983230072969 + 3 ^ 40 * 3497353 * 2
def baseEnd_3497353 : Nat := 133023933884737801778035

theorem tailTrace_3497353 : CollatzResearch.WordTrace tailWord_3497353 prefixEnd_3497353 133023933884737801778035 := by
  unfold tailWord_3497353
  simp only [CollatzResearch.WordTrace]
  refine ⟨127558943298694856184000713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85039295532463237456000475 127558943298694856184000713)
  ·
    refine ⟨95669207474021142138000535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127558943298694856184000713 95669207474021142138000535)
    ·
      refine ⟨143503811211031713207000803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95669207474021142138000535 143503811211031713207000803)
      ·
        refine ⟨215255716816547569810501205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143503811211031713207000803 215255716816547569810501205)
        ·
          refine ⟨2522527931443916833716811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 215255716816547569810501205 2522527931443916833716811)
          ·
            refine ⟨3783791897165875250575217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522527931443916833716811 3783791897165875250575217)
            ·
              refine ⟨2837843922874406437931413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3783791897165875250575217 2837843922874406437931413)
              ·
                refine ⟨133023933884737801778035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2837843922874406437931413 133023933884737801778035)
                ·
                  rfl

theorem cell22_3497353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 6].length) (baseStart_3497353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497353 prefixEnd_3497353 := by exact prefixLift 3497353
  have htrace : WordTrace (prefixWord ++ tailWord_3497353) baseStart_3497353 baseEnd_3497353 := by
    simpa [prefixWord, tailWord_3497353, baseEnd_3497353] using wordTrace_append hprefix tailTrace_3497353
  have hstable : (prefixWord ++ tailWord_3497353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497353).length < 2 ^ (prefixWord ++ tailWord_3497353).sum := by decide
  have hdescent : baseEnd_3497353 < baseStart_3497353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497411 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 1, 4]
def baseStart_3497411 : Nat := 118140960795 + 3497411 * 2 ^ 59
def prefixEnd_3497411 : Nat := 4983230072969 + 3 ^ 40 * 3497411 * 2
def baseEnd_3497411 : Nat := 1197235259547947398052137

theorem tailTrace_3497411 : CollatzResearch.WordTrace tailWord_3497411 prefixEnd_3497411 1197235259547947398052137 := by
  unfold tailWord_3497411
  simp only [CollatzResearch.WordTrace]
  refine ⟨127561058732484732089612087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85040705821656488059741391 127561058732484732089612087)
  ·
    refine ⟨191341588098727098134418131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127561058732484732089612087 191341588098727098134418131)
    ·
      refine ⟨287012382148090647201627197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191341588098727098134418131 287012382148090647201627197)
      ·
        refine ⟨107629643305533992700610199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287012382148090647201627197 107629643305533992700610199)
        ·
          refine ⟨161444464958300989050915299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107629643305533992700610199 161444464958300989050915299)
          ·
            refine ⟨242166697437451483576372949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161444464958300989050915299 242166697437451483576372949)
            ·
              refine ⟨5675781971190269146321241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 242166697437451483576372949 5675781971190269146321241)
              ·
                refine ⟨4256836478392701859740931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5675781971190269146321241 4256836478392701859740931)
                ·
                  refine ⟨6385254717589052789611397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256836478392701859740931 6385254717589052789611397)
                  ·
                    refine ⟨1197235259547947398052137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6385254717589052789611397 1197235259547947398052137)
                    ·
                      rfl

theorem cell22_3497411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 4].length) (baseStart_3497411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497411 prefixEnd_3497411 := by exact prefixLift 3497411
  have htrace : WordTrace (prefixWord ++ tailWord_3497411) baseStart_3497411 baseEnd_3497411 := by
    simpa [prefixWord, tailWord_3497411, baseEnd_3497411] using wordTrace_append hprefix tailTrace_3497411
  have hstable : (prefixWord ++ tailWord_3497411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497411).length < 2 ^ (prefixWord ++ tailWord_3497411).sum := by decide
  have hdescent : baseEnd_3497411 < baseStart_3497411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497424 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_3497424 : Nat := 118140960795 + 3497424 * 2 ^ 59
def prefixEnd_3497424 : Nat := 4983230072969 + 3 ^ 40 * 3497424 * 2
def baseEnd_3497424 : Nat := 1197239709713619697477097

theorem tailTrace_3497424 : CollatzResearch.WordTrace tailWord_3497424 prefixEnd_3497424 1197239709713619697477097 := by
  unfold tailWord_3497424
  simp only [CollatzResearch.WordTrace]
  refine ⟨63780766440718817654917663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85041021920958423539890217 63780766440718817654917663)
  ·
    refine ⟨95671149661078226482376495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63780766440718817654917663 95671149661078226482376495)
    ·
      refine ⟨143506724491617339723564743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95671149661078226482376495 143506724491617339723564743)
      ·
        refine ⟨215260086737426009585347115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143506724491617339723564743 215260086737426009585347115)
        ·
          refine ⟨322890130106139014378020673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215260086737426009585347115 322890130106139014378020673)
          ·
            refine ⟨242167597579604260783515505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322890130106139014378020673 242167597579604260783515505)
            ·
              refine ⟨181625698184703195587636629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242167597579604260783515505 181625698184703195587636629)
              ·
                refine ⟨8513704602407962293170467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181625698184703195587636629 8513704602407962293170467)
                ·
                  refine ⟨12770556903611943439755701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8513704602407962293170467 12770556903611943439755701)
                  ·
                    refine ⟨1197239709713619697477097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12770556903611943439755701 1197239709713619697477097)
                    ·
                      rfl

theorem cell22_3497424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_3497424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497424 prefixEnd_3497424 := by exact prefixLift 3497424
  have htrace : WordTrace (prefixWord ++ tailWord_3497424) baseStart_3497424 baseEnd_3497424 := by
    simpa [prefixWord, tailWord_3497424, baseEnd_3497424] using wordTrace_append hprefix tailTrace_3497424
  have hstable : (prefixWord ++ tailWord_3497424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497424).length < 2 ^ (prefixWord ++ tailWord_3497424).sum := by decide
  have hdescent : baseEnd_3497424 < baseStart_3497424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497443 : List Nat := [1, 1, 1, 6, 2, 2, 1, 4, 4]
def baseStart_3497443 : Nat := 118140960795 + 3497443 * 2 ^ 59
def prefixEnd_3497443 : Nat := 4983230072969 + 3 ^ 40 * 3497443 * 2
def baseEnd_3497443 : Nat := 399082071267303327084013

theorem tailTrace_3497443 : CollatzResearch.WordTrace tailWord_3497443 prefixEnd_3497443 399082071267303327084013 := by
  unfold tailWord_3497443
  simp only [CollatzResearch.WordTrace]
  refine ⟨127562225868368801554776983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85041483912245867703184655 127562225868368801554776983)
  ·
    refine ⟨191343338802553202332165475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127562225868368801554776983 191343338802553202332165475)
    ·
      refine ⟨287015008203829803498248213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191343338802553202332165475 287015008203829803498248213)
      ·
        refine ⟨13453828509554522038980385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 287015008203829803498248213 13453828509554522038980385)
        ·
          refine ⟨10090371382165891529235289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13453828509554522038980385 10090371382165891529235289)
          ·
            refine ⟨7567778536624418646926467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10090371382165891529235289 7567778536624418646926467)
            ·
              refine ⟨11351667804936627970389701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7567778536624418646926467 11351667804936627970389701)
              ·
                refine ⟨2128437713425617744448069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11351667804936627970389701 2128437713425617744448069)
                ·
                  refine ⟨399082071267303327084013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128437713425617744448069 399082071267303327084013)
                  ·
                    rfl

theorem cell22_3497443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 4].length) (baseStart_3497443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497443 prefixEnd_3497443 := by exact prefixLift 3497443
  have htrace : WordTrace (prefixWord ++ tailWord_3497443) baseStart_3497443 baseEnd_3497443 := by
    simpa [prefixWord, tailWord_3497443, baseEnd_3497443] using wordTrace_append hprefix tailTrace_3497443
  have hstable : (prefixWord ++ tailWord_3497443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497443).length < 2 ^ (prefixWord ++ tailWord_3497443).sum := by decide
  have hdescent : baseEnd_3497443 < baseStart_3497443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497458 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_3497458 : Nat := 118140960795 + 3497458 * 2 ^ 59
def prefixEnd_3497458 : Nat := 4983230072969 + 3 ^ 40 * 3497458 * 2
def baseEnd_3497458 : Nat := 1197251348608454942126993

theorem tailTrace_3497458 : CollatzResearch.WordTrace tailWord_3497458 prefixEnd_3497458 1197251348608454942126993 := by
  unfold tailWord_3497458
  simp only [CollatzResearch.WordTrace]
  refine ⟨31890693240828614779143257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85041848642209639411048685 31890693240828614779143257)
  ·
    refine ⟨23918019930621461084357443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31890693240828614779143257 23918019930621461084357443)
    ·
      refine ⟨35877029895932191626536165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23918019930621461084357443 35877029895932191626536165)
      ·
        refine ⟨6726943105487285929975531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35877029895932191626536165 6726943105487285929975531)
        ·
          refine ⟨10090414658230928894963297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6726943105487285929975531 10090414658230928894963297)
          ·
            refine ⟨7567810993673196671222473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10090414658230928894963297 7567810993673196671222473)
            ·
              refine ⟨5675858245254897503416855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7567810993673196671222473 5675858245254897503416855)
              ·
                refine ⟨8513787367882346255125283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5675858245254897503416855 8513787367882346255125283)
                ·
                  refine ⟨12770681051823519382687925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8513787367882346255125283 12770681051823519382687925)
                  ·
                    refine ⟨1197251348608454942126993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12770681051823519382687925 1197251348608454942126993)
                    ·
                      rfl

theorem cell22_3497458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_3497458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497458 prefixEnd_3497458 := by exact prefixLift 3497458
  have htrace : WordTrace (prefixWord ++ tailWord_3497458) baseStart_3497458 baseEnd_3497458 := by
    simpa [prefixWord, tailWord_3497458, baseEnd_3497458] using wordTrace_append hprefix tailTrace_3497458
  have hstable : (prefixWord ++ tailWord_3497458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497458).length < 2 ^ (prefixWord ++ tailWord_3497458).sum := by decide
  have hdescent : baseEnd_3497458 < baseStart_3497458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497606 : List Nat := [6, 16]
def baseStart_3497606 : Nat := 118140960795 + 3497606 * 2 ^ 59
def prefixEnd_3497606 : Nat := 4983230072969 + 3 ^ 40 * 3497606 * 2
def baseEnd_3497606 : Nat := 182487732362906857099

theorem tailTrace_3497606 : CollatzResearch.WordTrace tailWord_3497606 prefixEnd_3497606 182487732362906857099 := by
  unfold tailWord_3497606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986505342711821262280021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85045447311185520261973781 3986505342711821262280021)
  ·
    refine ⟨182487732362906857099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 16 3986505342711821262280021 182487732362906857099)
    ·
      rfl

theorem cell22_3497606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 16].length) (baseStart_3497606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497606 prefixEnd_3497606 := by exact prefixLift 3497606
  have htrace : WordTrace (prefixWord ++ tailWord_3497606) baseStart_3497606 baseEnd_3497606 := by
    simpa [prefixWord, tailWord_3497606, baseEnd_3497606] using wordTrace_append hprefix tailTrace_3497606
  have hstable : (prefixWord ++ tailWord_3497606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497606).length < 2 ^ (prefixWord ++ tailWord_3497606).sum := by decide
  have hdescent : baseEnd_3497606 < baseStart_3497606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497610 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_3497610 : Nat := 118140960795 + 3497610 * 2 ^ 59
def prefixEnd_3497610 : Nat := 4983230072969 + 3 ^ 40 * 3497610 * 2
def baseEnd_3497610 : Nat := 1197303381314777212326527

theorem tailTrace_3497610 : CollatzResearch.WordTrace tailWord_3497610 prefixEnd_3497610 1197303381314777212326527 := by
  unfold tailWord_3497610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31892079214690947269026571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85045544572509192717404189 31892079214690947269026571)
  ·
    refine ⟨47838118822036420903539857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31892079214690947269026571 47838118822036420903539857)
    ·
      refine ⟨35878589116527315677654893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47838118822036420903539857 35878589116527315677654893)
      ·
        refine ⟨13454470918697743379120585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35878589116527315677654893 13454470918697743379120585)
        ·
          refine ⟨10090853189023307534340439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13454470918697743379120585 10090853189023307534340439)
          ·
            refine ⟨15136279783534961301510659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10090853189023307534340439 15136279783534961301510659)
            ·
              refine ⟨22704419675302441952265989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15136279783534961301510659 22704419675302441952265989)
              ·
                refine ⟨4257078689119207866049873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22704419675302441952265989 4257078689119207866049873)
                ·
                  refine ⟨3192809016839405899537405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4257078689119207866049873 3192809016839405899537405)
                  ·
                    refine ⟨1197303381314777212326527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3192809016839405899537405 1197303381314777212326527)
                    ·
                      rfl

theorem cell22_3497610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_3497610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497610 prefixEnd_3497610 := by exact prefixLift 3497610
  have htrace : WordTrace (prefixWord ++ tailWord_3497610) baseStart_3497610 baseEnd_3497610 := by
    simpa [prefixWord, tailWord_3497610, baseEnd_3497610] using wordTrace_append hprefix tailTrace_3497610
  have hstable : (prefixWord ++ tailWord_3497610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497610).length < 2 ^ (prefixWord ++ tailWord_3497610).sum := by decide
  have hdescent : baseEnd_3497610 < baseStart_3497610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497623 : List Nat := [1, 1, 3, 3, 2, 4, 1, 7]
def baseStart_3497623 : Nat := 118140960795 + 3497623 * 2 ^ 59
def prefixEnd_3497623 : Nat := 4983230072969 + 3 ^ 40 * 3497623 * 2
def baseEnd_3497623 : Nat := 133034203497827723527943

theorem tailTrace_3497623 : CollatzResearch.WordTrace tailWord_3497623 prefixEnd_3497623 133034203497827723527943 := by
  unfold tailWord_3497623
  simp only [CollatzResearch.WordTrace]
  refine ⟨127568791007716692296329523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85045860671811128197553015 127568791007716692296329523)
  ·
    refine ⟨191353186511575038444494285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127568791007716692296329523 191353186511575038444494285)
    ·
      refine ⟨71757444941840639416685357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191353186511575038444494285 71757444941840639416685357)
      ·
        refine ⟨26909041853190239781257009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71757444941840639416685357 26909041853190239781257009)
        ·
          refine ⟨20181781389892679835942757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26909041853190239781257009 20181781389892679835942757)
          ·
            refine ⟨3784084010604877469239267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20181781389892679835942757 3784084010604877469239267)
            ·
              refine ⟨5676126015907316203858901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3784084010604877469239267 5676126015907316203858901)
              ·
                refine ⟨133034203497827723527943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5676126015907316203858901 133034203497827723527943)
                ·
                  rfl

theorem cell22_3497623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 7].length) (baseStart_3497623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497623 prefixEnd_3497623 := by exact prefixLift 3497623
  have htrace : WordTrace (prefixWord ++ tailWord_3497623) baseStart_3497623 baseEnd_3497623 := by
    simpa [prefixWord, tailWord_3497623, baseEnd_3497623] using wordTrace_append hprefix tailTrace_3497623
  have hstable : (prefixWord ++ tailWord_3497623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497623).length < 2 ^ (prefixWord ++ tailWord_3497623).sum := by decide
  have hdescent : baseEnd_3497623 < baseStart_3497623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497651 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 7]
def baseStart_3497651 : Nat := 118140960795 + 3497651 * 2 ^ 59
def prefixEnd_3497651 : Nat := 4983230072969 + 3 ^ 40 * 3497651 * 2
def baseEnd_3497651 : Nat := 399105805484222257350467

theorem tailTrace_3497651 : CollatzResearch.WordTrace tailWord_3497651 prefixEnd_3497651 399105805484222257350467 := by
  unfold tailWord_3497651
  simp only [CollatzResearch.WordTrace]
  refine ⟨127569812251615253078348807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85046541501076835385565871 127569812251615253078348807)
  ·
    refine ⟨191354718377422879617523211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127569812251615253078348807 191354718377422879617523211)
    ·
      refine ⟨287032077566134319426284817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191354718377422879617523211 287032077566134319426284817)
      ·
        refine ⟨215274058174600739569713613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287032077566134319426284817 215274058174600739569713613)
        ·
          refine ⟨80727771815475277338642605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215274058174600739569713613 80727771815475277338642605)
          ·
            refine ⟨30272914430803229001990977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80727771815475277338642605 30272914430803229001990977)
            ·
              refine ⟨22704685823102421751493233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30272914430803229001990977 22704685823102421751493233)
              ·
                refine ⟨17028514367326816313619925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22704685823102421751493233 17028514367326816313619925)
                ·
                  refine ⟨399105805484222257350467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17028514367326816313619925 399105805484222257350467)
                  ·
                    rfl

theorem cell22_3497651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 7].length) (baseStart_3497651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497651 prefixEnd_3497651 := by exact prefixLift 3497651
  have htrace : WordTrace (prefixWord ++ tailWord_3497651) baseStart_3497651 baseEnd_3497651 := by
    simpa [prefixWord, tailWord_3497651, baseEnd_3497651] using wordTrace_append hprefix tailTrace_3497651
  have hstable : (prefixWord ++ tailWord_3497651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497651).length < 2 ^ (prefixWord ++ tailWord_3497651).sum := by decide
  have hdescent : baseEnd_3497651 < baseStart_3497651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497668 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 7]
def baseStart_3497668 : Nat := 118140960795 + 3497668 * 2 ^ 59
def prefixEnd_3497668 : Nat := 4983230072969 + 3 ^ 40 * 3497668 * 2
def baseEnd_3497668 : Nat := 399107745300028131458783

theorem tailTrace_3497668 : CollatzResearch.WordTrace tailWord_3497668 prefixEnd_3497668 399107745300028131458783 := by
  unfold tailWord_3497668
  simp only [CollatzResearch.WordTrace]
  refine ⟨63785216146276832490858829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85046954861702443321145105 63785216146276832490858829)
  ·
    refine ⟨23919456054853812184072061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63785216146276832490858829 23919456054853812184072061)
    ·
      refine ⟨8969796020570179569027023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23919456054853812184072061 8969796020570179569027023)
      ·
        refine ⟨13454694030855269353540535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8969796020570179569027023 13454694030855269353540535)
        ·
          refine ⟨20182041046282904030310803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13454694030855269353540535 20182041046282904030310803)
          ·
            refine ⟨30273061569424356045466205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20182041046282904030310803 30273061569424356045466205)
            ·
              refine ⟨11352398088534133517049827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30273061569424356045466205 11352398088534133517049827)
              ·
                refine ⟨17028597132801200275574741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11352398088534133517049827 17028597132801200275574741)
                ·
                  refine ⟨399107745300028131458783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17028597132801200275574741 399107745300028131458783)
                  ·
                    rfl

theorem cell22_3497668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_3497668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497668 prefixEnd_3497668 := by exact prefixLift 3497668
  have htrace : WordTrace (prefixWord ++ tailWord_3497668) baseStart_3497668 baseEnd_3497668 := by
    simpa [prefixWord, tailWord_3497668, baseEnd_3497668] using wordTrace_append hprefix tailTrace_3497668
  have hstable : (prefixWord ++ tailWord_3497668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497668).length < 2 ^ (prefixWord ++ tailWord_3497668).sum := by decide
  have hdescent : baseEnd_3497668 < baseStart_3497668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497760 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_3497760 : Nat := 118140960795 + 3497760 * 2 ^ 59
def prefixEnd_3497760 : Nat := 4983230072969 + 3 ^ 40 * 3497760 * 2
def baseEnd_3497760 : Nat := 1197354729380226821076067

theorem tailTrace_3497760 : CollatzResearch.WordTrace tailWord_3497760 prefixEnd_3497760 1197354729380226821076067 := by
  unfold tailWord_3497760
  simp only [CollatzResearch.WordTrace]
  refine ⟨63786893904110182347033367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85049191872146909796044489 63786893904110182347033367)
  ·
    refine ⟨95680340856165273520550051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63786893904110182347033367 95680340856165273520550051)
    ·
      refine ⟨143520511284247910280825077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95680340856165273520550051 143520511284247910280825077)
      ·
        refine ⟨13455047932898241588827351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143520511284247910280825077 13455047932898241588827351)
        ·
          refine ⟨20182571899347362383241027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13455047932898241588827351 20182571899347362383241027)
          ·
            refine ⟨30273857849021043574861541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20182571899347362383241027 30273857849021043574861541)
            ·
              refine ⟨5676348346691445670286539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30273857849021043574861541 5676348346691445670286539)
              ·
                refine ⟨8514522520037168505429809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5676348346691445670286539 8514522520037168505429809)
                ·
                  refine ⟨6385891890027876379072357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8514522520037168505429809 6385891890027876379072357)
                  ·
                    refine ⟨1197354729380226821076067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6385891890027876379072357 1197354729380226821076067)
                    ·
                      rfl

theorem cell22_3497760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_3497760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497760 prefixEnd_3497760 := by exact prefixLift 3497760
  have htrace : WordTrace (prefixWord ++ tailWord_3497760) baseStart_3497760 baseEnd_3497760 := by
    simpa [prefixWord, tailWord_3497760, baseEnd_3497760] using wordTrace_append hprefix tailTrace_3497760
  have hstable : (prefixWord ++ tailWord_3497760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497760).length < 2 ^ (prefixWord ++ tailWord_3497760).sum := by decide
  have hdescent : baseEnd_3497760 < baseStart_3497760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497781 : List Nat := [1, 3, 3, 1, 5, 1, 2, 2, 4]
def baseStart_3497781 : Nat := 118140960795 + 3497781 * 2 ^ 59
def prefixEnd_3497781 : Nat := 4983230072969 + 3 ^ 40 * 3497781 * 2
def baseEnd_3497781 : Nat := 399120639369796588767001

theorem tailTrace_3497781 : CollatzResearch.WordTrace tailWord_3497781 prefixEnd_3497781 399120639369796588767001 := by
  unfold tailWord_3497781
  simp only [CollatzResearch.WordTrace]
  refine ⟨127574553741144285280581197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85049702494096190187054131 127574553741144285280581197)
  ·
    refine ⟨47840457652929106980217949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127574553741144285280581197 47840457652929106980217949)
    ·
      refine ⟨17940171619848415117581731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47840457652929106980217949 17940171619848415117581731)
      ·
        refine ⟨26910257429772622676372597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17940171619848415117581731 26910257429772622676372597)
        ·
          refine ⟨2522836634041183375909931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26910257429772622676372597 2522836634041183375909931)
          ·
            refine ⟨3784254951061775063864897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522836634041183375909931 3784254951061775063864897)
            ·
              refine ⟨2838191213296331297898673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3784254951061775063864897 2838191213296331297898673)
              ·
                refine ⟨2128643409972248473424005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2838191213296331297898673 2128643409972248473424005)
                ·
                  refine ⟨399120639369796588767001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128643409972248473424005 399120639369796588767001)
                  ·
                    rfl

theorem cell22_3497781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_3497781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497781 prefixEnd_3497781 := by exact prefixLift 3497781
  have htrace : WordTrace (prefixWord ++ tailWord_3497781) baseStart_3497781 baseEnd_3497781 := by
    simpa [prefixWord, tailWord_3497781, baseEnd_3497781] using wordTrace_append hprefix tailTrace_3497781
  have hstable : (prefixWord ++ tailWord_3497781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497781).length < 2 ^ (prefixWord ++ tailWord_3497781).sum := by decide
  have hdescent : baseEnd_3497781 < baseStart_3497781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497788 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_3497788 : Nat := 118140960795 + 3497788 * 2 ^ 59
def prefixEnd_3497788 : Nat := 4983230072969 + 3 ^ 40 * 3497788 * 2
def baseEnd_3497788 : Nat := 1197364314352444081375981

theorem tailTrace_3497788 : CollatzResearch.WordTrace tailWord_3497788 prefixEnd_3497788 1197364314352444081375981 := by
  unfold tailWord_3497788
  simp only [CollatzResearch.WordTrace]
  refine ⟨63787404526059462738043009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85049872701412616984057345 63787404526059462738043009)
  ·
    refine ⟨47840553394544597053532257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63787404526059462738043009 47840553394544597053532257)
    ·
      refine ⟨35880415045908447790149193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47840553394544597053532257 35880415045908447790149193)
      ·
        refine ⟨26910311284431335842611895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35880415045908447790149193 26910311284431335842611895)
        ·
          refine ⟨40365466926647003763917843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26910311284431335842611895 40365466926647003763917843)
          ·
            refine ⟨60548200389970505645876765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40365466926647003763917843 60548200389970505645876765)
            ·
              refine ⟨22705575146238939617203787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60548200389970505645876765 22705575146238939617203787)
              ·
                refine ⟨34058362719358409425805681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22705575146238939617203787 34058362719358409425805681)
                ·
                  refine ⟨25543772039518807069354261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34058362719358409425805681 25543772039518807069354261)
                  ·
                    refine ⟨1197364314352444081375981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25543772039518807069354261 1197364314352444081375981)
                    ·
                      rfl

theorem cell22_3497788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3497788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497788 prefixEnd_3497788 := by exact prefixLift 3497788
  have htrace : WordTrace (prefixWord ++ tailWord_3497788) baseStart_3497788 baseEnd_3497788 := by
    simpa [prefixWord, tailWord_3497788, baseEnd_3497788] using wordTrace_append hprefix tailTrace_3497788
  have hstable : (prefixWord ++ tailWord_3497788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497788).length < 2 ^ (prefixWord ++ tailWord_3497788).sum := by decide
  have hdescent : baseEnd_3497788 < baseStart_3497788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497818 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_3497818 : Nat := 118140960795 + 3497818 * 2 ^ 59
def prefixEnd_3497818 : Nat := 4983230072969 + 3 ^ 40 * 3497818 * 2
def baseEnd_3497818 : Nat := 1197374583965534003125889

theorem tailTrace_3497818 : CollatzResearch.WordTrace tailWord_3497818 prefixEnd_3497818 1197374583965534003125889 := by
  unfold tailWord_3497818
  simp only [CollatzResearch.WordTrace]
  refine ⟨31893975810502560149919527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85050602161340160399785405 31893975810502560149919527)
  ·
    refine ⟨47840963715753840224879291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31893975810502560149919527 47840963715753840224879291)
    ·
      refine ⟨71761445573630760337318937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47840963715753840224879291 71761445573630760337318937)
      ·
        refine ⟨53821084180223070252989203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71761445573630760337318937 53821084180223070252989203)
        ·
          refine ⟨80731626270334605379483805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53821084180223070252989203 80731626270334605379483805)
          ·
            refine ⟨30274359851375477017306427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80731626270334605379483805 30274359851375477017306427)
            ·
              refine ⟨45411539777063215525959641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30274359851375477017306427 45411539777063215525959641)
              ·
                refine ⟨34058654832797411644469731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45411539777063215525959641 34058654832797411644469731)
                ·
                  refine ⟨51087982249196117466704597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34058654832797411644469731 51087982249196117466704597)
                  ·
                    refine ⟨1197374583965534003125889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51087982249196117466704597 1197374583965534003125889)
                    ·
                      rfl

theorem cell22_3497818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_3497818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497818 prefixEnd_3497818 := by exact prefixLift 3497818
  have htrace : WordTrace (prefixWord ++ tailWord_3497818) baseStart_3497818 baseEnd_3497818 := by
    simpa [prefixWord, tailWord_3497818, baseEnd_3497818] using wordTrace_append hprefix tailTrace_3497818
  have hstable : (prefixWord ++ tailWord_3497818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497818).length < 2 ^ (prefixWord ++ tailWord_3497818).sum := by decide
  have hdescent : baseEnd_3497818 < baseStart_3497818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497824 : List Nat := [2, 1, 1, 3, 3, 3, 2, 3, 1, 3]
def baseStart_3497824 : Nat := 118140960795 + 3497824 * 2 ^ 59
def prefixEnd_3497824 : Nat := 4983230072969 + 3 ^ 40 * 3497824 * 2
def baseEnd_3497824 : Nat := 1197376637888151987475871

theorem tailTrace_3497824 : CollatzResearch.WordTrace tailWord_3497824 prefixEnd_3497824 1197376637888151987475871 := by
  unfold tailWord_3497824
  simp only [CollatzResearch.WordTrace]
  refine ⟨63788061039994251812198263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85050748053325669082931017 63788061039994251812198263)
  ·
    refine ⟨95682091559991377718297395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63788061039994251812198263 95682091559991377718297395)
    ·
      refine ⟨143523137339987066577446093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95682091559991377718297395 143523137339987066577446093)
      ·
        refine ⟨53821176502495149966542285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143523137339987066577446093 53821176502495149966542285)
        ·
          refine ⟨20182941188435681237453357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53821176502495149966542285 20182941188435681237453357)
          ·
            refine ⟨7568602945663380464045009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20182941188435681237453357 7568602945663380464045009)
            ·
              refine ⟨5676452209247535348033757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7568602945663380464045009 5676452209247535348033757)
              ·
                refine ⟨2128669578467825755512659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5676452209247535348033757 2128669578467825755512659)
                ·
                  refine ⟨3193004367701738633268989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128669578467825755512659 3193004367701738633268989)
                  ·
                    refine ⟨1197376637888151987475871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193004367701738633268989 1197376637888151987475871)
                    ·
                      rfl

theorem cell22_3497824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 3].length) (baseStart_3497824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3497824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3497824 prefixEnd_3497824 := by exact prefixLift 3497824
  have htrace : WordTrace (prefixWord ++ tailWord_3497824) baseStart_3497824 baseEnd_3497824 := by
    simpa [prefixWord, tailWord_3497824, baseEnd_3497824] using wordTrace_append hprefix tailTrace_3497824
  have hstable : (prefixWord ++ tailWord_3497824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497824).length < 2 ^ (prefixWord ++ tailWord_3497824).sum := by decide
  have hdescent : baseEnd_3497824 < baseStart_3497824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498032 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_3498032 : Nat := 118140960795 + 3498032 * 2 ^ 59
def prefixEnd_3498032 : Nat := 4983230072969 + 3 ^ 40 * 3498032 * 2
def baseEnd_3498032 : Nat := 1197447840538908778275233

theorem tailTrace_3498032 : CollatzResearch.WordTrace tailWord_3498032 prefixEnd_3498032 1197447840538908778275233 := by
  unfold tailWord_3498032
  simp only [CollatzResearch.WordTrace]
  refine ⟨63791854231617477573984175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85055805642156636765312233 63791854231617477573984175)
  ·
    refine ⟨95687781347426216360976263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63791854231617477573984175 95687781347426216360976263)
    ·
      refine ⟨143531672021139324541464395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95687781347426216360976263 143531672021139324541464395)
      ·
        refine ⟨215297508031708986812196593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143531672021139324541464395 215297508031708986812196593)
        ·
          refine ⟨161473131023781740109147445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215297508031708986812196593 161473131023781740109147445)
          ·
            refine ⟨15138106033479538135232573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161473131023781740109147445 15138106033479538135232573)
            ·
              refine ⟨5676789762554826800712215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15138106033479538135232573 5676789762554826800712215)
              ·
                refine ⟨8515184643832240201068323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5676789762554826800712215 8515184643832240201068323)
                ·
                  refine ⟨12772776965748360301602485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8515184643832240201068323 12772776965748360301602485)
                  ·
                    refine ⟨1197447840538908778275233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12772776965748360301602485 1197447840538908778275233)
                    ·
                      rfl

theorem cell22_3498032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_3498032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498032 prefixEnd_3498032 := by exact prefixLift 3498032
  have htrace : WordTrace (prefixWord ++ tailWord_3498032) baseStart_3498032 baseEnd_3498032 := by
    simpa [prefixWord, tailWord_3498032, baseEnd_3498032] using wordTrace_append hprefix tailTrace_3498032
  have hstable : (prefixWord ++ tailWord_3498032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498032).length < 2 ^ (prefixWord ++ tailWord_3498032).sum := by decide
  have hdescent : baseEnd_3498032 < baseStart_3498032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498049 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3498049 : Nat := 118140960795 + 3498049 * 2 ^ 59
def prefixEnd_3498049 : Nat := 4983230072969 + 3 ^ 40 * 3498049 * 2
def baseEnd_3498049 : Nat := 1197453659986326400600181

theorem tailTrace_3498049 : CollatzResearch.WordTrace tailWord_3498049 prefixEnd_3498049 1197453659986326400600181 := by
  unfold tailWord_3498049
  simp only [CollatzResearch.WordTrace]
  refine ⟨127584328504173367051337201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85056219002782244700891467 127584328504173367051337201)
  ·
    refine ⟨95688246378130025288502901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127584328504173367051337201 95688246378130025288502901)
    ·
      refine ⟨8970773097949689870797147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95688246378130025288502901 8970773097949689870797147)
      ·
        refine ⟨13456159646924534806195721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8970773097949689870797147 13456159646924534806195721)
        ·
          refine ⟨10092119735193401104646791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13456159646924534806195721 10092119735193401104646791)
          ·
            refine ⟨15138179602790101656970187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10092119735193401104646791 15138179602790101656970187)
            ·
              refine ⟨22707269404185152485455281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15138179602790101656970187 22707269404185152485455281)
              ·
                refine ⟨17030452053138864364091461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22707269404185152485455281 17030452053138864364091461)
                ·
                  refine ⟨3193209759963537068267149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17030452053138864364091461 3193209759963537068267149)
                  ·
                    refine ⟨1197453659986326400600181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193209759963537068267149 1197453659986326400600181)
                    ·
                      rfl

theorem cell22_3498049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3498049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498049 prefixEnd_3498049 := by exact prefixLift 3498049
  have htrace : WordTrace (prefixWord ++ tailWord_3498049) baseStart_3498049 baseEnd_3498049 := by
    simpa [prefixWord, tailWord_3498049, baseEnd_3498049] using wordTrace_append hprefix tailTrace_3498049
  have hstable : (prefixWord ++ tailWord_3498049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498049).length < 2 ^ (prefixWord ++ tailWord_3498049).sum := by decide
  have hdescent : baseEnd_3498049 < baseStart_3498049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498062 : List Nat := [4, 1, 1, 1, 1, 6, 8]
def baseStart_3498062 : Nat := 118140960795 + 3498062 * 2 ^ 59
def prefixEnd_3498062 : Nat := 4983230072969 + 3 ^ 40 * 3498062 * 2
def baseEnd_3498062 : Nat := 44350300375999951852783

theorem tailTrace_3498062 : CollatzResearch.WordTrace tailWord_3498062 prefixEnd_3498062 44350300375999951852783 := by
  unfold tailWord_3498062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15948100331640783783945055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85056535102084180181040293 15948100331640783783945055)
  ·
    refine ⟨23922150497461175675917583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15948100331640783783945055 23922150497461175675917583)
    ·
      refine ⟨35883225746191763513876375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23922150497461175675917583 35883225746191763513876375)
      ·
        refine ⟨53824838619287645270814563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35883225746191763513876375 53824838619287645270814563)
        ·
          refine ⟨80737257928931467906221845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53824838619287645270814563 80737257928931467906221845)
          ·
            refine ⟨3784558965418662558104149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80737257928931467906221845 3784558965418662558104149)
            ·
              refine ⟨44350300375999951852783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3784558965418662558104149 44350300375999951852783)
              ·
                rfl

theorem cell22_3498062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 8].length) (baseStart_3498062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498062 prefixEnd_3498062 := by exact prefixLift 3498062
  have htrace : WordTrace (prefixWord ++ tailWord_3498062) baseStart_3498062 baseEnd_3498062 := by
    simpa [prefixWord, tailWord_3498062, baseEnd_3498062] using wordTrace_append hprefix tailTrace_3498062
  have hstable : (prefixWord ++ tailWord_3498062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498062).length < 2 ^ (prefixWord ++ tailWord_3498062).sum := by decide
  have hdescent : baseEnd_3498062 < baseStart_3498062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498094 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3498094 : Nat := 118140960795 + 3498094 * 2 ^ 59
def prefixEnd_3498094 : Nat := 4983230072969 + 3 ^ 40 * 3498094 * 2
def baseEnd_3498094 : Nat := 1197469064405961283225043

theorem tailTrace_3498094 : CollatzResearch.WordTrace tailWord_3498094 prefixEnd_3498094 1197469064405961283225043 := by
  unfold tailWord_3498094
  simp only [CollatzResearch.WordTrace]
  refine ⟨15948246223626292467090667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85057313192673559824483557 15948246223626292467090667)
  ·
    refine ⟨23922369335439438700636001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15948246223626292467090667 23922369335439438700636001)
    ·
      refine ⟨17941777001579579025477001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23922369335439438700636001 17941777001579579025477001)
      ·
        refine ⟨13456332751184684269107751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17941777001579579025477001 13456332751184684269107751)
        ·
          refine ⟨20184499126777026403661627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13456332751184684269107751 20184499126777026403661627)
          ·
            refine ⟨30276748690165539605492441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20184499126777026403661627 30276748690165539605492441)
            ·
              refine ⟨22707561517624154704119331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30276748690165539605492441 22707561517624154704119331)
              ·
                refine ⟨34061342276436232056178997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22707561517624154704119331 34061342276436232056178997)
                ·
                  refine ⟨3193250838415896755266781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34061342276436232056178997 3193250838415896755266781)
                  ·
                    refine ⟨1197469064405961283225043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193250838415896755266781 1197469064405961283225043)
                    ·
                      rfl

theorem cell22_3498094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3498094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498094 prefixEnd_3498094 := by exact prefixLift 3498094
  have htrace : WordTrace (prefixWord ++ tailWord_3498094) baseStart_3498094 baseEnd_3498094 := by
    simpa [prefixWord, tailWord_3498094, baseEnd_3498094] using wordTrace_append hprefix tailTrace_3498094
  have hstable : (prefixWord ++ tailWord_3498094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498094).length < 2 ^ (prefixWord ++ tailWord_3498094).sum := by decide
  have hdescent : baseEnd_3498094 < baseStart_3498094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498212 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_3498212 : Nat := 118140960795 + 3498212 * 2 ^ 59
def prefixEnd_3498212 : Nat := 4983230072969 + 3 ^ 40 * 3498212 * 2
def baseEnd_3498212 : Nat := 1197509458217448308774681

theorem tailTrace_3498212 : CollatzResearch.WordTrace tailWord_3498212 prefixEnd_3498212 1197509458217448308774681 := by
  unfold tailWord_3498212
  simp only [CollatzResearch.WordTrace]
  refine ⟨63795136801291422944760445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85060182401721897259680593 63795136801291422944760445)
  ·
    refine ⟨23923176300484283604285167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63795136801291422944760445 23923176300484283604285167)
    ·
      refine ⟨35884764450726425406427751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23923176300484283604285167 35884764450726425406427751)
      ·
        refine ⟨53827146676089638109641627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35884764450726425406427751 53827146676089638109641627)
        ·
          refine ⟨80740720014134457164462441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53827146676089638109641627 80740720014134457164462441)
          ·
            refine ⟨60555540010600842873346831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80740720014134457164462441 60555540010600842873346831)
            ·
              refine ⟨90833310015901264310020247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60555540010600842873346831 90833310015901264310020247)
              ·
                refine ⟨136249965023851896465030371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90833310015901264310020247 136249965023851896465030371)
                ·
                  refine ⟨204374947535777844697545557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136249965023851896465030371 204374947535777844697545557)
                  ·
                    refine ⟨1197509458217448308774681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 204374947535777844697545557 1197509458217448308774681)
                    ·
                      rfl

theorem cell22_3498212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_3498212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498212 prefixEnd_3498212 := by exact prefixLift 3498212
  have htrace : WordTrace (prefixWord ++ tailWord_3498212) baseStart_3498212 baseEnd_3498212 := by
    simpa [prefixWord, tailWord_3498212, baseEnd_3498212] using wordTrace_append hprefix tailTrace_3498212
  have hstable : (prefixWord ++ tailWord_3498212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498212).length < 2 ^ (prefixWord ++ tailWord_3498212).sum := by decide
  have hdescent : baseEnd_3498212 < baseStart_3498212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498297 : List Nat := [1, 2, 1, 6, 1, 3, 2, 2, 1, 3]
def baseStart_3498297 : Nat := 118140960795 + 3498297 * 2 ^ 59
def prefixEnd_3498297 : Nat := 4983230072969 + 3 ^ 40 * 3498297 * 2
def baseEnd_3498297 : Nat := 1197538555454536420399421

theorem tailTrace_3498297 : CollatzResearch.WordTrace tailWord_3498297 prefixEnd_3498297 1197538555454536420399421 := by
  unfold tailWord_3498297
  simp only [CollatzResearch.WordTrace]
  refine ⟨127593373807274905406365145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85062249204849936937576763 127593373807274905406365145)
  ·
    refine ⟨95695030355456179054773859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127593373807274905406365145 95695030355456179054773859)
    ·
      refine ⟨143542545533184268582160789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95695030355456179054773859 143542545533184268582160789)
      ·
        refine ⟨6728556821868012589788787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143542545533184268582160789 6728556821868012589788787)
        ·
          refine ⟨10092835232802018884683181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728556821868012589788787 10092835232802018884683181)
          ·
            refine ⟨3784813212300757081756193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10092835232802018884683181 3784813212300757081756193)
            ·
              refine ⟨2838609909225567811317145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3784813212300757081756193 2838609909225567811317145)
              ·
                refine ⟨2128957431919175858487859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2838609909225567811317145 2128957431919175858487859)
                ·
                  refine ⟨3193436147878763787731789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128957431919175858487859 3193436147878763787731789)
                  ·
                    refine ⟨1197538555454536420399421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193436147878763787731789 1197538555454536420399421)
                    ·
                      rfl

theorem cell22_3498297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 3].length) (baseStart_3498297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498297 prefixEnd_3498297 := by exact prefixLift 3498297
  have htrace : WordTrace (prefixWord ++ tailWord_3498297) baseStart_3498297 baseEnd_3498297 := by
    simpa [prefixWord, tailWord_3498297, baseEnd_3498297] using wordTrace_append hprefix tailTrace_3498297
  have hstable : (prefixWord ++ tailWord_3498297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498297).length < 2 ^ (prefixWord ++ tailWord_3498297).sum := by decide
  have hdescent : baseEnd_3498297 < baseStart_3498297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498308 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3498308 : Nat := 118140960795 + 3498308 * 2 ^ 59
def prefixEnd_3498308 : Nat := 4983230072969 + 3 ^ 40 * 3498308 * 2
def baseEnd_3498308 : Nat := 1197542320979336058374387

theorem tailTrace_3498308 : CollatzResearch.WordTrace tailWord_3498308 prefixEnd_3498308 1197542320979336058374387 := by
  unfold tailWord_3498308
  simp only [CollatzResearch.WordTrace]
  refine ⟨63796887505117527142507789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85062516673490036190010385 63796887505117527142507789)
  ·
    refine ⟨23923832814419072678440421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63796887505117527142507789 23923832814419072678440421)
    ·
      refine ⟨4485718652703576127207579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23923832814419072678440421 4485718652703576127207579)
      ·
        refine ⟨6728577979055364190811369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4485718652703576127207579 6728577979055364190811369)
        ·
          refine ⟨5046433484291523143108527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6728577979055364190811369 5046433484291523143108527)
          ·
            refine ⟨7569650226437284714662791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046433484291523143108527 7569650226437284714662791)
            ·
              refine ⟨11354475339655927071994187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7569650226437284714662791 11354475339655927071994187)
              ·
                refine ⟨17031713009483890607991281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11354475339655927071994187 17031713009483890607991281)
                ·
                  refine ⟨12773784757112917955993461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17031713009483890607991281 12773784757112917955993461)
                  ·
                    refine ⟨1197542320979336058374387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12773784757112917955993461 1197542320979336058374387)
                    ·
                      rfl

theorem cell22_3498308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3498308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498308 prefixEnd_3498308 := by exact prefixLift 3498308
  have htrace : WordTrace (prefixWord ++ tailWord_3498308) baseStart_3498308 baseEnd_3498308 := by
    simpa [prefixWord, tailWord_3498308, baseEnd_3498308] using wordTrace_append hprefix tailTrace_3498308
  have hstable : (prefixWord ++ tailWord_3498308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498308).length < 2 ^ (prefixWord ++ tailWord_3498308).sum := by decide
  have hdescent : baseEnd_3498308 < baseStart_3498308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498338 : List Nat := [3, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_3498338 : Nat := 118140960795 + 3498338 * 2 ^ 59
def prefixEnd_3498338 : Nat := 4983230072969 + 3 ^ 40 * 3498338 * 2
def baseEnd_3498338 : Nat := 399184196864141993374765

theorem tailTrace_3498338 : CollatzResearch.WordTrace tailWord_3498338 prefixEnd_3498338 399184196864141993374765 := by
  unfold tailWord_3498338
  simp only [CollatzResearch.WordTrace]
  refine ⟨31898717300031592352151917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85063246133417579605738445 31898717300031592352151917)
  ·
    refine ⟨11962018987511847132056969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31898717300031592352151917 11962018987511847132056969)
    ·
      refine ⟨8971514240633885349042727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11962018987511847132056969 8971514240633885349042727)
      ·
        refine ⟨13457271360950828023564091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8971514240633885349042727 13457271360950828023564091)
        ·
          refine ⟨20185907041426242035346137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13457271360950828023564091 20185907041426242035346137)
          ·
            refine ⟨15139430281069681526509603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20185907041426242035346137 15139430281069681526509603)
            ·
              refine ⟨22709145421604522289764405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15139430281069681526509603 22709145421604522289764405)
              ·
                refine ⟨2128982383275423964665413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22709145421604522289764405 2128982383275423964665413)
                ·
                  refine ⟨399184196864141993374765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128982383275423964665413 399184196864141993374765)
                  ·
                    rfl

theorem cell22_3498338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_3498338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498338 prefixEnd_3498338 := by exact prefixLift 3498338
  have htrace : WordTrace (prefixWord ++ tailWord_3498338) baseStart_3498338 baseEnd_3498338 := by
    simpa [prefixWord, tailWord_3498338, baseEnd_3498338] using wordTrace_append hprefix tailTrace_3498338
  have hstable : (prefixWord ++ tailWord_3498338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498338).length < 2 ^ (prefixWord ++ tailWord_3498338).sum := by decide
  have hdescent : baseEnd_3498338 < baseStart_3498338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498349 : List Nat := [1, 5, 1, 1, 1, 2, 11]
def baseStart_3498349 : Nat := 118140960795 + 3498349 * 2 ^ 59
def prefixEnd_3498349 : Nat := 4983230072969 + 3 ^ 40 * 3498349 * 2
def baseEnd_3498349 : Nat := 44353939115452800670343

theorem tailTrace_3498349 : CollatzResearch.WordTrace tailWord_3498349 prefixEnd_3498349 44353939115452800670343 := by
  unfold tailWord_3498349
  simp only [CollatzResearch.WordTrace]
  refine ⟨127595270403086518287258101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85063513602057678858172067 127595270403086518287258101)
  ·
    refine ⟨11962056600289361089430447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127595270403086518287258101 11962056600289361089430447)
    ·
      refine ⟨17943084900434041634145671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11962056600289361089430447 17943084900434041634145671)
      ·
        refine ⟨26914627350651062451218507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17943084900434041634145671 26914627350651062451218507)
        ·
          refine ⟨40371941025976593676827761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26914627350651062451218507 40371941025976593676827761)
          ·
            refine ⟨30278955769482445257620821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40371941025976593676827761 30278955769482445257620821)
            ·
              refine ⟨44353939115452800670343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30278955769482445257620821 44353939115452800670343)
              ·
                rfl

theorem cell22_3498349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 11].length) (baseStart_3498349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498349 prefixEnd_3498349 := by exact prefixLift 3498349
  have htrace : WordTrace (prefixWord ++ tailWord_3498349) baseStart_3498349 baseEnd_3498349 := by
    simpa [prefixWord, tailWord_3498349, baseEnd_3498349] using wordTrace_append hprefix tailTrace_3498349
  have hstable : (prefixWord ++ tailWord_3498349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498349).length < 2 ^ (prefixWord ++ tailWord_3498349).sum := by decide
  have hdescent : baseEnd_3498349 < baseStart_3498349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498409 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_3498409 : Nat := 118140960795 + 3498409 * 2 ^ 59
def prefixEnd_3498409 : Nat := 4983230072969 + 3 ^ 40 * 3498409 * 2
def baseEnd_3498409 : Nat := 1197576895343405461599077

theorem tailTrace_3498409 : CollatzResearch.WordTrace tailWord_3498409 prefixEnd_3498409 1197576895343405461599077 := by
  unfold tailWord_3498409
  simp only [CollatzResearch.WordTrace]
  refine ⟨127597458782869148534442281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85064972521912765689628187 127597458782869148534442281)
  ·
    refine ⟨95698094087151861400831711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127597458782869148534442281 95698094087151861400831711)
    ·
      refine ⟨143547141130727792101247567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95698094087151861400831711 143547141130727792101247567)
      ·
        refine ⟨215320711696091688151871351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143547141130727792101247567 215320711696091688151871351)
        ·
          refine ⟨322981067544137532227807027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215320711696091688151871351 322981067544137532227807027)
          ·
            refine ⟨484471601316206298341710541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322981067544137532227807027 484471601316206298341710541)
            ·
              refine ⟨181676850493577361878141453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 484471601316206298341710541 181676850493577361878141453)
              ·
                refine ⟨68128818935091510704303045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181676850493577361878141453 68128818935091510704303045)
                ·
                  refine ⟨12774153550329658257056821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68128818935091510704303045 12774153550329658257056821)
                  ·
                    refine ⟨1197576895343405461599077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12774153550329658257056821 1197576895343405461599077)
                    ·
                      rfl

theorem cell22_3498409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_3498409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498409 prefixEnd_3498409 := by exact prefixLift 3498409
  have htrace : WordTrace (prefixWord ++ tailWord_3498409) baseStart_3498409 baseEnd_3498409 := by
    simpa [prefixWord, tailWord_3498409, baseEnd_3498409] using wordTrace_append hprefix tailTrace_3498409
  have hstable : (prefixWord ++ tailWord_3498409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498409).length < 2 ^ (prefixWord ++ tailWord_3498409).sum := by decide
  have hdescent : baseEnd_3498409 < baseStart_3498409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498424 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_3498424 : Nat := 118140960795 + 3498424 * 2 ^ 59
def prefixEnd_3498424 : Nat := 4983230072969 + 3 ^ 40 * 3498424 * 2
def baseEnd_3498424 : Nat := 1197582030149950422474031

theorem tailTrace_3498424 : CollatzResearch.WordTrace tailWord_3498424 prefixEnd_3498424 1197582030149950422474031 := by
  unfold tailWord_3498424
  simp only [CollatzResearch.WordTrace]
  refine ⟨63799002938907403048119163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85065337251876537397492217 63799002938907403048119163)
  ·
    refine ⟨95698504408361104572178745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63799002938907403048119163 95698504408361104572178745)
    ·
      refine ⟨71773878306270828429134059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95698504408361104572178745 71773878306270828429134059)
      ·
        refine ⟨107660817459406242643701089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71773878306270828429134059 107660817459406242643701089)
        ·
          refine ⟨80745613094554681982775817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107660817459406242643701089 80745613094554681982775817)
          ·
            refine ⟨60559209820916011487081863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80745613094554681982775817 60559209820916011487081863)
            ·
              refine ⟨90838814731374017230622795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60559209820916011487081863 90838814731374017230622795)
              ·
                refine ⟨136258222097061025845934193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90838814731374017230622795 136258222097061025845934193)
                ·
                  refine ⟨102193666572795769384450645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136258222097061025845934193 102193666572795769384450645)
                  ·
                    refine ⟨1197582030149950422474031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102193666572795769384450645 1197582030149950422474031)
                    ·
                      rfl

theorem cell22_3498424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_3498424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498424 prefixEnd_3498424 := by exact prefixLift 3498424
  have htrace : WordTrace (prefixWord ++ tailWord_3498424) baseStart_3498424 baseEnd_3498424 := by
    simpa [prefixWord, tailWord_3498424, baseEnd_3498424] using wordTrace_append hprefix tailTrace_3498424
  have hstable : (prefixWord ++ tailWord_3498424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498424).length < 2 ^ (prefixWord ++ tailWord_3498424).sum := by decide
  have hdescent : baseEnd_3498424 < baseStart_3498424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498428 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 5]
def baseStart_3498428 : Nat := 118140960795 + 3498428 * 2 ^ 59
def prefixEnd_3498428 : Nat := 4983230072969 + 3 ^ 40 * 3498428 * 2
def baseEnd_3498428 : Nat := 399194466477231915124673

theorem tailTrace_3498428 : CollatzResearch.WordTrace tailWord_3498428 prefixEnd_3498428 399194466477231915124673 := by
  unfold tailWord_3498428
  simp only [CollatzResearch.WordTrace]
  refine ⟨63799075884900157389691969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85065434513200209852922625 63799075884900157389691969)
  ·
    refine ⟨47849306913675118042268977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63799075884900157389691969 47849306913675118042268977)
    ·
      refine ⟨35886980185256338531701733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47849306913675118042268977 35886980185256338531701733)
      ·
        refine ⟨6728808784735563474694075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35886980185256338531701733 6728808784735563474694075)
        ·
          refine ⟨10093213177103345212041113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728808784735563474694075 10093213177103345212041113)
          ·
            refine ⟨7569909882827508909030835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10093213177103345212041113 7569909882827508909030835)
            ·
              refine ⟨11354864824241263363546253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7569909882827508909030835 11354864824241263363546253)
              ·
                refine ⟨4258074309090473761329845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11354864824241263363546253 4258074309090473761329845)
                ·
                  refine ⟨399194466477231915124673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4258074309090473761329845 399194466477231915124673)
                  ·
                    rfl

theorem cell22_3498428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_3498428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498428 prefixEnd_3498428 := by exact prefixLift 3498428
  have htrace : WordTrace (prefixWord ++ tailWord_3498428) baseStart_3498428 baseEnd_3498428 := by
    simpa [prefixWord, tailWord_3498428, baseEnd_3498428] using wordTrace_append hprefix tailTrace_3498428
  have hstable : (prefixWord ++ tailWord_3498428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498428).length < 2 ^ (prefixWord ++ tailWord_3498428).sum := by decide
  have hdescent : baseEnd_3498428 < baseStart_3498428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498471 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3498471 : Nat := 118140960795 + 3498471 * 2 ^ 59
def prefixEnd_3498471 : Nat := 4983230072969 + 3 ^ 40 * 3498471 * 2
def baseEnd_3498471 : Nat := 1197598119210457966548887

theorem tailTrace_3498471 : CollatzResearch.WordTrace tailWord_3498471 prefixEnd_3498471 1197598119210457966548887 := by
  unfold tailWord_3498471
  simp only [CollatzResearch.WordTrace]
  refine ⟨127599720108644533123199267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85066480072429688748799511 127599720108644533123199267)
  ·
    refine ⟨191399580162966799684798901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127599720108644533123199267 191399580162966799684798901)
    ·
      refine ⟨17943710640278137470449897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191399580162966799684798901 17943710640278137470449897)
      ·
        refine ⟨13457782980208603102837423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17943710640278137470449897 13457782980208603102837423)
        ·
          refine ⟨20186674470312904654256135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13457782980208603102837423 20186674470312904654256135)
          ·
            refine ⟨30280011705469356981384203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20186674470312904654256135 30280011705469356981384203)
            ·
              refine ⟨45420017558204035472076305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30280011705469356981384203 45420017558204035472076305)
              ·
                refine ⟨34065013168653026604057229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45420017558204035472076305 34065013168653026604057229)
                ·
                  refine ⟨12774379938244884976521461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34065013168653026604057229 12774379938244884976521461)
                  ·
                    refine ⟨1197598119210457966548887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12774379938244884976521461 1197598119210457966548887)
                    ·
                      rfl

theorem cell22_3498471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3498471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498471 prefixEnd_3498471 := by exact prefixLift 3498471
  have htrace : WordTrace (prefixWord ++ tailWord_3498471) baseStart_3498471 baseEnd_3498471 := by
    simpa [prefixWord, tailWord_3498471, baseEnd_3498471] using wordTrace_append hprefix tailTrace_3498471
  have hstable : (prefixWord ++ tailWord_3498471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498471).length < 2 ^ (prefixWord ++ tailWord_3498471).sum := by decide
  have hdescent : baseEnd_3498471 < baseStart_3498471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498488 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 2, 3]
def baseStart_3498488 : Nat := 118140960795 + 3498488 * 2 ^ 59
def prefixEnd_3498488 : Nat := 4983230072969 + 3 ^ 40 * 3498488 * 2
def baseEnd_3498488 : Nat := 1197603938657875588873835

theorem tailTrace_3498488 : CollatzResearch.WordTrace tailWord_3498488 prefixEnd_3498488 1197603938657875588873835 := by
  unfold tailWord_3498488
  simp only [CollatzResearch.WordTrace]
  refine ⟨63800170074791472513284059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85066893433055296684378745 63800170074791472513284059)
  ·
    refine ⟨95700255112187208769926089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63800170074791472513284059 95700255112187208769926089)
    ·
      refine ⟨71775191334140406577444567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95700255112187208769926089 71775191334140406577444567)
      ·
        refine ⟨107662787001210609866166851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71775191334140406577444567 107662787001210609866166851)
        ·
          refine ⟨161494180501815914799250277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107662787001210609866166851 161494180501815914799250277)
          ·
            refine ⟨30280158844090484024859427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161494180501815914799250277 30280158844090484024859427)
            ·
              refine ⟨45420238266135726037289141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30280158844090484024859427 45420238266135726037289141)
              ·
                refine ⟨4258147337450224315995857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45420238266135726037289141 4258147337450224315995857)
                ·
                  refine ⟨3193610503087668236996893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258147337450224315995857 3193610503087668236996893)
                  ·
                    refine ⟨1197603938657875588873835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193610503087668236996893 1197603938657875588873835)
                    ·
                      rfl

theorem cell22_3498488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_3498488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498488 prefixEnd_3498488 := by exact prefixLift 3498488
  have htrace : WordTrace (prefixWord ++ tailWord_3498488) baseStart_3498488 baseEnd_3498488 := by
    simpa [prefixWord, tailWord_3498488, baseEnd_3498488] using wordTrace_append hprefix tailTrace_3498488
  have hstable : (prefixWord ++ tailWord_3498488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498488).length < 2 ^ (prefixWord ++ tailWord_3498488).sum := by decide
  have hdescent : baseEnd_3498488 < baseStart_3498488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498503 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 1, 6]
def baseStart_3498503 : Nat := 118140960795 + 3498503 * 2 ^ 59
def prefixEnd_3498503 : Nat := 4983230072969 + 3 ^ 40 * 3498503 * 2
def baseEnd_3498503 : Nat := 1197609073464420549748789

theorem tailTrace_3498503 : CollatzResearch.WordTrace tailWord_3498503 prefixEnd_3498503 1197609073464420549748789 := by
  unfold tailWord_3498503
  simp only [CollatzResearch.WordTrace]
  refine ⟨127600887244528602588364163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85067258163019068392242775 127600887244528602588364163)
  ·
    refine ⟨191401330866792903882546245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127600887244528602588364163 191401330866792903882546245)
    ·
      refine ⟨35887749537523669477977421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191401330866792903882546245 35887749537523669477977421)
      ·
        refine ⟨13457906076571376054241533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35887749537523669477977421 13457906076571376054241533)
        ·
          refine ⟨5046714778714266020340575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13457906076571376054241533 5046714778714266020340575)
          ·
            refine ⟨7570072168071399030510863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046714778714266020340575 7570072168071399030510863)
            ·
              refine ⟨11355108252107098545766295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570072168071399030510863 11355108252107098545766295)
              ·
                refine ⟨17032662378160647818649443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11355108252107098545766295 17032662378160647818649443)
                ·
                  refine ⟨25548993567240971727974165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17032662378160647818649443 25548993567240971727974165)
                  ·
                    refine ⟨1197609073464420549748789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25548993567240971727974165 1197609073464420549748789)
                    ·
                      rfl

theorem cell22_3498503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_3498503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498503 prefixEnd_3498503 := by exact prefixLift 3498503
  have htrace : WordTrace (prefixWord ++ tailWord_3498503) baseStart_3498503 baseEnd_3498503 := by
    simpa [prefixWord, tailWord_3498503, baseEnd_3498503] using wordTrace_append hprefix tailTrace_3498503
  have hstable : (prefixWord ++ tailWord_3498503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498503).length < 2 ^ (prefixWord ++ tailWord_3498503).sum := by decide
  have hdescent : baseEnd_3498503 < baseStart_3498503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498509 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3498509 : Nat := 118140960795 + 3498509 * 2 ^ 59
def prefixEnd_3498509 : Nat := 4983230072969 + 3 ^ 40 * 3498509 * 2
def baseEnd_3498509 : Nat := 1197611127387038534098771

theorem tailTrace_3498509 : CollatzResearch.WordTrace tailWord_3498509 prefixEnd_3498509 1197611127387038534098771 := by
  unfold tailWord_3498509
  simp only [CollatzResearch.WordTrace]
  refine ⟨127601106082506865613082581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85067404055004577075388387 127601106082506865613082581)
  ·
    refine ⟨2990650923808754662806623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127601106082506865613082581 2990650923808754662806623)
    ·
      refine ⟨4485976385713131994209935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2990650923808754662806623 4485976385713131994209935)
      ·
        refine ⟨6728964578569697991314903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4485976385713131994209935 6728964578569697991314903)
        ·
          refine ⟨10093446867854546986972355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728964578569697991314903 10093446867854546986972355)
          ·
            refine ⟨15140170301781820480458533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10093446867854546986972355 15140170301781820480458533)
            ·
              refine ⟨2838781931584091340085975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15140170301781820480458533 2838781931584091340085975)
              ·
                refine ⟨4258172897376137010128963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838781931584091340085975 4258172897376137010128963)
                ·
                  refine ⟨6387259346064205515193445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258172897376137010128963 6387259346064205515193445)
                  ·
                    refine ⟨1197611127387038534098771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387259346064205515193445 1197611127387038534098771)
                    ·
                      rfl

theorem cell22_3498509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3498509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498509 prefixEnd_3498509 := by exact prefixLift 3498509
  have htrace : WordTrace (prefixWord ++ tailWord_3498509) baseStart_3498509 baseEnd_3498509 := by
    simpa [prefixWord, tailWord_3498509, baseEnd_3498509] using wordTrace_append hprefix tailTrace_3498509
  have hstable : (prefixWord ++ tailWord_3498509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498509).length < 2 ^ (prefixWord ++ tailWord_3498509).sum := by decide
  have hdescent : baseEnd_3498509 < baseStart_3498509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498533 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_3498533 : Nat := 118140960795 + 3498533 * 2 ^ 59
def prefixEnd_3498533 : Nat := 4983230072969 + 3 ^ 40 * 3498533 * 2
def baseEnd_3498533 : Nat := 1197619343077510471498697

theorem tailTrace_3498533 : CollatzResearch.WordTrace tailWord_3498533 prefixEnd_3498533 1197619343077510471498697 := by
  unfold tailWord_3498533
  simp only [CollatzResearch.WordTrace]
  refine ⟨127601981434419917711956253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85067987622946611807970835 127601981434419917711956253)
  ·
    refine ⟨47850743037907469141983595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127601981434419917711956253 47850743037907469141983595)
    ·
      refine ⟨71776114556861203712975393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47850743037907469141983595 71776114556861203712975393)
      ·
        refine ⟨53832085917645902784731545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71776114556861203712975393 53832085917645902784731545)
        ·
          refine ⟨40374064438234427088548659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53832085917645902784731545 40374064438234427088548659)
          ·
            refine ⟨60561096657351640632822989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40374064438234427088548659 60561096657351640632822989)
            ·
              refine ⟨22710411246506865237308621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60561096657351640632822989 22710411246506865237308621)
              ·
                refine ⟨8516404217440074463990733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22710411246506865237308621 8516404217440074463990733)
                ·
                  refine ⟨3193651581540027923996525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8516404217440074463990733 3193651581540027923996525)
                  ·
                    refine ⟨1197619343077510471498697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193651581540027923996525 1197619343077510471498697)
                    ·
                      rfl

theorem cell22_3498533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_3498533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498533 prefixEnd_3498533 := by exact prefixLift 3498533
  have htrace : WordTrace (prefixWord ++ tailWord_3498533) baseStart_3498533 baseEnd_3498533 := by
    simpa [prefixWord, tailWord_3498533, baseEnd_3498533] using wordTrace_append hprefix tailTrace_3498533
  have hstable : (prefixWord ++ tailWord_3498533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498533).length < 2 ^ (prefixWord ++ tailWord_3498533).sum := by decide
  have hdescent : baseEnd_3498533 < baseStart_3498533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498567 : List Nat := [1, 1, 4, 1, 4, 1, 3, 3, 1, 3]
def baseStart_3498567 : Nat := 118140960795 + 3498567 * 2 ^ 59
def prefixEnd_3498567 : Nat := 4983230072969 + 3 ^ 40 * 3498567 * 2
def baseEnd_3498567 : Nat := 1197630981972345716148593

theorem tailTrace_3498567 : CollatzResearch.WordTrace tailWord_3498567 prefixEnd_3498567 1197630981972345716148593 := by
  unfold tailWord_3498567
  simp only [CollatzResearch.WordTrace]
  refine ⟨127603221516296741518693955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85068814344197827679129303 127603221516296741518693955)
  ·
    refine ⟨191404832274445112278040933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127603221516296741518693955 191404832274445112278040933)
    ·
      refine ⟨35888406051458458552132675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191404832274445112278040933 35888406051458458552132675)
      ·
        refine ⟨53832609077187687828199013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35888406051458458552132675 53832609077187687828199013)
        ·
          refine ⟨10093614201972691467787315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53832609077187687828199013 10093614201972691467787315)
          ·
            refine ⟨15140421302959037201680973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10093614201972691467787315 15140421302959037201680973)
            ·
              refine ⟨5677657988609638950630365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15140421302959037201680973 5677657988609638950630365)
              ·
                refine ⟨2129121745728614606486387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5677657988609638950630365 2129121745728614606486387)
                ·
                  refine ⟨3193682618592921909729581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129121745728614606486387 3193682618592921909729581)
                  ·
                    refine ⟨1197630981972345716148593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193682618592921909729581 1197630981972345716148593)
                    ·
                      rfl

theorem cell22_3498567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_3498567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498567 prefixEnd_3498567 := by exact prefixLift 3498567
  have htrace : WordTrace (prefixWord ++ tailWord_3498567) baseStart_3498567 baseEnd_3498567 := by
    simpa [prefixWord, tailWord_3498567, baseEnd_3498567] using wordTrace_append hprefix tailTrace_3498567
  have hstable : (prefixWord ++ tailWord_3498567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498567).length < 2 ^ (prefixWord ++ tailWord_3498567).sum := by decide
  have hdescent : baseEnd_3498567 < baseStart_3498567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498590 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3498590 : Nat := 118140960795 + 3498590 * 2 ^ 59
def prefixEnd_3498590 : Nat := 4983230072969 + 3 ^ 40 * 3498590 * 2
def baseEnd_3498590 : Nat := 1197638855342381322823523

theorem tailTrace_3498590 : CollatzResearch.WordTrace tailWord_3498590 prefixEnd_3498590 1197638855342381322823523 := by
  unfold tailWord_3498590
  simp only [CollatzResearch.WordTrace]
  refine ⟨15950507549401677055847653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85069373596808944297854149 15950507549401677055847653)
  ·
    refine ⟨2990720165512814447971435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15950507549401677055847653 2990720165512814447971435)
    ·
      refine ⟨4486080248269221671957153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2990720165512814447971435 4486080248269221671957153)
      ·
        refine ⟨3364560186201916253967865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4486080248269221671957153 3364560186201916253967865)
        ·
          refine ⟨2523420139651437190475899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3364560186201916253967865 2523420139651437190475899)
          ·
            refine ⟨3785130209477155785713849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523420139651437190475899 3785130209477155785713849)
            ·
              refine ⟨2838847657107866839285387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785130209477155785713849 2838847657107866839285387)
              ·
                refine ⟨4258271485661800258928081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838847657107866839285387 4258271485661800258928081)
                ·
                  refine ⟨3193703614246350194196061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258271485661800258928081 3193703614246350194196061)
                  ·
                    refine ⟨1197638855342381322823523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193703614246350194196061 1197638855342381322823523)
                    ·
                      rfl

theorem cell22_3498590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3498590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498590 prefixEnd_3498590 := by exact prefixLift 3498590
  have htrace : WordTrace (prefixWord ++ tailWord_3498590) baseStart_3498590 baseEnd_3498590 := by
    simpa [prefixWord, tailWord_3498590, baseEnd_3498590] using wordTrace_append hprefix tailTrace_3498590
  have hstable : (prefixWord ++ tailWord_3498590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498590).length < 2 ^ (prefixWord ++ tailWord_3498590).sum := by decide
  have hdescent : baseEnd_3498590 < baseStart_3498590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498597 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 5]
def baseStart_3498597 : Nat := 118140960795 + 3498597 * 2 ^ 59
def prefixEnd_3498597 : Nat := 4983230072969 + 3 ^ 40 * 3498597 * 2
def baseEnd_3498597 : Nat := 399213750528478545966167

theorem tailTrace_3498597 : CollatzResearch.WordTrace tailWord_3498597 prefixEnd_3498597 399213750528478545966167 := by
  unfold tailWord_3498597
  simp only [CollatzResearch.WordTrace]
  refine ⟨127604315706188056642286045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85069543804125371094857363 127604315706188056642286045)
  ·
    refine ⟨47851618389820521240857267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127604315706188056642286045 47851618389820521240857267)
    ·
      refine ⟨71777427584730781861285901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47851618389820521240857267 71777427584730781861285901)
      ·
        refine ⟨26916535344274043197982213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71777427584730781861285901 26916535344274043197982213)
        ·
          refine ⟨5046850377051383099621665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26916535344274043197982213 5046850377051383099621665)
          ·
            refine ⟨3785137782788537324716249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5046850377051383099621665 3785137782788537324716249)
            ·
              refine ⟨2838853337091402993537187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785137782788537324716249 2838853337091402993537187)
              ·
                refine ⟨4258280005637104490305781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838853337091402993537187 4258280005637104490305781)
                ·
                  refine ⟨399213750528478545966167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4258280005637104490305781 399213750528478545966167)
                  ·
                    rfl

theorem cell22_3498597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_3498597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498597 prefixEnd_3498597 := by exact prefixLift 3498597
  have htrace : WordTrace (prefixWord ++ tailWord_3498597) baseStart_3498597 baseEnd_3498597 := by
    simpa [prefixWord, tailWord_3498597, baseEnd_3498597] using wordTrace_append hprefix tailTrace_3498597
  have hstable : (prefixWord ++ tailWord_3498597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498597).length < 2 ^ (prefixWord ++ tailWord_3498597).sum := by decide
  have hdescent : baseEnd_3498597 < baseStart_3498597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498610 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_3498610 : Nat := 118140960795 + 3498610 * 2 ^ 59
def prefixEnd_3498610 : Nat := 4983230072969 + 3 ^ 40 * 3498610 * 2
def baseEnd_3498610 : Nat := 1197645701751107937323461

theorem tailTrace_3498610 : CollatzResearch.WordTrace tailWord_3498610 prefixEnd_3498610 1197645701751107937323461 := by
  unfold tailWord_3498610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31901197463785239965627321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85069859903427306575006189 31901197463785239965627321)
  ·
    refine ⟨23925898097838929974220491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31901197463785239965627321 23925898097838929974220491)
    ·
      refine ⟨35888847146758394961330737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23925898097838929974220491 35888847146758394961330737)
      ·
        refine ⟨26916635360068796220998053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35888847146758394961330737 26916635360068796220998053)
        ·
          refine ⟨5046869130012899291437135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26916635360068796220998053 5046869130012899291437135)
          ·
            refine ⟨7570303695019348937155703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046869130012899291437135 7570303695019348937155703)
            ·
              refine ⟨11355455542529023405733555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570303695019348937155703 11355455542529023405733555)
              ·
                refine ⟨17033183313793535108600333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11355455542529023405733555 17033183313793535108600333)
                ·
                  refine ⟨6387443742672575665725125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17033183313793535108600333 6387443742672575665725125)
                  ·
                    refine ⟨1197645701751107937323461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387443742672575665725125 1197645701751107937323461)
                    ·
                      rfl

theorem cell22_3498610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_3498610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498610 prefixEnd_3498610 := by exact prefixLift 3498610
  have htrace : WordTrace (prefixWord ++ tailWord_3498610) baseStart_3498610 baseEnd_3498610 := by
    simpa [prefixWord, tailWord_3498610, baseEnd_3498610] using wordTrace_append hprefix tailTrace_3498610
  have hstable : (prefixWord ++ tailWord_3498610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498610).length < 2 ^ (prefixWord ++ tailWord_3498610).sum := by decide
  have hdescent : baseEnd_3498610 < baseStart_3498610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498623 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 4, 3]
def baseStart_3498623 : Nat := 118140960795 + 3498623 * 2 ^ 59
def prefixEnd_3498623 : Nat := 4983230072969 + 3 ^ 40 * 3498623 * 2
def baseEnd_3498623 : Nat := 1197650151916780236748421

theorem tailTrace_3498623 : CollatzResearch.WordTrace tailWord_3498623 prefixEnd_3498623 1197650151916780236748421 := by
  unfold tailWord_3498623
  simp only [CollatzResearch.WordTrace]
  refine ⟨127605264004093863082732523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85070176002729242055155015 127605264004093863082732523)
  ·
    refine ⟨191407896006140794624098785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127605264004093863082732523 191407896006140794624098785)
    ·
      refine ⟨143555922004605595968074089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191407896006140794624098785 143555922004605595968074089)
      ·
        refine ⟨107666941503454196976055567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143555922004605595968074089 107666941503454196976055567)
        ·
          refine ⟨161500412255181295464083351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107666941503454196976055567 161500412255181295464083351)
          ·
            refine ⟨242250618382771943196125027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161500412255181295464083351 242250618382771943196125027)
            ·
              refine ⟨363375927574157914794187541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242250618382771943196125027 363375927574157914794187541)
              ·
                refine ⟨17033246605038652255977541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 363375927574157914794187541 17033246605038652255977541)
                ·
                  refine ⟨3193733738444747297995789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17033246605038652255977541 3193733738444747297995789)
                  ·
                    refine ⟨1197650151916780236748421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193733738444747297995789 1197650151916780236748421)
                    ·
                      rfl

theorem cell22_3498623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_3498623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498623 prefixEnd_3498623 := by exact prefixLift 3498623
  have htrace : WordTrace (prefixWord ++ tailWord_3498623) baseStart_3498623 baseEnd_3498623 := by
    simpa [prefixWord, tailWord_3498623, baseEnd_3498623] using wordTrace_append hprefix tailTrace_3498623
  have hstable : (prefixWord ++ tailWord_3498623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498623).length < 2 ^ (prefixWord ++ tailWord_3498623).sum := by decide
  have hdescent : baseEnd_3498623 < baseStart_3498623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498625 : List Nat := [1, 2, 4, 2, 1, 1, 2, 5, 4]
def baseStart_3498625 : Nat := 118140960795 + 3498625 * 2 ^ 59
def prefixEnd_3498625 : Nat := 4983230072969 + 3 ^ 40 * 3498625 * 2
def baseEnd_3498625 : Nat := 399216945519217632732805

theorem tailTrace_3498625 : CollatzResearch.WordTrace tailWord_3498625 prefixEnd_3498625 399216945519217632732805 := by
  unfold tailWord_3498625
  simp only [CollatzResearch.WordTrace]
  refine ⟨127605336950086617424305329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85070224633391078282870219 127605336950086617424305329)
  ·
    refine ⟨95704002712564963068228997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127605336950086617424305329 95704002712564963068228997)
    ·
      refine ⟨17944500508605930575292937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95704002712564963068228997 17944500508605930575292937)
      ·
        refine ⟨13458375381454447931469703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17944500508605930575292937 13458375381454447931469703)
        ·
          refine ⟨20187563072181671897204555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13458375381454447931469703 20187563072181671897204555)
          ·
            refine ⟨30281344608272507845806833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20187563072181671897204555 30281344608272507845806833)
            ·
              refine ⟨22711008456204380884355125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30281344608272507845806833 22711008456204380884355125)
              ·
                refine ⟨2129157042769160707908293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22711008456204380884355125 2129157042769160707908293)
                ·
                  refine ⟨399216945519217632732805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2129157042769160707908293 399216945519217632732805)
                  ·
                    rfl

theorem cell22_3498625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 4].length) (baseStart_3498625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498625 prefixEnd_3498625 := by exact prefixLift 3498625
  have htrace : WordTrace (prefixWord ++ tailWord_3498625) baseStart_3498625 baseEnd_3498625 := by
    simpa [prefixWord, tailWord_3498625, baseEnd_3498625] using wordTrace_append hprefix tailTrace_3498625
  have hstable : (prefixWord ++ tailWord_3498625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498625).length < 2 ^ (prefixWord ++ tailWord_3498625).sum := by decide
  have hdescent : baseEnd_3498625 < baseStart_3498625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498642 : List Nat := [3, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_3498642 : Nat := 118140960795 + 3498642 * 2 ^ 59
def prefixEnd_3498642 : Nat := 4983230072969 + 3 ^ 40 * 3498642 * 2
def baseEnd_3498642 : Nat := 399218885335023506841121

theorem tailTrace_3498642 : CollatzResearch.WordTrace tailWord_3498642 prefixEnd_3498642 399218885335023506841121 := by
  unfold tailWord_3498642
  simp only [CollatzResearch.WordTrace]
  refine ⟨31901489247756257331918545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85070637994016686218449453 31901489247756257331918545)
  ·
    refine ⟨23926116935817192998938909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31901489247756257331918545 23926116935817192998938909)
    ·
      refine ⟨8972293850931447374602091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23926116935817192998938909 8972293850931447374602091)
      ·
        refine ⟨13458440776397171061903137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8972293850931447374602091 13458440776397171061903137)
        ·
          refine ⟨10093830582297878296427353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13458440776397171061903137 10093830582297878296427353)
          ·
            refine ⟨7570372936723408722320515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10093830582297878296427353 7570372936723408722320515)
            ·
              refine ⟨11355559405085113083480773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570372936723408722320515 11355559405085113083480773)
              ·
                refine ⟨2129167388453458703152645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11355559405085113083480773 2129167388453458703152645)
                ·
                  refine ⟨399218885335023506841121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2129167388453458703152645 399218885335023506841121)
                  ·
                    rfl

theorem cell22_3498642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_3498642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498642 prefixEnd_3498642 := by exact prefixLift 3498642
  have htrace : WordTrace (prefixWord ++ tailWord_3498642) baseStart_3498642 baseEnd_3498642 := by
    simpa [prefixWord, tailWord_3498642, baseEnd_3498642] using wordTrace_append hprefix tailTrace_3498642
  have hstable : (prefixWord ++ tailWord_3498642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498642).length < 2 ^ (prefixWord ++ tailWord_3498642).sum := by decide
  have hdescent : baseEnd_3498642 < baseStart_3498642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498651 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 3, 9]
def baseStart_3498651 : Nat := 118140960795 + 3498651 * 2 ^ 59
def prefixEnd_3498651 : Nat := 4983230072969 + 3 ^ 40 * 3498651 * 2
def baseEnd_3498651 : Nat := 1197659736888997497048335

theorem tailTrace_3498651 : CollatzResearch.WordTrace tailWord_3498651 prefixEnd_3498651 1197659736888997497048335 := by
  unfold tailWord_3498651
  simp only [CollatzResearch.WordTrace]
  refine ⟨127606285247992423864751807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85070856831994949243167871 127606285247992423864751807)
  ·
    refine ⟨191409427871988635797127711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127606285247992423864751807 191409427871988635797127711)
    ·
      refine ⟨287114141807982953695691567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191409427871988635797127711 287114141807982953695691567)
      ·
        refine ⟨430671212711974430543537351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287114141807982953695691567 430671212711974430543537351)
        ·
          refine ⟨646006819067961645815306027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430671212711974430543537351 646006819067961645815306027)
          ·
            refine ⟨969010228601942468722959041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646006819067961645815306027 969010228601942468722959041)
            ·
              refine ⟨726757671451456851542219281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969010228601942468722959041 726757671451456851542219281)
              ·
                refine ⟨545068253588592638656664461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726757671451456851542219281 545068253588592638656664461)
                ·
                  refine ⟨204400595095722239496249173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545068253588592638656664461 204400595095722239496249173)
                  ·
                    refine ⟨1197659736888997497048335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 204400595095722239496249173 1197659736888997497048335)
                    ·
                      rfl

theorem cell22_3498651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_3498651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498651 prefixEnd_3498651 := by exact prefixLift 3498651
  have htrace : WordTrace (prefixWord ++ tailWord_3498651) baseStart_3498651 baseEnd_3498651 := by
    simpa [prefixWord, tailWord_3498651, baseEnd_3498651] using wordTrace_append hprefix tailTrace_3498651
  have hstable : (prefixWord ++ tailWord_3498651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498651).length < 2 ^ (prefixWord ++ tailWord_3498651).sum := by decide
  have hdescent : baseEnd_3498651 < baseStart_3498651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498653 : List Nat := [1, 4, 2, 1, 1, 1, 5, 7]
def baseStart_3498653 : Nat := 118140960795 + 3498653 * 2 ^ 59
def prefixEnd_3498653 : Nat := 4983230072969 + 3 ^ 40 * 3498653 * 2
def baseEnd_3498653 : Nat := 133073380169985573166481

theorem tailTrace_3498653 : CollatzResearch.WordTrace tailWord_3498653 prefixEnd_3498653 133073380169985573166481 := by
  unfold tailWord_3498653
  simp only [CollatzResearch.WordTrace]
  refine ⟨127606358193985178206324613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85070905462656785470883075 127606358193985178206324613)
  ·
    refine ⟨23926192161372220913685865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127606358193985178206324613 23926192161372220913685865)
    ·
      refine ⟨17944644121029165685264399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23926192161372220913685865 17944644121029165685264399)
      ·
        refine ⟨26916966181543748527896599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17944644121029165685264399 26916966181543748527896599)
        ·
          refine ⟨40375449272315622791844899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26916966181543748527896599 40375449272315622791844899)
          ·
            refine ⟨60563173908473434187767349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40375449272315622791844899 60563173908473434187767349)
            ·
              refine ⟨5677797553919384455103189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60563173908473434187767349 5677797553919384455103189)
              ·
                refine ⟨133073380169985573166481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5677797553919384455103189 133073380169985573166481)
                ·
                  rfl

theorem cell22_3498653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 7].length) (baseStart_3498653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498653 prefixEnd_3498653 := by exact prefixLift 3498653
  have htrace : WordTrace (prefixWord ++ tailWord_3498653) baseStart_3498653 baseEnd_3498653 := by
    simpa [prefixWord, tailWord_3498653, baseEnd_3498653] using wordTrace_append hprefix tailTrace_3498653
  have hstable : (prefixWord ++ tailWord_3498653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498653).length < 2 ^ (prefixWord ++ tailWord_3498653).sum := by decide
  have hdescent : baseEnd_3498653 < baseStart_3498653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498678 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3498678 : Nat := 118140960795 + 3498678 * 2 ^ 59
def prefixEnd_3498678 : Nat := 4983230072969 + 3 ^ 40 * 3498678 * 2
def baseEnd_3498678 : Nat := 1197668979540778426623253

theorem tailTrace_3498678 : CollatzResearch.WordTrace tailWord_3498678 prefixEnd_3498678 1197668979540778426623253 := by
  unfold tailWord_3498678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7975454376180912967249043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85071513345929738317323125 7975454376180912967249043)
  ·
    refine ⟨11963181564271369450873565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7975454376180912967249043 11963181564271369450873565)
    ·
      refine ⟨4486193086601763544077587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11963181564271369450873565 4486193086601763544077587)
      ·
        refine ⟨6729289629902645316116381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486193086601763544077587 6729289629902645316116381)
        ·
          refine ⟨2523483611213491993543643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6729289629902645316116381 2523483611213491993543643)
          ·
            refine ⟨3785225416820237990315465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523483611213491993543643 3785225416820237990315465)
            ·
              refine ⟨2838919062615178492736599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785225416820237990315465 2838919062615178492736599)
              ·
                refine ⟨4258378593922767739104899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838919062615178492736599 4258378593922767739104899)
                ·
                  refine ⟨6387567890884151608657349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258378593922767739104899 6387567890884151608657349)
                  ·
                    refine ⟨1197668979540778426623253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387567890884151608657349 1197668979540778426623253)
                    ·
                      rfl

theorem cell22_3498678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3498678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498678 prefixEnd_3498678 := by exact prefixLift 3498678
  have htrace : WordTrace (prefixWord ++ tailWord_3498678) baseStart_3498678 baseEnd_3498678 := by
    simpa [prefixWord, tailWord_3498678, baseEnd_3498678] using wordTrace_append hprefix tailTrace_3498678
  have hstable : (prefixWord ++ tailWord_3498678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498678).length < 2 ^ (prefixWord ++ tailWord_3498678).sum := by decide
  have hdescent : baseEnd_3498678 < baseStart_3498678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498702 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_3498702 : Nat := 118140960795 + 3498702 * 2 ^ 59
def prefixEnd_3498702 : Nat := 4983230072969 + 3 ^ 40 * 3498702 * 2
def baseEnd_3498702 : Nat := 1197677195231250364023179

theorem tailTrace_3498702 : CollatzResearch.WordTrace tailWord_3498702 prefixEnd_3498702 1197677195231250364023179 := by
  unfold tailWord_3498702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15951018171350957446857295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85072096913871773049905573 15951018171350957446857295)
  ·
    refine ⟨23926527257026436170285943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15951018171350957446857295 23926527257026436170285943)
    ·
      refine ⟨35889790885539654255428915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23926527257026436170285943 35889790885539654255428915)
      ·
        refine ⟨53834686328309481383143373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35889790885539654255428915 53834686328309481383143373)
        ·
          refine ⟨20188007373116055518678765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53834686328309481383143373 20188007373116055518678765)
          ·
            refine ⟨7570502764918520819504537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20188007373116055518678765 7570502764918520819504537)
            ·
              refine ⟨5677877073688890614628403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7570502764918520819504537 5677877073688890614628403)
              ·
                refine ⟨8516815610533335921942605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677877073688890614628403 8516815610533335921942605)
                ·
                  refine ⟨3193805853950000970728477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8516815610533335921942605 3193805853950000970728477)
                  ·
                    refine ⟨1197677195231250364023179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193805853950000970728477 1197677195231250364023179)
                    ·
                      rfl

theorem cell22_3498702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_3498702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498702 prefixEnd_3498702 := by exact prefixLift 3498702
  have htrace : WordTrace (prefixWord ++ tailWord_3498702) baseStart_3498702 baseEnd_3498702 := by
    simpa [prefixWord, tailWord_3498702, baseEnd_3498702] using wordTrace_append hprefix tailTrace_3498702
  have hstable : (prefixWord ++ tailWord_3498702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498702).length < 2 ^ (prefixWord ++ tailWord_3498702).sum := by decide
  have hdescent : baseEnd_3498702 < baseStart_3498702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498713 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_3498713 : Nat := 118140960795 + 3498713 * 2 ^ 59
def prefixEnd_3498713 : Nat := 4983230072969 + 3 ^ 40 * 3498713 * 2
def baseEnd_3498713 : Nat := 1197680960756050001998145

theorem tailTrace_3498713 : CollatzResearch.WordTrace tailWord_3498713 prefixEnd_3498713 1197680960756050001998145 := by
  unfold tailWord_3498713
  simp only [CollatzResearch.WordTrace]
  refine ⟨127608546573767808453508793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85072364382511872302339195 127608546573767808453508793)
  ·
    refine ⟨95706409930325856340131595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127608546573767808453508793 95706409930325856340131595)
    ·
      refine ⟨143559614895488784510197393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95706409930325856340131595 143559614895488784510197393)
      ·
        refine ⟨107669711171616588382648045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143559614895488784510197393 107669711171616588382648045)
        ·
          refine ⟨40376141689356220643493017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107669711171616588382648045 40376141689356220643493017)
          ·
            refine ⟨30282106267017165482619763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40376141689356220643493017 30282106267017165482619763)
            ·
              refine ⟨45423159400525748223929645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30282106267017165482619763 45423159400525748223929645)
              ·
                refine ⟨17033684775197155583973617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45423159400525748223929645 17033684775197155583973617)
                ·
                  refine ⟨12775263581397866687980213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17033684775197155583973617 12775263581397866687980213)
                  ·
                    refine ⟨1197680960756050001998145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12775263581397866687980213 1197680960756050001998145)
                    ·
                      rfl

theorem cell22_3498713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_3498713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498713 prefixEnd_3498713 := by exact prefixLift 3498713
  have htrace : WordTrace (prefixWord ++ tailWord_3498713) baseStart_3498713 baseEnd_3498713 := by
    simpa [prefixWord, tailWord_3498713, baseEnd_3498713] using wordTrace_append hprefix tailTrace_3498713
  have hstable : (prefixWord ++ tailWord_3498713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498713).length < 2 ^ (prefixWord ++ tailWord_3498713).sum := by decide
  have hdescent : baseEnd_3498713 < baseStart_3498713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498760 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 6]
def baseStart_3498760 : Nat := 118140960795 + 3498760 * 2 ^ 59
def prefixEnd_3498760 : Nat := 4983230072969 + 3 ^ 40 * 3498760 * 2
def baseEnd_3498760 : Nat := 399232349938852515357667

theorem tailTrace_3498760 : CollatzResearch.WordTrace tailWord_3498760 prefixEnd_3498760 399232349938852515357667 := by
  unfold tailWord_3498760
  simp only [CollatzResearch.WordTrace]
  refine ⟨63805130402298767740234867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85073507203065023653646489 63805130402298767740234867)
  ·
    refine ⟨95707695603448151610352301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63805130402298767740234867 95707695603448151610352301)
    ·
      refine ⟨35890385851293056853882113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95707695603448151610352301 35890385851293056853882113)
      ·
        refine ⟨26917789388469792640411585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35890385851293056853882113 26917789388469792640411585)
        ·
          refine ⟨20188342041352344480308689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26917789388469792640411585 20188342041352344480308689)
          ·
            refine ⟨15141256531014258360231517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20188342041352344480308689 15141256531014258360231517)
            ·
              refine ⟨5677971199130346885086819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15141256531014258360231517 5677971199130346885086819)
              ·
                refine ⟨8516956798695520327630229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677971199130346885086819 8516956798695520327630229)
                ·
                  refine ⟨399232349938852515357667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8516956798695520327630229 399232349938852515357667)
                  ·
                    rfl

theorem cell22_3498760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_3498760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498760 prefixEnd_3498760 := by exact prefixLift 3498760
  have htrace : WordTrace (prefixWord ++ tailWord_3498760) baseStart_3498760 baseEnd_3498760 := by
    simpa [prefixWord, tailWord_3498760, baseEnd_3498760] using wordTrace_append hprefix tailTrace_3498760
  have hstable : (prefixWord ++ tailWord_3498760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498760).length < 2 ^ (prefixWord ++ tailWord_3498760).sum := by decide
  have hdescent : baseEnd_3498760 < baseStart_3498760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498837 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_3498837 : Nat := 118140960795 + 3498837 * 2 ^ 59
def prefixEnd_3498837 : Nat := 4983230072969 + 3 ^ 40 * 3498837 * 2
def baseEnd_3498837 : Nat := 1197723408490155011897765

theorem tailTrace_3498837 : CollatzResearch.WordTrace tailWord_3498837 prefixEnd_3498837 1197723408490155011897765 := by
  unfold tailWord_3498837
  simp only [CollatzResearch.WordTrace]
  refine ⟨127613069225318577631022765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85075379483545718420681843 127613069225318577631022765)
  ·
    refine ⟨47854900959494466611633537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127613069225318577631022765 47854900959494466611633537)
    ·
      refine ⟨35891175719620849958725153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47854900959494466611633537 35891175719620849958725153)
      ·
        refine ⟨26918381789715637469043865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35891175719620849958725153 26918381789715637469043865)
        ·
          refine ⟨20188786342286728101782899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26918381789715637469043865 20188786342286728101782899)
          ·
            refine ⟨30283179513430092152674349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20188786342286728101782899 30283179513430092152674349)
            ·
              refine ⟨11356192317536284557252881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30283179513430092152674349 11356192317536284557252881)
              ·
                refine ⟨8517144238152213417939661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11356192317536284557252881 8517144238152213417939661)
                ·
                  refine ⟨3193929089307080031727373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8517144238152213417939661 3193929089307080031727373)
                  ·
                    refine ⟨1197723408490155011897765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3193929089307080031727373 1197723408490155011897765)
                    ·
                      rfl

theorem cell22_3498837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_3498837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498837 prefixEnd_3498837 := by exact prefixLift 3498837
  have htrace : WordTrace (prefixWord ++ tailWord_3498837) baseStart_3498837 baseEnd_3498837 := by
    simpa [prefixWord, tailWord_3498837, baseEnd_3498837] using wordTrace_append hprefix tailTrace_3498837
  have hstable : (prefixWord ++ tailWord_3498837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498837).length < 2 ^ (prefixWord ++ tailWord_3498837).sum := by decide
  have hdescent : baseEnd_3498837 < baseStart_3498837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498865 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_3498865 : Nat := 118140960795 + 3498865 * 2 ^ 59
def prefixEnd_3498865 : Nat := 4983230072969 + 3 ^ 40 * 3498865 * 2
def baseEnd_3498865 : Nat := 1197732993462372272197679

theorem tailTrace_3498865 : CollatzResearch.WordTrace tailWord_3498865 prefixEnd_3498865 1197732993462372272197679 := by
  unfold tailWord_3498865
  simp only [CollatzResearch.WordTrace]
  refine ⟨127614090469217138413042049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85076060312811425608694699 127614090469217138413042049)
  ·
    refine ⟨95710567851912853809781537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127614090469217138413042049 95710567851912853809781537)
    ·
      refine ⟨71782925888934640357336153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95710567851912853809781537 71782925888934640357336153)
      ·
        refine ⟨53837194416700980268002115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71782925888934640357336153 53837194416700980268002115)
        ·
          refine ⟨80755791625051470402003173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53837194416700980268002115 80755791625051470402003173)
          ·
            refine ⟨15141710929697150700375595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80755791625051470402003173 15141710929697150700375595)
            ·
              refine ⟨22712566394545726050563393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15141710929697150700375595 22712566394545726050563393)
              ·
                refine ⟨17034424795909294537922545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22712566394545726050563393 17034424795909294537922545)
                ·
                  refine ⟨12775818596931970903441909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17034424795909294537922545 12775818596931970903441909)
                  ·
                    refine ⟨1197732993462372272197679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12775818596931970903441909 1197732993462372272197679)
                    ·
                      rfl

theorem cell22_3498865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_3498865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498865 prefixEnd_3498865 := by exact prefixLift 3498865
  have htrace : WordTrace (prefixWord ++ tailWord_3498865) baseStart_3498865 baseEnd_3498865 := by
    simpa [prefixWord, tailWord_3498865, baseEnd_3498865] using wordTrace_append hprefix tailTrace_3498865
  have hstable : (prefixWord ++ tailWord_3498865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498865).length < 2 ^ (prefixWord ++ tailWord_3498865).sum := by decide
  have hdescent : baseEnd_3498865 < baseStart_3498865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498880 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_3498880 : Nat := 118140960795 + 3498880 * 2 ^ 59
def prefixEnd_3498880 : Nat := 4983230072969 + 3 ^ 40 * 3498880 * 2
def baseEnd_3498880 : Nat := 1197738128268917233072633

theorem tailTrace_3498880 : CollatzResearch.WordTrace tailWord_3498880 prefixEnd_3498880 1197738128268917233072633 := by
  unfold tailWord_3498880
  simp only [CollatzResearch.WordTrace]
  refine ⟨63807318782081397987419047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85076425042775197316558729 63807318782081397987419047)
  ·
    refine ⟨95710978173122096981128571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63807318782081397987419047 95710978173122096981128571)
    ·
      refine ⟨143566467259683145471692857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95710978173122096981128571 143566467259683145471692857)
      ·
        refine ⟨107674850444762359103769643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143566467259683145471692857 107674850444762359103769643)
        ·
          refine ⟨161512275667143538655654465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107674850444762359103769643 161512275667143538655654465)
          ·
            refine ⟨121134206750357653991740849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161512275667143538655654465 121134206750357653991740849)
            ·
              refine ⟨90850655062768240493805637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121134206750357653991740849 90850655062768240493805637)
              ·
                refine ⟨17034497824269045092588557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90850655062768240493805637 17034497824269045092588557)
                ·
                  refine ⟨6387936684100891909720709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17034497824269045092588557 6387936684100891909720709)
                  ·
                    refine ⟨1197738128268917233072633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387936684100891909720709 1197738128268917233072633)
                    ·
                      rfl

theorem cell22_3498880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_3498880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498880 prefixEnd_3498880 := by exact prefixLift 3498880
  have htrace : WordTrace (prefixWord ++ tailWord_3498880) baseStart_3498880 baseEnd_3498880 := by
    simpa [prefixWord, tailWord_3498880, baseEnd_3498880] using wordTrace_append hprefix tailTrace_3498880
  have hstable : (prefixWord ++ tailWord_3498880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498880).length < 2 ^ (prefixWord ++ tailWord_3498880).sum := by decide
  have hdescent : baseEnd_3498880 < baseStart_3498880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498914 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3498914 : Nat := 118140960795 + 3498914 * 2 ^ 59
def prefixEnd_3498914 : Nat := 4983230072969 + 3 ^ 40 * 3498914 * 2
def baseEnd_3498914 : Nat := 1197749767163752477722529

theorem tailTrace_3498914 : CollatzResearch.WordTrace tailWord_3498914 prefixEnd_3498914 1197749767163752477722529 := by
  unfold tailWord_3498914
  simp only [CollatzResearch.WordTrace]
  refine ⟨31903969411509904945393949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85077251764026413187717197 31903969411509904945393949)
  ·
    refine ⟨11963988529316214354522731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31903969411509904945393949 11963988529316214354522731)
    ·
      refine ⟨17945982793974321531784097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11963988529316214354522731 17945982793974321531784097)
      ·
        refine ⟨13459487095480741148838073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17945982793974321531784097 13459487095480741148838073)
        ·
          refine ⟨10094615321610555861628555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13459487095480741148838073 10094615321610555861628555)
          ·
            refine ⟨15141922982415833792442833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10094615321610555861628555 15141922982415833792442833)
            ·
              refine ⟨11356442236811875344332125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15141922982415833792442833 11356442236811875344332125)
              ·
                refine ⟨4258665838804453254124547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11356442236811875344332125 4258665838804453254124547)
                ·
                  refine ⟨6387998758206679881186821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258665838804453254124547 6387998758206679881186821)
                  ·
                    refine ⟨1197749767163752477722529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387998758206679881186821 1197749767163752477722529)
                    ·
                      rfl

theorem cell22_3498914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3498914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498914 prefixEnd_3498914 := by exact prefixLift 3498914
  have htrace : WordTrace (prefixWord ++ tailWord_3498914) baseStart_3498914 baseEnd_3498914 := by
    simpa [prefixWord, tailWord_3498914, baseEnd_3498914] using wordTrace_append hprefix tailTrace_3498914
  have hstable : (prefixWord ++ tailWord_3498914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498914).length < 2 ^ (prefixWord ++ tailWord_3498914).sum := by decide
  have hdescent : baseEnd_3498914 < baseStart_3498914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498929 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 6]
def baseStart_3498929 : Nat := 118140960795 + 3498929 * 2 ^ 59
def prefixEnd_3498929 : Nat := 4983230072969 + 3 ^ 40 * 3498929 * 2
def baseEnd_3498929 : Nat := 399251633990099146199161

theorem tailTrace_3498929 : CollatzResearch.WordTrace tailWord_3498929 prefixEnd_3498929 399251633990099146199161 := by
  unfold tailWord_3498929
  simp only [CollatzResearch.WordTrace]
  refine ⟨127616424740985277343371841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85077616493990184895581227 127616424740985277343371841)
  ·
    refine ⟨95712318555738958007528881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127616424740985277343371841 95712318555738958007528881)
    ·
      refine ⟨71784238916804218505646661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95712318555738958007528881 71784238916804218505646661)
      ·
        refine ⟨13459544796900790969808749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71784238916804218505646661 13459544796900790969808749)
        ·
          refine ⟨5047329298837796613678281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13459544796900790969808749 5047329298837796613678281)
          ·
            refine ⟨3785496974128347460258711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5047329298837796613678281 3785496974128347460258711)
            ·
              refine ⟨5678245461192521190388067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785496974128347460258711 5678245461192521190388067)
              ·
                refine ⟨8517368191788781785582101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678245461192521190388067 8517368191788781785582101)
                ·
                  refine ⟨399251633990099146199161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8517368191788781785582101 399251633990099146199161)
                  ·
                    rfl

theorem cell22_3498929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_3498929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498929 prefixEnd_3498929 := by exact prefixLift 3498929
  have htrace : WordTrace (prefixWord ++ tailWord_3498929) baseStart_3498929 baseEnd_3498929 := by
    simpa [prefixWord, tailWord_3498929, baseEnd_3498929] using wordTrace_append hprefix tailTrace_3498929
  have hstable : (prefixWord ++ tailWord_3498929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498929).length < 2 ^ (prefixWord ++ tailWord_3498929).sum := by decide
  have hdescent : baseEnd_3498929 < baseStart_3498929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498942 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_3498942 : Nat := 118140960795 + 3498942 * 2 ^ 59
def prefixEnd_3498942 : Nat := 4983230072969 + 3 ^ 40 * 3498942 * 2
def baseEnd_3498942 : Nat := 1197759352135969738022443

theorem tailTrace_3498942 : CollatzResearch.WordTrace tailWord_3498942 prefixEnd_3498942 1197759352135969738022443 := by
  unfold tailWord_3498942
  simp only [CollatzResearch.WordTrace]
  refine ⟨15952112361242272570449385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85077932593292120375730053 15952112361242272570449385)
  ·
    refine ⟨11964084270931704427837039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15952112361242272570449385 11964084270931704427837039)
    ·
      refine ⟨17946126406397556641755559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11964084270931704427837039 17946126406397556641755559)
      ·
        refine ⟨26919189609596334962633339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17946126406397556641755559 26919189609596334962633339)
        ·
          refine ⟨40378784414394502443950009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26919189609596334962633339 40378784414394502443950009)
          ·
            refine ⟨30284088310795876832962507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40378784414394502443950009 30284088310795876832962507)
            ·
              refine ⟨45426132466193815249443761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30284088310795876832962507 45426132466193815249443761)
              ·
                refine ⟨34069599349645361437082821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45426132466193815249443761 34069599349645361437082821)
                ·
                  refine ⟨6388049878058505269453029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34069599349645361437082821 6388049878058505269453029)
                  ·
                    refine ⟨1197759352135969738022443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6388049878058505269453029 1197759352135969738022443)
                    ·
                      rfl

theorem cell22_3498942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_3498942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498942 prefixEnd_3498942 := by exact prefixLift 3498942
  have htrace : WordTrace (prefixWord ++ tailWord_3498942) baseStart_3498942 baseEnd_3498942 := by
    simpa [prefixWord, tailWord_3498942, baseEnd_3498942] using wordTrace_append hprefix tailTrace_3498942
  have hstable : (prefixWord ++ tailWord_3498942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498942).length < 2 ^ (prefixWord ++ tailWord_3498942).sum := by decide
  have hdescent : baseEnd_3498942 < baseStart_3498942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498944 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 2, 3]
def baseStart_3498944 : Nat := 118140960795 + 3498944 * 2 ^ 59
def prefixEnd_3498944 : Nat := 4983230072969 + 3 ^ 40 * 3498944 * 2
def baseEnd_3498944 : Nat := 1197760036776842399472437

theorem tailTrace_3498944 : CollatzResearch.WordTrace tailWord_3498944 prefixEnd_3498944 1197760036776842399472437 := by
  unfold tailWord_3498944
  simp only [CollatzResearch.WordTrace]
  refine ⟨63808485917965467452583943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85077981223953956603445257 63808485917965467452583943)
  ·
    refine ⟨95712728876948201178875915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63808485917965467452583943 95712728876948201178875915)
    ·
      refine ⟨143569093315422301768313873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95712728876948201178875915 143569093315422301768313873)
      ·
        refine ⟨107676819986566726326235405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143569093315422301768313873 107676819986566726326235405)
        ·
          refine ⟨40378807494962522372338277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107676819986566726326235405 40378807494962522372338277)
          ·
            refine ⟨7571026405305472944813427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40378807494962522372338277 7571026405305472944813427)
            ·
              refine ⟨11356539607958209417220141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571026405305472944813427 11356539607958209417220141)
              ·
                refine ⟨4258702352984328531457553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11356539607958209417220141 4258702352984328531457553)
                ·
                  refine ⟨3194026764738246398593165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258702352984328531457553 3194026764738246398593165)
                  ·
                    refine ⟨1197760036776842399472437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194026764738246398593165 1197760036776842399472437)
                    ·
                      rfl

theorem cell22_3498944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_3498944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498944 prefixEnd_3498944 := by exact prefixLift 3498944
  have htrace : WordTrace (prefixWord ++ tailWord_3498944) baseStart_3498944 baseEnd_3498944 := by
    simpa [prefixWord, tailWord_3498944, baseEnd_3498944] using wordTrace_append hprefix tailTrace_3498944
  have hstable : (prefixWord ++ tailWord_3498944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498944).length < 2 ^ (prefixWord ++ tailWord_3498944).sum := by decide
  have hdescent : baseEnd_3498944 < baseStart_3498944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498948 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3498948 : Nat := 118140960795 + 3498948 * 2 ^ 59
def prefixEnd_3498948 : Nat := 4983230072969 + 3 ^ 40 * 3498948 * 2
def baseEnd_3498948 : Nat := 1197761406058587722372425

theorem tailTrace_3498948 : CollatzResearch.WordTrace tailWord_3498948 prefixEnd_3498948 1197761406058587722372425 := by
  unfold tailWord_3498948
  simp only [CollatzResearch.WordTrace]
  refine ⟨63808558863958221794156749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85078078485277629058875665 63808558863958221794156749)
  ·
    refine ⟨23928209573984333172808781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63808558863958221794156749 23928209573984333172808781)
    ·
      refine ⟨8973078590244124939803293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23928209573984333172808781 8973078590244124939803293)
      ·
        refine ⟨3364904471341546852426235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8973078590244124939803293 3364904471341546852426235)
        ·
          refine ⟨5047356707012320278639353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3364904471341546852426235 5047356707012320278639353)
          ·
            refine ⟨3785517530259240208979515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5047356707012320278639353 3785517530259240208979515)
            ·
              refine ⟨5678276295388860313469273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785517530259240208979515 5678276295388860313469273)
              ·
                refine ⟨4258707221541645235101955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5678276295388860313469273 4258707221541645235101955)
                ·
                  refine ⟨6388060832312467852652933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258707221541645235101955 6388060832312467852652933)
                  ·
                    refine ⟨1197761406058587722372425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6388060832312467852652933 1197761406058587722372425)
                    ·
                      rfl

theorem cell22_3498948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3498948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498948 prefixEnd_3498948 := by exact prefixLift 3498948
  have htrace : WordTrace (prefixWord ++ tailWord_3498948) baseStart_3498948 baseEnd_3498948 := by
    simpa [prefixWord, tailWord_3498948, baseEnd_3498948] using wordTrace_append hprefix tailTrace_3498948
  have hstable : (prefixWord ++ tailWord_3498948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498948).length < 2 ^ (prefixWord ++ tailWord_3498948).sum := by decide
  have hdescent : baseEnd_3498948 < baseStart_3498948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498978 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3498978 : Nat := 118140960795 + 3498978 * 2 ^ 59
def prefixEnd_3498978 : Nat := 4983230072969 + 3 ^ 40 * 3498978 * 2
def baseEnd_3498978 : Nat := 1197771675671677644122333

theorem tailTrace_3498978 : CollatzResearch.WordTrace tailWord_3498978 prefixEnd_3498978 1197771675671677644122333 := by
  unfold tailWord_3498978
  simp only [CollatzResearch.WordTrace]
  refine ⟨31904552979451939677976397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85078807945205172474603725 31904552979451939677976397)
  ·
    refine ⟨11964207367294477379241149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31904552979451939677976397 11964207367294477379241149)
    ·
      refine ⟨4486577762735429017215431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11964207367294477379241149 4486577762735429017215431)
      ·
        refine ⟨6729866644103143525823147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486577762735429017215431 6729866644103143525823147)
        ·
          refine ⟨10094799966154715288734721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6729866644103143525823147 10094799966154715288734721)
          ·
            refine ⟨7571099974616036466551041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10094799966154715288734721 7571099974616036466551041)
            ·
              refine ⟨5678324980962027349913281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7571099974616036466551041 5678324980962027349913281)
              ·
                refine ⟨4258743735721520512434961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5678324980962027349913281 4258743735721520512434961)
                ·
                  refine ⟨3194057801791140384326221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258743735721520512434961 3194057801791140384326221)
                  ·
                    refine ⟨1197771675671677644122333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194057801791140384326221 1197771675671677644122333)
                    ·
                      rfl

theorem cell22_3498978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3498978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3498978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3498978 prefixEnd_3498978 := by exact prefixLift 3498978
  have htrace : WordTrace (prefixWord ++ tailWord_3498978) baseStart_3498978 baseEnd_3498978 := by
    simpa [prefixWord, tailWord_3498978, baseEnd_3498978] using wordTrace_append hprefix tailTrace_3498978
  have hstable : (prefixWord ++ tailWord_3498978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498978).length < 2 ^ (prefixWord ++ tailWord_3498978).sum := by decide
  have hdescent : baseEnd_3498978 < baseStart_3498978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499010 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3499010 : Nat := 118140960795 + 3499010 * 2 ^ 59
def prefixEnd_3499010 : Nat := 4983230072969 + 3 ^ 40 * 3499010 * 2
def baseEnd_3499010 : Nat := 1197782629925640227322235

theorem tailTrace_3499010 : CollatzResearch.WordTrace tailWord_3499010 prefixEnd_3499010 1197782629925640227322235 := by
  unfold tailWord_3499010
  simp only [CollatzResearch.WordTrace]
  refine ⟨31904844763422957044267621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85079586035794552118046989 31904844763422957044267621)
  ·
    refine ⟨5982158393141804445800179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31904844763422957044267621 5982158393141804445800179)
    ·
      refine ⟨8973237589712706668700269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5982158393141804445800179 8973237589712706668700269)
      ·
        refine ⟨3364964096142265000762601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8973237589712706668700269 3364964096142265000762601)
        ·
          refine ⟨2523723072106698750571951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3364964096142265000762601 2523723072106698750571951)
          ·
            refine ⟨3785584608160048125857927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523723072106698750571951 3785584608160048125857927)
            ·
              refine ⟨5678376912240072188786891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785584608160048125857927 5678376912240072188786891)
              ·
                refine ⟨8517565368360108283180337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678376912240072188786891 8517565368360108283180337)
                ·
                  refine ⟨6388174026270081212385253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8517565368360108283180337 6388174026270081212385253)
                  ·
                    refine ⟨1197782629925640227322235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6388174026270081212385253 1197782629925640227322235)
                    ·
                      rfl

theorem cell22_3499010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3499010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499010 prefixEnd_3499010 := by exact prefixLift 3499010
  have htrace : WordTrace (prefixWord ++ tailWord_3499010) baseStart_3499010 baseEnd_3499010 := by
    simpa [prefixWord, tailWord_3499010, baseEnd_3499010] using wordTrace_append hprefix tailTrace_3499010
  have hstable : (prefixWord ++ tailWord_3499010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499010).length < 2 ^ (prefixWord ++ tailWord_3499010).sum := by decide
  have hdescent : baseEnd_3499010 < baseStart_3499010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499036 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 5]
def baseStart_3499036 : Nat := 118140960795 + 3499036 * 2 ^ 59
def prefixEnd_3499036 : Nat := 4983230072969 + 3 ^ 40 * 3499036 * 2
def baseEnd_3499036 : Nat := 399263843418994942057385

theorem tailTrace_3499036 : CollatzResearch.WordTrace tailWord_3499036 prefixEnd_3499036 399263843418994942057385 := by
  unfold tailWord_3499036
  simp only [CollatzResearch.WordTrace]
  refine ⟨63810163675798817308758481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85080218234398423078344641 63810163675798817308758481)
  ·
    refine ⟨47857622756849112981568861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63810163675798817308758481 47857622756849112981568861)
    ·
      refine ⟨17946608533818417368088323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47857622756849112981568861 17946608533818417368088323)
      ·
        refine ⟨26919912800727626052132485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17946608533818417368088323 26919912800727626052132485)
        ·
          refine ⟨5047483650136429884774841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26919912800727626052132485 5047483650136429884774841)
          ·
            refine ⟨3785612737602322413581131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5047483650136429884774841 3785612737602322413581131)
            ·
              refine ⟨5678419106403483620371697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785612737602322413581131 5678419106403483620371697)
              ·
                refine ⟨4258814329802612715278773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5678419106403483620371697 4258814329802612715278773)
                ·
                  refine ⟨399263843418994942057385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4258814329802612715278773 399263843418994942057385)
                  ·
                    rfl

theorem cell22_3499036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_3499036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499036 prefixEnd_3499036 := by exact prefixLift 3499036
  have htrace : WordTrace (prefixWord ++ tailWord_3499036) baseStart_3499036 baseEnd_3499036 := by
    simpa [prefixWord, tailWord_3499036, baseEnd_3499036] using wordTrace_append hprefix tailTrace_3499036
  have hstable : (prefixWord ++ tailWord_3499036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499036).length < 2 ^ (prefixWord ++ tailWord_3499036).sum := by decide
  have hdescent : baseEnd_3499036 < baseStart_3499036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499077 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_3499077 : Nat := 118140960795 + 3499077 * 2 ^ 59
def prefixEnd_3499077 : Nat := 4983230072969 + 3 ^ 40 * 3499077 * 2
def baseEnd_3499077 : Nat := 1197805565394874385897029

theorem tailTrace_3499077 : CollatzResearch.WordTrace tailWord_3499077 prefixEnd_3499077 1197805565394874385897029 := by
  unfold tailWord_3499077
  simp only [CollatzResearch.WordTrace]
  refine ⟨127621822744449098619759485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85081215162966065746506323 127621822744449098619759485)
  ·
    refine ⟨47858183529168411982409807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127621822744449098619759485 47858183529168411982409807)
    ·
      refine ⟨71787275293752617973614711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47858183529168411982409807 71787275293752617973614711)
      ·
        refine ⟨107680912940628926960422067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71787275293752617973614711 107680912940628926960422067)
        ·
          refine ⟨161521369410943390440633101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107680912940628926960422067 161521369410943390440633101)
          ·
            refine ⟨60570513529103771415237413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161521369410943390440633101 60570513529103771415237413)
            ·
              refine ⟨11356971286706957140357015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60570513529103771415237413 11356971286706957140357015)
              ·
                refine ⟨17035456930060435710535523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11356971286706957140357015 17035456930060435710535523)
                ·
                  refine ⟨25553185395090653565803285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17035456930060435710535523 25553185395090653565803285)
                  ·
                    refine ⟨1197805565394874385897029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25553185395090653565803285 1197805565394874385897029)
                    ·
                      rfl

theorem cell22_3499077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_3499077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499077 prefixEnd_3499077 := by exact prefixLift 3499077
  have htrace : WordTrace (prefixWord ++ tailWord_3499077) baseStart_3499077 baseEnd_3499077 := by
    simpa [prefixWord, tailWord_3499077, baseEnd_3499077] using wordTrace_append hprefix tailTrace_3499077
  have hstable : (prefixWord ++ tailWord_3499077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499077).length < 2 ^ (prefixWord ++ tailWord_3499077).sum := by decide
  have hdescent : baseEnd_3499077 < baseStart_3499077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499079 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 4, 3]
def baseStart_3499079 : Nat := 118140960795 + 3499079 * 2 ^ 59
def prefixEnd_3499079 : Nat := 4983230072969 + 3 ^ 40 * 3499079 * 2
def baseEnd_3499079 : Nat := 1197806250035747047347023

theorem tailTrace_3499079 : CollatzResearch.WordTrace tailWord_3499079 prefixEnd_3499079 1197806250035747047347023 := by
  unfold tailWord_3499079
  simp only [CollatzResearch.WordTrace]
  refine ⟨127621895690441852961332291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85081263793627901974221527 127621895690441852961332291)
  ·
    refine ⟨191432843535662779441998437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127621895690441852961332291 191432843535662779441998437)
    ·
      refine ⟨35893658162936771145374707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191432843535662779441998437 35893658162936771145374707)
      ·
        refine ⟨53840487244405156718062061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35893658162936771145374707 53840487244405156718062061)
        ·
          refine ⟨20190182716651933769273273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53840487244405156718062061 20190182716651933769273273)
          ·
            refine ⟨15142637037488950326954955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20190182716651933769273273 15142637037488950326954955)
            ·
              refine ⟨22713955556233425490432433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15142637037488950326954955 22713955556233425490432433)
              ·
                refine ⟨17035466667175069117824325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22713955556233425490432433 17035466667175069117824325)
                ·
                  refine ⟨3194150000095325459592061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17035466667175069117824325 3194150000095325459592061)
                  ·
                    refine ⟨1197806250035747047347023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194150000095325459592061 1197806250035747047347023)
                    ·
                      rfl

theorem cell22_3499079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_3499079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499079 prefixEnd_3499079 := by exact prefixLift 3499079
  have htrace : WordTrace (prefixWord ++ tailWord_3499079) baseStart_3499079 baseEnd_3499079 := by
    simpa [prefixWord, tailWord_3499079, baseEnd_3499079] using wordTrace_append hprefix tailTrace_3499079
  have hstable : (prefixWord ++ tailWord_3499079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499079).length < 2 ^ (prefixWord ++ tailWord_3499079).sum := by decide
  have hdescent : baseEnd_3499079 < baseStart_3499079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499092 : List Nat := [2, 4, 1, 1, 1, 1, 12]
def baseStart_3499092 : Nat := 118140960795 + 3499092 * 2 ^ 59
def prefixEnd_3499092 : Nat := 4983230072969 + 3 ^ 40 * 3499092 * 2
def baseEnd_3499092 : Nat := 44363359266719235065629

theorem tailTrace_3499092 : CollatzResearch.WordTrace tailWord_3499092 prefixEnd_3499092 44363359266719235065629 := by
  unfold tailWord_3499092
  simp only [CollatzResearch.WordTrace]
  refine ⟨63811184919697378090777765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85081579892929837454370353 63811184919697378090777765)
  ·
    refine ⟨11964597172443258392020831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63811184919697378090777765 11964597172443258392020831)
    ·
      refine ⟨17946895758664887588031247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11964597172443258392020831 17946895758664887588031247)
      ·
        refine ⟨26920343637997331382046871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17946895758664887588031247 26920343637997331382046871)
        ·
          refine ⟨40380515456995997073070307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26920343637997331382046871 40380515456995997073070307)
          ·
            refine ⟨60570773185493995609605461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40380515456995997073070307 60570773185493995609605461)
            ·
              refine ⟨44363359266719235065629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 60570773185493995609605461 44363359266719235065629)
              ·
                rfl

theorem cell22_3499092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 12].length) (baseStart_3499092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499092 prefixEnd_3499092 := by exact prefixLift 3499092
  have htrace : WordTrace (prefixWord ++ tailWord_3499092) baseStart_3499092 baseEnd_3499092 := by
    simpa [prefixWord, tailWord_3499092, baseEnd_3499092] using wordTrace_append hprefix tailTrace_3499092
  have hstable : (prefixWord ++ tailWord_3499092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499092).length < 2 ^ (prefixWord ++ tailWord_3499092).sum := by decide
  have hdescent : baseEnd_3499092 < baseStart_3499092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499113 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 2, 3]
def baseStart_3499113 : Nat := 118140960795 + 3499113 * 2 ^ 59
def prefixEnd_3499113 : Nat := 4983230072969 + 3 ^ 40 * 3499113 * 2
def baseEnd_3499113 : Nat := 1197817888930582291996919

theorem tailTrace_3499113 : CollatzResearch.WordTrace tailWord_3499113 prefixEnd_3499113 1197817888930582291996919 := by
  unfold tailWord_3499113
  simp only [CollatzResearch.WordTrace]
  refine ⟨127623135772318676768069993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85082090514879117845379995 127623135772318676768069993)
  ·
    refine ⟨95717351829239007576052495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127623135772318676768069993 95717351829239007576052495)
    ·
      refine ⟨143576027743858511364078743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95717351829239007576052495 143576027743858511364078743)
      ·
        refine ⟨215364041615787767046118115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143576027743858511364078743 215364041615787767046118115)
        ·
          refine ⟨323046062423681650569177173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215364041615787767046118115 323046062423681650569177173)
          ·
            refine ⟨3785696044027519342607545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 323046062423681650569177173 3785696044027519342607545)
            ·
              refine ⟨2839272033020639506955659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785696044027519342607545 2839272033020639506955659)
              ·
                refine ⟨4258908049530959260433489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839272033020639506955659 4258908049530959260433489)
                ·
                  refine ⟨3194181037148219445325117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258908049530959260433489 3194181037148219445325117)
                  ·
                    refine ⟨1197817888930582291996919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194181037148219445325117 1197817888930582291996919)
                    ·
                      rfl

theorem cell22_3499113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 3].length) (baseStart_3499113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499113 prefixEnd_3499113 := by exact prefixLift 3499113
  have htrace : WordTrace (prefixWord ++ tailWord_3499113) baseStart_3499113 baseEnd_3499113 := by
    simpa [prefixWord, tailWord_3499113, baseEnd_3499113] using wordTrace_append hprefix tailTrace_3499113
  have hstable : (prefixWord ++ tailWord_3499113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499113).length < 2 ^ (prefixWord ++ tailWord_3499113).sum := by decide
  have hdescent : baseEnd_3499113 < baseStart_3499113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499169 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_3499169 : Nat := 118140960795 + 3499169 * 2 ^ 59
def prefixEnd_3499169 : Nat := 4983230072969 + 3 ^ 40 * 3499169 * 2
def baseEnd_3499169 : Nat := 1197837058875016812596747

theorem tailTrace_3499169 : CollatzResearch.WordTrace tailWord_3499169 prefixEnd_3499169 1197837058875016812596747 := by
  unfold tailWord_3499169
  simp only [CollatzResearch.WordTrace]
  refine ⟨127625178260115798332108561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85083452173410532221405707 127625178260115798332108561)
  ·
    refine ⟨95718883695086848749081421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127625178260115798332108561 95718883695086848749081421)
    ·
      refine ⟨35894581385657568280905533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95718883695086848749081421 35894581385657568280905533)
      ·
        refine ⟨13460468019621588105339575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35894581385657568280905533 13460468019621588105339575)
        ·
          refine ⟨20190702029432382158009363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13460468019621588105339575 20190702029432382158009363)
          ·
            refine ⟨30286053044148573237014045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20190702029432382158009363 30286053044148573237014045)
            ·
              refine ⟨11357269891555714963880267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30286053044148573237014045 11357269891555714963880267)
              ·
                refine ⟨17035904837333572445820401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11357269891555714963880267 17035904837333572445820401)
                ·
                  refine ⟨12776928628000179334365301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17035904837333572445820401 12776928628000179334365301)
                  ·
                    refine ⟨1197837058875016812596747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12776928628000179334365301 1197837058875016812596747)
                    ·
                      rfl

theorem cell22_3499169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_3499169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499169 prefixEnd_3499169 := by exact prefixLift 3499169
  have htrace : WordTrace (prefixWord ++ tailWord_3499169) baseStart_3499169 baseEnd_3499169 := by
    simpa [prefixWord, tailWord_3499169, baseEnd_3499169] using wordTrace_append hprefix tailTrace_3499169
  have hstable : (prefixWord ++ tailWord_3499169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499169).length < 2 ^ (prefixWord ++ tailWord_3499169).sum := by decide
  have hdescent : baseEnd_3499169 < baseStart_3499169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499231 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 2, 3]
def baseStart_3499231 : Nat := 118140960795 + 3499231 * 2 ^ 59
def prefixEnd_3499231 : Nat := 4983230072969 + 3 ^ 40 * 3499231 * 2
def baseEnd_3499231 : Nat := 1197858282742069317546557

theorem tailTrace_3499231 : CollatzResearch.WordTrace tailWord_3499231 prefixEnd_3499231 1197858282742069317546557 := by
  unfold tailWord_3499231
  simp only [CollatzResearch.WordTrace]
  refine ⟨127627439585891182920865547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85084959723927455280577031 127627439585891182920865547)
  ·
    refine ⟨191441159378836774381298321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127627439585891182920865547 191441159378836774381298321)
    ·
      refine ⟨143580869534127580785973741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191441159378836774381298321 143580869534127580785973741)
      ·
        refine ⟨53842826075297842794740153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143580869534127580785973741 53842826075297842794740153)
        ·
          refine ⟨40382119556473382096055115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53842826075297842794740153 40382119556473382096055115)
          ·
            refine ⟨60573179334710073144082673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40382119556473382096055115 60573179334710073144082673)
            ·
              refine ⟨45429884501032554858062005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60573179334710073144082673 45429884501032554858062005)
              ·
                refine ⟨4259051671971802017943313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45429884501032554858062005 4259051671971802017943313)
                ·
                  refine ⟨3194288753978851513457485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4259051671971802017943313 3194288753978851513457485)
                  ·
                    refine ⟨1197858282742069317546557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194288753978851513457485 1197858282742069317546557)
                    ·
                      rfl

theorem cell22_3499231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_3499231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499231 prefixEnd_3499231 := by exact prefixLift 3499231
  have htrace : WordTrace (prefixWord ++ tailWord_3499231) baseStart_3499231 baseEnd_3499231 := by
    simpa [prefixWord, tailWord_3499231, baseEnd_3499231] using wordTrace_append hprefix tailTrace_3499231
  have hstable : (prefixWord ++ tailWord_3499231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499231).length < 2 ^ (prefixWord ++ tailWord_3499231).sum := by decide
  have hdescent : baseEnd_3499231 < baseStart_3499231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499244 : List Nat := [2, 2, 1, 1, 2, 5, 1, 8]
def baseStart_3499244 : Nat := 118140960795 + 3499244 * 2 ^ 59
def prefixEnd_3499244 : Nat := 4983230072969 + 3 ^ 40 * 3499244 * 2
def baseEnd_3499244 : Nat := 133095859211971290774613

theorem tailTrace_3499244 : CollatzResearch.WordTrace tailWord_3499244 prefixEnd_3499244 133095859211971290774613 := by
  unfold tailWord_3499244
  simp only [CollatzResearch.WordTrace]
  refine ⟨63813956867422043070544393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85085275823229390760725857 63813956867422043070544393)
  ·
    refine ⟨47860467650566532302908295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63813956867422043070544393 47860467650566532302908295)
    ·
      refine ⟨71790701475849798454362443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47860467650566532302908295 71790701475849798454362443)
      ·
        refine ⟨107686052213774697681543665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71790701475849798454362443 107686052213774697681543665)
        ·
          refine ⟨80764539160331023261157749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107686052213774697681543665 80764539160331023261157749)
          ·
            refine ⟨7571675546281033430733539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80764539160331023261157749 7571675546281033430733539)
            ·
              refine ⟨11357513319421550146100309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571675546281033430733539 11357513319421550146100309)
              ·
                refine ⟨133095859211971290774613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11357513319421550146100309 133095859211971290774613)
                ·
                  rfl

theorem cell22_3499244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 8].length) (baseStart_3499244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499244 prefixEnd_3499244 := by exact prefixLift 3499244
  have htrace : WordTrace (prefixWord ++ tailWord_3499244) baseStart_3499244 baseEnd_3499244 := by
    simpa [prefixWord, tailWord_3499244, baseEnd_3499244] using wordTrace_append hprefix tailTrace_3499244
  have hstable : (prefixWord ++ tailWord_3499244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499244).length < 2 ^ (prefixWord ++ tailWord_3499244).sum := by decide
  have hdescent : baseEnd_3499244 < baseStart_3499244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499250 : List Nat := [3, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_3499250 : Nat := 118140960795 + 3499250 * 2 ^ 59
def prefixEnd_3499250 : Nat := 4983230072969 + 3 ^ 40 * 3499250 * 2
def baseEnd_3499250 : Nat := 399288262276786533773833

theorem tailTrace_3499250 : CollatzResearch.WordTrace tailWord_3499250 prefixEnd_3499250 399288262276786533773833 := by
  unfold tailWord_3499250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31907033143205587291451801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85085421715214899443871469 31907033143205587291451801)
  ·
    refine ⟨23930274857404190468588851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31907033143205587291451801 23930274857404190468588851)
    ·
      refine ⟨35895412286106285702883277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23930274857404190468588851 35895412286106285702883277)
      ·
        refine ⟨13460779607289857138581229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35895412286106285702883277 13460779607289857138581229)
        ·
          refine ⟨5047792352733696426967961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13460779607289857138581229 5047792352733696426967961)
          ·
            refine ⟨3785844264550272320225971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5047792352733696426967961 3785844264550272320225971)
            ·
              refine ⟨5678766396825408480338957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785844264550272320225971 5678766396825408480338957)
              ·
                refine ⟨2129537398809528180127109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5678766396825408480338957 2129537398809528180127109)
                ·
                  refine ⟨399288262276786533773833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2129537398809528180127109 399288262276786533773833)
                  ·
                    rfl

theorem cell22_3499250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_3499250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499250 prefixEnd_3499250 := by exact prefixLift 3499250
  have htrace : WordTrace (prefixWord ++ tailWord_3499250) baseStart_3499250 baseEnd_3499250 := by
    simpa [prefixWord, tailWord_3499250, baseEnd_3499250] using wordTrace_append hprefix tailTrace_3499250
  have hstable : (prefixWord ++ tailWord_3499250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499250).length < 2 ^ (prefixWord ++ tailWord_3499250).sum := by decide
  have hdescent : baseEnd_3499250 < baseStart_3499250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499274 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_3499274 : Nat := 118140960795 + 3499274 * 2 ^ 59
def prefixEnd_3499274 : Nat := 4983230072969 + 3 ^ 40 * 3499274 * 2
def baseEnd_3499274 : Nat := 1197873002520831538721425

theorem tailTrace_3499274 : CollatzResearch.WordTrace tailWord_3499274 prefixEnd_3499274 1197873002520831538721425 := by
  unfold tailWord_3499274
  simp only [CollatzResearch.WordTrace]
  refine ⟨31907251981183850316170219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85086005283156934176453917 31907251981183850316170219)
  ·
    refine ⟨47860877971775775474255329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31907251981183850316170219 47860877971775775474255329)
    ·
      refine ⟨35895658478831831605691497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47860877971775775474255329 35895658478831831605691497)
      ·
        refine ⟨26921743859123873704268623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35895658478831831605691497 26921743859123873704268623)
        ·
          refine ⟨40382615788685810556402935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26921743859123873704268623 40382615788685810556402935)
          ·
            refine ⟨60573923683028715834604403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40382615788685810556402935 60573923683028715834604403)
            ·
              refine ⟨90860885524543073751906605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60573923683028715834604403 90860885524543073751906605)
              ·
                refine ⟨34072832071703652656964977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90860885524543073751906605 34072832071703652656964977)
                ·
                  refine ⟨25554624053777739492723733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34072832071703652656964977 25554624053777739492723733)
                  ·
                    refine ⟨1197873002520831538721425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25554624053777739492723733 1197873002520831538721425)
                    ·
                      rfl

theorem cell22_3499274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_3499274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499274 prefixEnd_3499274 := by exact prefixLift 3499274
  have htrace : WordTrace (prefixWord ++ tailWord_3499274) baseStart_3499274 baseEnd_3499274 := by
    simpa [prefixWord, tailWord_3499274, baseEnd_3499274] using wordTrace_append hprefix tailTrace_3499274
  have hstable : (prefixWord ++ tailWord_3499274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499274).length < 2 ^ (prefixWord ++ tailWord_3499274).sum := by decide
  have hdescent : baseEnd_3499274 < baseStart_3499274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499282 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3499282 : Nat := 118140960795 + 3499282 * 2 ^ 59
def prefixEnd_3499282 : Nat := 4983230072969 + 3 ^ 40 * 3499282 * 2
def baseEnd_3499282 : Nat := 1197875741084322184521401

theorem tailTrace_3499282 : CollatzResearch.WordTrace tailWord_3499282 prefixEnd_3499282 1197875741084322184521401 := by
  unfold tailWord_3499282
  simp only [CollatzResearch.WordTrace]
  refine ⟨31907324927176604657743025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85086199805804279087314733 31907324927176604657743025)
  ·
    refine ⟨23930493695382453493307269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31907324927176604657743025 23930493695382453493307269)
    ·
      refine ⟨4486967567884210029995113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23930493695382453493307269 4486967567884210029995113)
      ·
        refine ⟨3365225675913157522496335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4486967567884210029995113 3365225675913157522496335)
        ·
          refine ⟨5047838513869736283744503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365225675913157522496335 5047838513869736283744503)
          ·
            refine ⟨7571757770804604425616755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047838513869736283744503 7571757770804604425616755)
            ·
              refine ⟨11357636656206906638425133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571757770804604425616755 11357636656206906638425133)
              ·
                refine ⟨4259113746077589989409425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11357636656206906638425133 4259113746077589989409425)
                ·
                  refine ⟨3194335309558192492057069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4259113746077589989409425 3194335309558192492057069)
                  ·
                    refine ⟨1197875741084322184521401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194335309558192492057069 1197875741084322184521401)
                    ·
                      rfl

theorem cell22_3499282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3499282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499282 prefixEnd_3499282 := by exact prefixLift 3499282
  have htrace : WordTrace (prefixWord ++ tailWord_3499282) baseStart_3499282 baseEnd_3499282 := by
    simpa [prefixWord, tailWord_3499282, baseEnd_3499282] using wordTrace_append hprefix tailTrace_3499282
  have hstable : (prefixWord ++ tailWord_3499282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499282).length < 2 ^ (prefixWord ++ tailWord_3499282).sum := by decide
  have hdescent : baseEnd_3499282 < baseStart_3499282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499327 : List Nat := [1, 1, 2, 2, 4, 4, 2, 2, 1, 3]
def baseStart_3499327 : Nat := 118140960795 + 3499327 * 2 ^ 59
def prefixEnd_3499327 : Nat := 4983230072969 + 3 ^ 40 * 3499327 * 2
def baseEnd_3499327 : Nat := 1197891145503957067146263

theorem tailTrace_3499327 : CollatzResearch.WordTrace tailWord_3499327 prefixEnd_3499327 1197891145503957067146263 := by
  unfold tailWord_3499327
  simp only [CollatzResearch.WordTrace]
  refine ⟨127630940993543391316360235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85087293995695594210906823 127630940993543391316360235)
  ·
    refine ⟨191446411490315086974540353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127630940993543391316360235 191446411490315086974540353)
    ·
      refine ⟨143584808617736315230905265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191446411490315086974540353 143584808617736315230905265)
      ·
        refine ⟨107688606463302236423178949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143584808617736315230905265 107688606463302236423178949)
        ·
          refine ⟨20191613711869169329346053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107688606463302236423178949 20191613711869169329346053)
          ·
            refine ⟨3785927570975469249252385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20191613711869169329346053 3785927570975469249252385)
            ·
              refine ⟨2839445678231601936939289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785927570975469249252385 2839445678231601936939289)
              ·
                refine ⟨2129584258673701452704467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2839445678231601936939289 2129584258673701452704467)
                ·
                  refine ⟨3194376388010552179056701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129584258673701452704467 3194376388010552179056701)
                  ·
                    refine ⟨1197891145503957067146263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194376388010552179056701 1197891145503957067146263)
                    ·
                      rfl

theorem cell22_3499327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 3].length) (baseStart_3499327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499327 prefixEnd_3499327 := by exact prefixLift 3499327
  have htrace : WordTrace (prefixWord ++ tailWord_3499327) baseStart_3499327 baseEnd_3499327 := by
    simpa [prefixWord, tailWord_3499327, baseEnd_3499327] using wordTrace_append hprefix tailTrace_3499327
  have hstable : (prefixWord ++ tailWord_3499327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499327).length < 2 ^ (prefixWord ++ tailWord_3499327).sum := by decide
  have hdescent : baseEnd_3499327 < baseStart_3499327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499351 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 6]
def baseStart_3499351 : Nat := 118140960795 + 3499351 * 2 ^ 59
def prefixEnd_3499351 : Nat := 4983230072969 + 3 ^ 40 * 3499351 * 2
def baseEnd_3499351 : Nat := 399299787064809668182063

theorem tailTrace_3499351 : CollatzResearch.WordTrace tailWord_3499351 prefixEnd_3499351 399299787064809668182063 := by
  unfold tailWord_3499351
  simp only [CollatzResearch.WordTrace]
  refine ⟨127631816345456443415233907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85087877563637628943489271 127631816345456443415233907)
  ·
    refine ⟨191447724518184665122850861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127631816345456443415233907 191447724518184665122850861)
    ·
      refine ⟨71792896694319249421069073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191447724518184665122850861 71792896694319249421069073)
      ·
        refine ⟨53844672520739437065801805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71792896694319249421069073 53844672520739437065801805)
        ·
          refine ⟨20191752195277288899675677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53844672520739437065801805 20191752195277288899675677)
          ·
            refine ⟨7571907073228983337378379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20191752195277288899675677 7571907073228983337378379)
            ·
              refine ⟨11357860609843475006067569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571907073228983337378379 11357860609843475006067569)
              ·
                refine ⟨8518395457382606254550677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11357860609843475006067569 8518395457382606254550677)
                ·
                  refine ⟨399299787064809668182063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8518395457382606254550677 399299787064809668182063)
                  ·
                    rfl

theorem cell22_3499351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 6].length) (baseStart_3499351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499351 prefixEnd_3499351 := by exact prefixLift 3499351
  have htrace : WordTrace (prefixWord ++ tailWord_3499351) baseStart_3499351 baseEnd_3499351 := by
    simpa [prefixWord, tailWord_3499351, baseEnd_3499351] using wordTrace_append hprefix tailTrace_3499351
  have hstable : (prefixWord ++ tailWord_3499351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499351).length < 2 ^ (prefixWord ++ tailWord_3499351).sum := by decide
  have hdescent : baseEnd_3499351 < baseStart_3499351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499370 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_3499370 : Nat := 118140960795 + 3499370 * 2 ^ 59
def prefixEnd_3499370 : Nat := 4983230072969 + 3 ^ 40 * 3499370 * 2
def baseEnd_3499370 : Nat := 1197905865282719288321131

theorem tailTrace_3499370 : CollatzResearch.WordTrace tailWord_3499370 prefixEnd_3499370 1197905865282719288321131 := by
  unfold tailWord_3499370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31908127333096902415043891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85088339554925073106783709 31908127333096902415043891)
  ·
    refine ⟨47862190999645353622565837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31908127333096902415043891 47862190999645353622565837)
    ·
      refine ⟨17948321624867007608462189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47862190999645353622565837 17948321624867007608462189)
      ·
        refine ⟨6730620609325127853173321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17948321624867007608462189 6730620609325127853173321)
        ·
          refine ⟨5047965456993845889879991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6730620609325127853173321 5047965456993845889879991)
          ·
            refine ⟨7571948185490768834819987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047965456993845889879991 7571948185490768834819987)
            ·
              refine ⟨11357922278236153252229981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571948185490768834819987 11357922278236153252229981)
              ·
                refine ⟨4259220854338557469586243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11357922278236153252229981 4259220854338557469586243)
                ·
                  refine ⟨6388831281507836204379365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259220854338557469586243 6388831281507836204379365)
                  ·
                    refine ⟨1197905865282719288321131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6388831281507836204379365 1197905865282719288321131)
                    ·
                      rfl

theorem cell22_3499370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_3499370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499370 prefixEnd_3499370 := by exact prefixLift 3499370
  have htrace : WordTrace (prefixWord ++ tailWord_3499370) baseStart_3499370 baseEnd_3499370 := by
    simpa [prefixWord, tailWord_3499370, baseEnd_3499370] using wordTrace_append hprefix tailTrace_3499370
  have hstable : (prefixWord ++ tailWord_3499370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499370).length < 2 ^ (prefixWord ++ tailWord_3499370).sum := by decide
  have hdescent : baseEnd_3499370 < baseStart_3499370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499441 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 7]
def baseStart_3499441 : Nat := 118140960795 + 3499441 * 2 ^ 59
def prefixEnd_3499441 : Nat := 4983230072969 + 3 ^ 40 * 3499441 * 2
def baseEnd_3499441 : Nat := 399310056677899589931971

theorem tailTrace_3499441 : CollatzResearch.WordTrace tailWord_3499441 prefixEnd_3499441 399310056677899589931971 := by
  unfold tailWord_3499441
  simp only [CollatzResearch.WordTrace]
  refine ⟨127635098915130388786010177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85090065943420259190673451 127635098915130388786010177)
  ·
    refine ⟨95726324186347791589507633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127635098915130388786010177 95726324186347791589507633)
    ·
      refine ⟨71794743139760843692130725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95726324186347791589507633 71794743139760843692130725)
      ·
        refine ⟨13461514338705158192274511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71794743139760843692130725 13461514338705158192274511)
        ·
          refine ⟨20192271508057737288411767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13461514338705158192274511 20192271508057737288411767)
          ·
            refine ⟨30288407262086605932617651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20192271508057737288411767 30288407262086605932617651)
            ·
              refine ⟨45432610893129908898926477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30288407262086605932617651 45432610893129908898926477)
              ·
                refine ⟨17037229084923715837097429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45432610893129908898926477 17037229084923715837097429)
                ·
                  refine ⟨399310056677899589931971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17037229084923715837097429 399310056677899589931971)
                  ·
                    rfl

theorem cell22_3499441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_3499441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499441 prefixEnd_3499441 := by exact prefixLift 3499441
  have htrace : WordTrace (prefixWord ++ tailWord_3499441) baseStart_3499441 baseEnd_3499441 := by
    simpa [prefixWord, tailWord_3499441, baseEnd_3499441] using wordTrace_append hprefix tailTrace_3499441
  have hstable : (prefixWord ++ tailWord_3499441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499441).length < 2 ^ (prefixWord ++ tailWord_3499441).sum := by decide
  have hdescent : baseEnd_3499441 < baseStart_3499441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499445 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_3499445 : Nat := 118140960795 + 3499445 * 2 ^ 59
def prefixEnd_3499445 : Nat := 4983230072969 + 3 ^ 40 * 3499445 * 2
def baseEnd_3499445 : Nat := 1197931539315444092695901

theorem tailTrace_3499445 : CollatzResearch.WordTrace tailWord_3499445 prefixEnd_3499445 1197931539315444092695901 := by
  unfold tailWord_3499445
  simp only [CollatzResearch.WordTrace]
  refine ⟨127635244807115897469155789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85090163204743931646103859 127635244807115897469155789)
  ·
    refine ⟨47863216802668461550933421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127635244807115897469155789 47863216802668461550933421)
    ·
      refine ⟨17948706301000673081600033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47863216802668461550933421 17948706301000673081600033)
      ·
        refine ⟨13461529725750504811200025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17948706301000673081600033 13461529725750504811200025)
        ·
          refine ⟨10096147294312878608400019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13461529725750504811200025 10096147294312878608400019)
          ·
            refine ⟨15144220941469317912600029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10096147294312878608400019 15144220941469317912600029)
            ·
              refine ⟨5679082853050994217225011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15144220941469317912600029 5679082853050994217225011)
              ·
                refine ⟨8518624279576491325837517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679082853050994217225011 8518624279576491325837517)
                ·
                  refine ⟨3194484104841184247189069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8518624279576491325837517 3194484104841184247189069)
                  ·
                    refine ⟨1197931539315444092695901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194484104841184247189069 1197931539315444092695901)
                    ·
                      rfl

theorem cell22_3499445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_3499445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499445 prefixEnd_3499445 := by exact prefixLift 3499445
  have htrace : WordTrace (prefixWord ++ tailWord_3499445) baseStart_3499445 baseEnd_3499445 := by
    simpa [prefixWord, tailWord_3499445, baseEnd_3499445] using wordTrace_append hprefix tailTrace_3499445
  have hstable : (prefixWord ++ tailWord_3499445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499445).length < 2 ^ (prefixWord ++ tailWord_3499445).sum := by decide
  have hdescent : baseEnd_3499445 < baseStart_3499445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499456 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_3499456 : Nat := 118140960795 + 3499456 * 2 ^ 59
def prefixEnd_3499456 : Nat := 4983230072969 + 3 ^ 40 * 3499456 * 2
def baseEnd_3499456 : Nat := 1197935304840243730670867

theorem tailTrace_3499456 : CollatzResearch.WordTrace tailWord_3499456 prefixEnd_3499456 1197935304840243730670867 := by
  unfold tailWord_3499456
  simp only [CollatzResearch.WordTrace]
  refine ⟨63817823005038023173903111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85090430673384030898537481 63817823005038023173903111)
  ·
    refine ⟨95726734507557034760854667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63817823005038023173903111 95726734507557034760854667)
    ·
      refine ⟨143590101761335552141282001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95726734507557034760854667 143590101761335552141282001)
      ·
        refine ⟨107692576321001664105961501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143590101761335552141282001 107692576321001664105961501)
        ·
          refine ⟨40384716120375624039735563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107692576321001664105961501 40384716120375624039735563)
          ·
            refine ⟨60577074180563436059603345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40384716120375624039735563 60577074180563436059603345)
            ·
              refine ⟨45432805635422577044702509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60577074180563436059603345 45432805635422577044702509)
              ·
                refine ⟨17037302113283466391763441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45432805635422577044702509 17037302113283466391763441)
                ·
                  refine ⟨12777976584962599793822581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17037302113283466391763441 12777976584962599793822581)
                  ·
                    refine ⟨1197935304840243730670867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12777976584962599793822581 1197935304840243730670867)
                    ·
                      rfl

theorem cell22_3499456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_3499456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499456 prefixEnd_3499456 := by exact prefixLift 3499456
  have htrace : WordTrace (prefixWord ++ tailWord_3499456) baseStart_3499456 baseEnd_3499456 := by
    simpa [prefixWord, tailWord_3499456, baseEnd_3499456] using wordTrace_append hprefix tailTrace_3499456
  have hstable : (prefixWord ++ tailWord_3499456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499456).length < 2 ^ (prefixWord ++ tailWord_3499456).sum := by decide
  have hdescent : baseEnd_3499456 < baseStart_3499456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499552 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 2, 3]
def baseStart_3499552 : Nat := 118140960795 + 3499552 * 2 ^ 59
def prefixEnd_3499552 : Nat := 4983230072969 + 3 ^ 40 * 3499552 * 2
def baseEnd_3499552 : Nat := 1197968167602131480270573

theorem tailTrace_3499552 : CollatzResearch.WordTrace tailWord_3499552 prefixEnd_3499552 1197968167602131480270573 := by
  unfold tailWord_3499552
  simp only [CollatzResearch.WordTrace]
  refine ⟨63819573708864127371650455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85092764945152169828867273 63819573708864127371650455)
  ·
    refine ⟨95729360563296191057475683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63819573708864127371650455 95729360563296191057475683)
    ·
      refine ⟨143594040844944286586213525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95729360563296191057475683 143594040844944286586213525)
      ·
        refine ⟨6730970664606763433728759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143594040844944286586213525 6730970664606763433728759)
        ·
          refine ⟨10096455996910145150593139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6730970664606763433728759 10096455996910145150593139)
          ·
            refine ⟨15144683995365217725889709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10096455996910145150593139 15144683995365217725889709)
            ·
              refine ⟨5679256498261956647208641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15144683995365217725889709 5679256498261956647208641)
              ·
                refine ⟨4259442373696467485406481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5679256498261956647208641 4259442373696467485406481)
                ·
                  refine ⟨3194581780272350614054861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4259442373696467485406481 3194581780272350614054861)
                  ·
                    refine ⟨1197968167602131480270573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194581780272350614054861 1197968167602131480270573)
                    ·
                      rfl

theorem cell22_3499552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_3499552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499552 prefixEnd_3499552 := by exact prefixLift 3499552
  have htrace : WordTrace (prefixWord ++ tailWord_3499552) baseStart_3499552 baseEnd_3499552 := by
    simpa [prefixWord, tailWord_3499552, baseEnd_3499552] using wordTrace_append hprefix tailTrace_3499552
  have hstable : (prefixWord ++ tailWord_3499552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499552).length < 2 ^ (prefixWord ++ tailWord_3499552).sum := by decide
  have hdescent : baseEnd_3499552 < baseStart_3499552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499672 : List Nat := [2, 1, 2, 4, 1, 3, 1, 4, 4]
def baseStart_3499672 : Nat := 118140960795 + 3499672 * 2 ^ 59
def prefixEnd_3499672 : Nat := 4983230072969 + 3 ^ 40 * 3499672 * 2
def baseEnd_3499672 : Nat := 399336415351497055756735

theorem tailTrace_3499672 : CollatzResearch.WordTrace tailWord_3499672 prefixEnd_3499672 399336415351497055756735 := by
  unfold tailWord_3499672
  simp only [CollatzResearch.WordTrace]
  refine ⟨63821762088646757618834635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85095682784862343491779513 63821762088646757618834635)
  ·
    refine ⟨95732643132970136428251953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63821762088646757618834635 95732643132970136428251953)
    ·
      refine ⟨71799482349727602321188965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95732643132970136428251953 71799482349727602321188965)
      ·
        refine ⟨13462402940573925435222931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71799482349727602321188965 13462402940573925435222931)
        ·
          refine ⟨20193604410860888152834397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13462402940573925435222931 20193604410860888152834397)
          ·
            refine ⟨7572601654072833057312899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20193604410860888152834397 7572601654072833057312899)
            ·
              refine ⟨11358902481109249585969349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572601654072833057312899 11358902481109249585969349)
              ·
                refine ⟨2129794215207984297369253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11358902481109249585969349 2129794215207984297369253)
                ·
                  refine ⟨399336415351497055756735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2129794215207984297369253 399336415351497055756735)
                  ·
                    rfl

theorem cell22_3499672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 4].length) (baseStart_3499672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499672 prefixEnd_3499672 := by exact prefixLift 3499672
  have htrace : WordTrace (prefixWord ++ tailWord_3499672) baseStart_3499672 baseEnd_3499672 := by
    simpa [prefixWord, tailWord_3499672, baseEnd_3499672] using wordTrace_append hprefix tailTrace_3499672
  have hstable : (prefixWord ++ tailWord_3499672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499672).length < 2 ^ (prefixWord ++ tailWord_3499672).sum := by decide
  have hdescent : baseEnd_3499672 < baseStart_3499672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499751 : List Nat := [1, 1, 5, 4, 2, 1, 2, 6]
def baseStart_3499751 : Nat := 118140960795 + 3499751 * 2 ^ 59
def prefixEnd_3499751 : Nat := 4983230072969 + 3 ^ 40 * 3499751 * 2
def baseEnd_3499751 : Nat := 133115143263217921616107

theorem tailTrace_3499751 : CollatzResearch.WordTrace tailWord_3499751 prefixEnd_3499751 133115143263217921616107 := by
  unfold tailWord_3499751
  simp only [CollatzResearch.WordTrace]
  refine ⟨127646405544007311729795107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85097603696004874486530071 127646405544007311729795107)
  ·
    refine ⟨191469608316010967594692661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127646405544007311729795107 191469608316010967594692661)
    ·
      refine ⟨17950275779626028212002437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191469608316010967594692661 17950275779626028212002437)
      ·
        refine ⟨3365676708679880289750457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17950275779626028212002437 3365676708679880289750457)
        ·
          refine ⟨2524257531509910217312843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3365676708679880289750457 2524257531509910217312843)
          ·
            refine ⟨3786386297264865325969265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524257531509910217312843 3786386297264865325969265)
            ·
              refine ⟨2839789722948648994476949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3786386297264865325969265 2839789722948648994476949)
              ·
                refine ⟨133115143263217921616107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2839789722948648994476949 133115143263217921616107)
                ·
                  rfl

theorem cell22_3499751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 6].length) (baseStart_3499751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499751 prefixEnd_3499751 := by exact prefixLift 3499751
  have htrace : WordTrace (prefixWord ++ tailWord_3499751) baseStart_3499751 baseEnd_3499751 := by
    simpa [prefixWord, tailWord_3499751, baseEnd_3499751] using wordTrace_append hprefix tailTrace_3499751
  have hstable : (prefixWord ++ tailWord_3499751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499751).length < 2 ^ (prefixWord ++ tailWord_3499751).sum := by decide
  have hdescent : baseEnd_3499751 < baseStart_3499751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499766 : List Nat := [5, 1, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_3499766 : Nat := 118140960795 + 3499766 * 2 ^ 59
def prefixEnd_3499766 : Nat := 4983230072969 + 3 ^ 40 * 3499766 * 2
def baseEnd_3499766 : Nat := 1198041424175506255419917

theorem tailTrace_3499766 : CollatzResearch.WordTrace tailWord_3499766 prefixEnd_3499766 1198041424175506255419917 := by
  unfold tailWord_3499766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7977934539934560580724447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85097968425968646194394101 7977934539934560580724447)
  ·
    refine ⟨11966901809901840871086671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7977934539934560580724447 11966901809901840871086671)
    ·
      refine ⟨17950352714852761306630007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11966901809901840871086671 17950352714852761306630007)
      ·
        refine ⟨26925529072279141959945011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17950352714852761306630007 26925529072279141959945011)
        ·
          refine ⟨40388293608418712939917517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26925529072279141959945011 40388293608418712939917517)
          ·
            refine ⟨15145610103157017352469069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40388293608418712939917517 15145610103157017352469069)
            ·
              refine ⟨5679603788683881507175901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15145610103157017352469069 5679603788683881507175901)
              ·
                refine ⟨2129851420756455565190963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5679603788683881507175901 2129851420756455565190963)
                ·
                  refine ⟨3194777131134683347786445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129851420756455565190963 3194777131134683347786445)
                  ·
                    refine ⟨1198041424175506255419917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194777131134683347786445 1198041424175506255419917)
                    ·
                      rfl

theorem cell22_3499766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_3499766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499766 prefixEnd_3499766 := by exact prefixLift 3499766
  have htrace : WordTrace (prefixWord ++ tailWord_3499766) baseStart_3499766 baseEnd_3499766 := by
    simpa [prefixWord, tailWord_3499766, baseEnd_3499766] using wordTrace_append hprefix tailTrace_3499766
  have hstable : (prefixWord ++ tailWord_3499766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499766).length < 2 ^ (prefixWord ++ tailWord_3499766).sum := by decide
  have hdescent : baseEnd_3499766 < baseStart_3499766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499783 : List Nat := [1, 1, 4, 4, 2, 1, 3, 2, 1, 3]
def baseStart_3499783 : Nat := 118140960795 + 3499783 * 2 ^ 59
def prefixEnd_3499783 : Nat := 4983230072969 + 3 ^ 40 * 3499783 * 2
def baseEnd_3499783 : Nat := 1198047243622923877744865

theorem tailTrace_3499783 : CollatzResearch.WordTrace tailWord_3499783 prefixEnd_3499783 1198047243622923877744865 := by
  unfold tailWord_3499783
  simp only [CollatzResearch.WordTrace]
  refine ⟨127647572679891381194960003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85098381786594254129973335 127647572679891381194960003)
  ·
    refine ⟨191471359019837071792440005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127647572679891381194960003 191471359019837071792440005)
    ·
      refine ⟨35900879816219450961082501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191471359019837071792440005 35900879816219450961082501)
      ·
        refine ⟨6731414965541147055202969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35900879816219450961082501 6731414965541147055202969)
        ·
          refine ⟨5048561224155860291402227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6731414965541147055202969 5048561224155860291402227)
          ·
            refine ⟨7572841836233790437103341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5048561224155860291402227 7572841836233790437103341)
            ·
              refine ⟨2839815688587671413913753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7572841836233790437103341 2839815688587671413913753)
              ·
                refine ⟨2129861766440753560435315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2839815688587671413913753 2129861766440753560435315)
                ·
                  refine ⟨3194792649661130340652973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129861766440753560435315 3194792649661130340652973)
                  ·
                    refine ⟨1198047243622923877744865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194792649661130340652973 1198047243622923877744865)
                    ·
                      rfl

theorem cell22_3499783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_3499783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499783 prefixEnd_3499783 := by exact prefixLift 3499783
  have htrace : WordTrace (prefixWord ++ tailWord_3499783) baseStart_3499783 baseEnd_3499783 := by
    simpa [prefixWord, tailWord_3499783, baseEnd_3499783] using wordTrace_append hprefix tailTrace_3499783
  have hstable : (prefixWord ++ tailWord_3499783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499783).length < 2 ^ (prefixWord ++ tailWord_3499783).sum := by decide
  have hdescent : baseEnd_3499783 < baseStart_3499783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499789 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3499789 : Nat := 118140960795 + 3499789 * 2 ^ 59
def prefixEnd_3499789 : Nat := 4983230072969 + 3 ^ 40 * 3499789 * 2
def baseEnd_3499789 : Nat := 1198049297545541862094847

theorem tailTrace_3499789 : CollatzResearch.WordTrace tailWord_3499789 prefixEnd_3499789 1198049297545541862094847 := by
  unfold tailWord_3499789
  simp only [CollatzResearch.WordTrace]
  refine ⟨127647791517869644219678421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85098527678579762813118947 127647791517869644219678421)
  ·
    refine ⟨2991745113700069786398713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127647791517869644219678421 2991745113700069786398713)
    ·
      refine ⟨2243808835275052339799035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2991745113700069786398713 2243808835275052339799035)
      ·
        refine ⟨3365713252912578509698553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243808835275052339799035 3365713252912578509698553)
        ·
          refine ⟨2524284939684433882273915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3365713252912578509698553 2524284939684433882273915)
          ·
            refine ⟨3786427409526650823410873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524284939684433882273915 3786427409526650823410873)
            ·
              refine ⟨2839820557144988117558155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3786427409526650823410873 2839820557144988117558155)
              ·
                refine ⟨4259730835717482176337233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839820557144988117558155 4259730835717482176337233)
                ·
                  refine ⟨3194798126788111632252925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4259730835717482176337233 3194798126788111632252925)
                  ·
                    refine ⟨1198049297545541862094847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194798126788111632252925 1198049297545541862094847)
                    ·
                      rfl

theorem cell22_3499789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3499789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499789 prefixEnd_3499789 := by exact prefixLift 3499789
  have htrace : WordTrace (prefixWord ++ tailWord_3499789) baseStart_3499789 baseEnd_3499789 := by
    simpa [prefixWord, tailWord_3499789, baseEnd_3499789] using wordTrace_append hprefix tailTrace_3499789
  have hstable : (prefixWord ++ tailWord_3499789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499789).length < 2 ^ (prefixWord ++ tailWord_3499789).sum := by decide
  have hdescent : baseEnd_3499789 < baseStart_3499789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499809 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 1, 4]
def baseStart_3499809 : Nat := 118140960795 + 3499809 * 2 ^ 59
def prefixEnd_3499809 : Nat := 4983230072969 + 3 ^ 40 * 3499809 * 2
def baseEnd_3499809 : Nat := 1198056143954268476594785

theorem tailTrace_3499809 : CollatzResearch.WordTrace tailWord_3499809 prefixEnd_3499809 1198056143954268476594785 := by
  unfold tailWord_3499809
  simp only [CollatzResearch.WordTrace]
  refine ⟨127648520977797187635406481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85099013985198125090270987 127648520977797187635406481)
  ·
    refine ⟨95736390733347890726554861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127648520977797187635406481 95736390733347890726554861)
    ·
      refine ⟨35901146525005459022458073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95736390733347890726554861 35901146525005459022458073)
      ·
        refine ⟨26925859893754094266843555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35901146525005459022458073 26925859893754094266843555)
        ·
          refine ⟨40388789840631141400265333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26925859893754094266843555 40388789840631141400265333)
          ·
            refine ⟨3786449047559169506274875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40388789840631141400265333 3786449047559169506274875)
            ·
              refine ⟨5679673571338754259412313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786449047559169506274875 5679673571338754259412313)
              ·
                refine ⟨4259755178504065694559235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5679673571338754259412313 4259755178504065694559235)
                ·
                  refine ⟨6389632767756098541838853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259755178504065694559235 6389632767756098541838853)
                  ·
                    refine ⟨1198056143954268476594785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6389632767756098541838853 1198056143954268476594785)
                    ·
                      rfl

theorem cell22_3499809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_3499809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499809 prefixEnd_3499809 := by exact prefixLift 3499809
  have htrace : WordTrace (prefixWord ++ tailWord_3499809) baseStart_3499809 baseEnd_3499809 := by
    simpa [prefixWord, tailWord_3499809, baseEnd_3499809] using wordTrace_append hprefix tailTrace_3499809
  have hstable : (prefixWord ++ tailWord_3499809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499809).length < 2 ^ (prefixWord ++ tailWord_3499809).sum := by decide
  have hdescent : baseEnd_3499809 < baseStart_3499809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499865 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_3499865 : Nat := 118140960795 + 3499865 * 2 ^ 59
def prefixEnd_3499865 : Nat := 4983230072969 + 3 ^ 40 * 3499865 * 2
def baseEnd_3499865 : Nat := 1198075313898702997194613

theorem tailTrace_3499865 : CollatzResearch.WordTrace tailWord_3499865 prefixEnd_3499865 1198075313898702997194613 := by
  unfold tailWord_3499865
  simp only [CollatzResearch.WordTrace]
  refine ⟨127650563465594309199445049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85100375643729539466296699 127650563465594309199445049)
  ·
    refine ⟨95737922599195731899583787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127650563465594309199445049 95737922599195731899583787)
    ·
      refine ⟨143606883898793597849375681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95737922599195731899583787 143606883898793597849375681)
      ·
        refine ⟨107705162924095198387031761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143606883898793597849375681 107705162924095198387031761)
        ·
          refine ⟨80778872193071398790273821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107705162924095198387031761 80778872193071398790273821)
          ·
            refine ⟨30292077072401774546352683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80778872193071398790273821 30292077072401774546352683)
            ·
              refine ⟨45438115608602661819529025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30292077072401774546352683 45438115608602661819529025)
              ·
                refine ⟨34078586706451996364646769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45438115608602661819529025 34078586706451996364646769)
                ·
                  refine ⟨25558940029838997273485077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34078586706451996364646769 25558940029838997273485077)
                  ·
                    refine ⟨1198075313898702997194613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25558940029838997273485077 1198075313898702997194613)
                    ·
                      rfl

theorem cell22_3499865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_3499865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499865 prefixEnd_3499865 := by exact prefixLift 3499865
  have htrace : WordTrace (prefixWord ++ tailWord_3499865) baseStart_3499865 baseEnd_3499865 := by
    simpa [prefixWord, tailWord_3499865, baseEnd_3499865] using wordTrace_append hprefix tailTrace_3499865
  have hstable : (prefixWord ++ tailWord_3499865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499865).length < 2 ^ (prefixWord ++ tailWord_3499865).sum := by decide
  have hdescent : baseEnd_3499865 < baseStart_3499865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499935 : List Nat := [1, 1, 2, 5, 4, 1, 1, 3, 1, 3]
def baseStart_3499935 : Nat := 118140960795 + 3499935 * 2 ^ 59
def prefixEnd_3499935 : Nat := 4983230072969 + 3 ^ 40 * 3499935 * 2
def baseEnd_3499935 : Nat := 1198099276329246147944399

theorem tailTrace_3499935 : CollatzResearch.WordTrace tailWord_3499935 prefixEnd_3499935 1198099276329246147944399 := by
  unfold tailWord_3499935
  simp only [CollatzResearch.WordTrace]
  refine ⟨127653116575340711154493259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85102077716893807436328839 127653116575340711154493259)
  ·
    refine ⟨191479674863011066731739889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127653116575340711154493259 191479674863011066731739889)
    ·
      refine ⟨143609756147258300048804917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191479674863011066731739889 143609756147258300048804917)
      ·
        refine ⟨13463414638805465629575461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143609756147258300048804917 13463414638805465629575461)
        ·
          refine ⟨2524390244776024805545399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13463414638805465629575461 2524390244776024805545399)
          ·
            refine ⟨3786585367164037208318099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524390244776024805545399 3786585367164037208318099)
            ·
              refine ⟨5679878050746055812477149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786585367164037208318099 5679878050746055812477149)
              ·
                refine ⟨2129954269029770929678931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5679878050746055812477149 2129954269029770929678931)
                ·
                  refine ⟨3194931403544656394518397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129954269029770929678931 3194931403544656394518397)
                  ·
                    refine ⟨1198099276329246147944399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194931403544656394518397 1198099276329246147944399)
                    ·
                      rfl

theorem cell22_3499935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 3].length) (baseStart_3499935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499935 prefixEnd_3499935 := by exact prefixLift 3499935
  have htrace : WordTrace (prefixWord ++ tailWord_3499935) baseStart_3499935 baseEnd_3499935 := by
    simpa [prefixWord, tailWord_3499935, baseEnd_3499935] using wordTrace_append hprefix tailTrace_3499935
  have hstable : (prefixWord ++ tailWord_3499935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499935).length < 2 ^ (prefixWord ++ tailWord_3499935).sum := by decide
  have hdescent : baseEnd_3499935 < baseStart_3499935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499989 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3499989 : Nat := 118140960795 + 3499989 * 2 ^ 59
def prefixEnd_3499989 : Nat := 4983230072969 + 3 ^ 40 * 3499989 * 2
def baseEnd_3499989 : Nat := 1198117761632808007094233

theorem tailTrace_3499989 : CollatzResearch.WordTrace tailWord_3499989 prefixEnd_3499989 1198117761632808007094233 := by
  unfold tailWord_3499989
  simp only [CollatzResearch.WordTrace]
  refine ⟨127655086117145078376959021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85103390744763385584639347 127655086117145078376959021)
  ·
    refine ⟨47870657293929404391359633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127655086117145078376959021 47870657293929404391359633)
    ·
      refine ⟨35902992970447053293519725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47870657293929404391359633 35902992970447053293519725)
      ·
        refine ⟨13463622363917644985069897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35902992970447053293519725 13463622363917644985069897)
        ·
          refine ⟨10097716772938233738802423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13463622363917644985069897 10097716772938233738802423)
          ·
            refine ⟨15146575159407350608203635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10097716772938233738802423 15146575159407350608203635)
            ·
              refine ⟨22719862739111025912305453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15146575159407350608203635 22719862739111025912305453)
              ·
                refine ⟨8519948527166634717114545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22719862739111025912305453 8519948527166634717114545)
                ·
                  refine ⟨6389961395374976037835909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8519948527166634717114545 6389961395374976037835909)
                  ·
                    refine ⟨1198117761632808007094233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6389961395374976037835909 1198117761632808007094233)
                    ·
                      rfl

theorem cell22_3499989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3499989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3499989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3499989 prefixEnd_3499989 := by exact prefixLift 3499989
  have htrace : WordTrace (prefixWord ++ tailWord_3499989) baseStart_3499989 baseEnd_3499989 := by
    simpa [prefixWord, tailWord_3499989, baseEnd_3499989] using wordTrace_append hprefix tailTrace_3499989
  have hstable : (prefixWord ++ tailWord_3499989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499989).length < 2 ^ (prefixWord ++ tailWord_3499989).sum := by decide
  have hdescent : baseEnd_3499989 < baseStart_3499989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500096 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_3500096 : Nat := 118140960795 + 3500096 * 2 ^ 59
def prefixEnd_3500096 : Nat := 4983230072969 + 3 ^ 40 * 3500096 * 2
def baseEnd_3500096 : Nat := 1198154389919495394668905

theorem tailTrace_3500096 : CollatzResearch.WordTrace tailWord_3500096 prefixEnd_3500096 1198154389919495394668905 := by
  unfold tailWord_3500096
  simp only [CollatzResearch.WordTrace]
  refine ⟨63829494363878717825552071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85105992485171623767402761 63829494363878717825552071)
  ·
    refine ⟨95744241545818076738328107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63829494363878717825552071 95744241545818076738328107)
    ·
      refine ⟨143616362318727115107492161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95744241545818076738328107 143616362318727115107492161)
      ·
        refine ⟨107712271739045336330619121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143616362318727115107492161 107712271739045336330619121)
        ·
          refine ⟨80784203804284002247964341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107712271739045336330619121 80784203804284002247964341)
          ·
            refine ⟨7573519106651625210746657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80784203804284002247964341 7573519106651625210746657)
            ·
              refine ⟨5680139329988718908059993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7573519106651625210746657 5680139329988718908059993)
              ·
                refine ⟨4260104497491539181044995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5680139329988718908059993 4260104497491539181044995)
                ·
                  refine ⟨6390156746237308771567493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260104497491539181044995 6390156746237308771567493)
                  ·
                    refine ⟨1198154389919495394668905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6390156746237308771567493 1198154389919495394668905)
                    ·
                      rfl

theorem cell22_3500096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_3500096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500096 prefixEnd_3500096 := by exact prefixLift 3500096
  have htrace : WordTrace (prefixWord ++ tailWord_3500096) baseStart_3500096 baseEnd_3500096 := by
    simpa [prefixWord, tailWord_3500096, baseEnd_3500096] using wordTrace_append hprefix tailTrace_3500096
  have hstable : (prefixWord ++ tailWord_3500096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500096).length < 2 ^ (prefixWord ++ tailWord_3500096).sum := by decide
  have hdescent : baseEnd_3500096 < baseStart_3500096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500128 : List Nat := [2, 1, 1, 3, 2, 4, 3, 2, 4]
def baseStart_3500128 : Nat := 118140960795 + 3500128 * 2 ^ 59
def prefixEnd_3500128 : Nat := 4983230072969 + 3 ^ 40 * 3500128 * 2
def baseEnd_3500128 : Nat := 399388448057819325956269

theorem tailTrace_3500128 : CollatzResearch.WordTrace tailWord_3500128 prefixEnd_3500128 399388448057819325956269 := by
  unfold tailWord_3500128
  simp only [CollatzResearch.WordTrace]
  refine ⟨63830077931820752558134519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85106770575761003410846025 63830077931820752558134519)
  ·
    refine ⟨95745116897731128837201779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63830077931820752558134519 95745116897731128837201779)
    ·
      refine ⟨143617675346596693255802669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95745116897731128837201779 143617675346596693255802669)
      ·
        refine ⟨53856628254973759970926001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143617675346596693255802669 53856628254973759970926001)
        ·
          refine ⟨40392471191230319978194501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53856628254973759970926001 40392471191230319978194501)
          ·
            refine ⟨7573588348355684995911469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40392471191230319978194501 7573588348355684995911469)
            ·
              refine ⟨2840095630633381873466801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7573588348355684995911469 2840095630633381873466801)
              ·
                refine ⟨2130071722975036405100101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840095630633381873466801 2130071722975036405100101)
                ·
                  refine ⟨399388448057819325956269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130071722975036405100101 399388448057819325956269)
                  ·
                    rfl

theorem cell22_3500128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 4].length) (baseStart_3500128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500128 prefixEnd_3500128 := by exact prefixLift 3500128
  have htrace : WordTrace (prefixWord ++ tailWord_3500128) baseStart_3500128 baseEnd_3500128 := by
    simpa [prefixWord, tailWord_3500128, baseEnd_3500128] using wordTrace_append hprefix tailTrace_3500128
  have hstable : (prefixWord ++ tailWord_3500128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500128).length < 2 ^ (prefixWord ++ tailWord_3500128).sum := by decide
  have hdescent : baseEnd_3500128 < baseStart_3500128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500143 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 2, 3]
def baseStart_3500143 : Nat := 118140960795 + 3500143 * 2 ^ 59
def prefixEnd_3500143 : Nat := 4983230072969 + 3 ^ 40 * 3500143 * 2
def baseEnd_3500143 : Nat := 1198170478980002938743761

theorem tailTrace_3500143 : CollatzResearch.WordTrace tailWord_3500143 prefixEnd_3500143 1198170478980002938743761 := by
  unfold tailWord_3500143
  simp only [CollatzResearch.WordTrace]
  refine ⟨127660702958587162678065083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85107135305724775118710055 127660702958587162678065083)
  ·
    refine ⟨191491054437880744017097625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127660702958587162678065083 191491054437880744017097625)
    ·
      refine ⟨143618290828410558012823219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191491054437880744017097625 143618290828410558012823219)
      ·
        refine ⟨215427436242615837019234829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143618290828410558012823219 215427436242615837019234829)
        ·
          refine ⟨80785288590980938882213061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215427436242615837019234829 80785288590980938882213061)
          ·
            refine ⟨15147241610808926040414949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80785288590980938882213061 15147241610808926040414949)
            ·
              refine ⟨2840107802026673632577803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15147241610808926040414949 2840107802026673632577803)
              ·
                refine ⟨4260161703040010448866705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840107802026673632577803 4260161703040010448866705)
                ·
                  refine ⟨3195121277280007836650029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4260161703040010448866705 3195121277280007836650029)
                  ·
                    refine ⟨1198170478980002938743761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3195121277280007836650029 1198170478980002938743761)
                    ·
                      rfl

theorem cell22_3500143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 3].length) (baseStart_3500143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500143 prefixEnd_3500143 := by exact prefixLift 3500143
  have htrace : WordTrace (prefixWord ++ tailWord_3500143) baseStart_3500143 baseEnd_3500143 := by
    simpa [prefixWord, tailWord_3500143, baseEnd_3500143] using wordTrace_append hprefix tailTrace_3500143
  have hstable : (prefixWord ++ tailWord_3500143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500143).length < 2 ^ (prefixWord ++ tailWord_3500143).sum := by decide
  have hdescent : baseEnd_3500143 < baseStart_3500143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500190 : List Nat := [4, 3, 1, 1, 4, 1, 1, 7]
def baseStart_3500190 : Nat := 118140960795 + 3500190 * 2 ^ 59
def prefixEnd_3500190 : Nat := 4983230072969 + 3 ^ 40 * 3500190 * 2
def baseEnd_3500190 : Nat := 133131840893390053646513

theorem tailTrace_3500190 : CollatzResearch.WordTrace tailWord_3500190 prefixEnd_3500190 133131840893390053646513 := by
  unfold tailWord_3500190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15957802148677111213128253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85108278126277926470017349 15957802148677111213128253)
  ·
    refine ⟨5984175805753916704923095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15957802148677111213128253 5984175805753916704923095)
    ·
      refine ⟨8976263708630875057384643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5984175805753916704923095 8976263708630875057384643)
      ·
        refine ⟨13464395562946312586076965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8976263708630875057384643 13464395562946312586076965)
        ·
          refine ⟨2524574168052433609889431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13464395562946312586076965 2524574168052433609889431)
          ·
            refine ⟨3786861252078650414834147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524574168052433609889431 3786861252078650414834147)
            ·
              refine ⟨5680291878117975622251221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786861252078650414834147 5680291878117975622251221)
              ·
                refine ⟨133131840893390053646513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5680291878117975622251221 133131840893390053646513)
                ·
                  rfl

theorem cell22_3500190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_3500190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500190 prefixEnd_3500190 := by exact prefixLift 3500190
  have htrace : WordTrace (prefixWord ++ tailWord_3500190) baseStart_3500190 baseEnd_3500190 := by
    simpa [prefixWord, tailWord_3500190, baseEnd_3500190] using wordTrace_append hprefix tailTrace_3500190
  have hstable : (prefixWord ++ tailWord_3500190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500190).length < 2 ^ (prefixWord ++ tailWord_3500190).sum := by decide
  have hdescent : baseEnd_3500190 < baseStart_3500190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500222 : List Nat := [4, 2, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_3500222 : Nat := 118140960795 + 3500222 * 2 ^ 59
def prefixEnd_3500222 : Nat := 4983230072969 + 3 ^ 40 * 3500222 * 2
def baseEnd_3500222 : Nat := 1198197522294473066018519

theorem tailTrace_3500222 : CollatzResearch.WordTrace tailWord_3500222 prefixEnd_3500222 1198197522294473066018519 := by
  unfold tailWord_3500222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15957948040662619896273865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85109056216867306113460613 15957948040662619896273865)
  ·
    refine ⟨11968461030496964922205399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15957948040662619896273865 11968461030496964922205399)
    ·
      refine ⟨17952691545745447383308099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11968461030496964922205399 17952691545745447383308099)
      ·
        refine ⟨26929037318618171074962149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17952691545745447383308099 26929037318618171074962149)
        ·
          refine ⟨5049194497240907076555403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26929037318618171074962149 5049194497240907076555403)
          ·
            refine ⟨7573791745861360614833105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049194497240907076555403 7573791745861360614833105)
            ·
              refine ⟨5680343809396020461124829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7573791745861360614833105 5680343809396020461124829)
              ·
                refine ⟨2130128928523507672921811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5680343809396020461124829 2130128928523507672921811)
                ·
                  refine ⟨3195193392785261509382717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130128928523507672921811 3195193392785261509382717)
                  ·
                    refine ⟨1198197522294473066018519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3195193392785261509382717 1198197522294473066018519)
                    ·
                      rfl

theorem cell22_3500222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_3500222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500222 prefixEnd_3500222 := by exact prefixLift 3500222
  have htrace : WordTrace (prefixWord ++ tailWord_3500222) baseStart_3500222 baseEnd_3500222 := by
    simpa [prefixWord, tailWord_3500222, baseEnd_3500222] using wordTrace_append hprefix tailTrace_3500222
  have hstable : (prefixWord ++ tailWord_3500222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500222).length < 2 ^ (prefixWord ++ tailWord_3500222).sum := by decide
  have hdescent : baseEnd_3500222 < baseStart_3500222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500252 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 5]
def baseStart_3500252 : Nat := 118140960795 + 3500252 * 2 ^ 59
def prefixEnd_3500252 : Nat := 4983230072969 + 3 ^ 40 * 3500252 * 2
def baseEnd_3500252 : Nat := 399402597302520995922809

theorem tailTrace_3500252 : CollatzResearch.WordTrace tailWord_3500252 prefixEnd_3500252 399402597302520995922809 := by
  unfold tailWord_3500252
  simp only [CollatzResearch.WordTrace]
  refine ⟨63832339257596137146891505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85109785676794849529188673 63832339257596137146891505)
  ·
    refine ⟨47874254443197102860168629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63832339257596137146891505 47874254443197102860168629)
    ·
      refine ⟨4488211354049728393140809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47874254443197102860168629 4488211354049728393140809)
      ·
        refine ⟨3366158515537296294855607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4488211354049728393140809 3366158515537296294855607)
        ·
          refine ⟨5049237773305944442283411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366158515537296294855607 5049237773305944442283411)
          ·
            refine ⟨7573856659958916663425117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049237773305944442283411 7573856659958916663425117)
            ·
              refine ⟨2840196247484593748784419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7573856659958916663425117 2840196247484593748784419)
              ·
                refine ⟨4260294371226890623176629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840196247484593748784419 4260294371226890623176629)
                ·
                  refine ⟨399402597302520995922809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4260294371226890623176629 399402597302520995922809)
                  ·
                    rfl

theorem cell22_3500252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_3500252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500252 prefixEnd_3500252 := by exact prefixLift 3500252
  have htrace : WordTrace (prefixWord ++ tailWord_3500252) baseStart_3500252 baseEnd_3500252 := by
    simpa [prefixWord, tailWord_3500252, baseEnd_3500252] using wordTrace_append hprefix tailTrace_3500252
  have hstable : (prefixWord ++ tailWord_3500252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500252).length < 2 ^ (prefixWord ++ tailWord_3500252).sum := by decide
  have hdescent : baseEnd_3500252 < baseStart_3500252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500278 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_3500278 : Nat := 118140960795 + 3500278 * 2 ^ 59
def prefixEnd_3500278 : Nat := 4983230072969 + 3 ^ 40 * 3500278 * 2
def baseEnd_3500278 : Nat := 1198216692238907586618347

theorem tailTrace_3500278 : CollatzResearch.WordTrace tailWord_3500278 prefixEnd_3500278 1198216692238907586618347 := by
  unfold tailWord_3500278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7979101675818630045889343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85110417875398720489486325 7979101675818630045889343)
  ·
    refine ⟨11968652513727945068834015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7979101675818630045889343 11968652513727945068834015)
    ·
      refine ⟨17952978770591917603251023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11968652513727945068834015 17952978770591917603251023)
      ·
        refine ⟨26929468155887876404876535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17952978770591917603251023 26929468155887876404876535)
        ·
          refine ⟨40394202233831814607314803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26929468155887876404876535 40394202233831814607314803)
          ·
            refine ⟨60591303350747721910972205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40394202233831814607314803 60591303350747721910972205)
            ·
              refine ⟨22721738756530395716614577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60591303350747721910972205 22721738756530395716614577)
              ·
                refine ⟨17041304067397796787460933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22721738756530395716614577 17041304067397796787460933)
                ·
                  refine ⟨3195244512637086897648925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17041304067397796787460933 3195244512637086897648925)
                  ·
                    refine ⟨1198216692238907586618347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3195244512637086897648925 1198216692238907586618347)
                    ·
                      rfl

theorem cell22_3500278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_3500278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500278 prefixEnd_3500278 := by exact prefixLift 3500278
  have htrace : WordTrace (prefixWord ++ tailWord_3500278) baseStart_3500278 baseEnd_3500278 := by
    simpa [prefixWord, tailWord_3500278, baseEnd_3500278] using wordTrace_append hprefix tailTrace_3500278
  have hstable : (prefixWord ++ tailWord_3500278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500278).length < 2 ^ (prefixWord ++ tailWord_3500278).sum := by decide
  have hdescent : baseEnd_3500278 < baseStart_3500278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500351 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 2, 5]
def baseStart_3500351 : Nat := 118140960795 + 3500351 * 2 ^ 59
def prefixEnd_3500351 : Nat := 4983230072969 + 3 ^ 40 * 3500351 * 2
def baseEnd_3500351 : Nat := 1198241681630759729543123

theorem tailTrace_3500351 : CollatzResearch.WordTrace tailWord_3500351 prefixEnd_3500351 1198241681630759729543123 := by
  unfold tailWord_3500351
  simp only [CollatzResearch.WordTrace]
  refine ⟨127668289341833614201636907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85112192894555742801091271 127668289341833614201636907)
  ·
    refine ⟨191502434012750421302455361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127668289341833614201636907 191502434012750421302455361)
    ·
      refine ⟨143626825509562815976841521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191502434012750421302455361 143626825509562815976841521)
      ·
        refine ⟨107720119132172111982631141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143626825509562815976841521 107720119132172111982631141)
        ·
          refine ⟨20197522337282270996743339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107720119132172111982631141 20197522337282270996743339)
          ·
            refine ⟨30296283505923406495115009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20197522337282270996743339 30296283505923406495115009)
            ·
              refine ⟨22722212629442554871336257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30296283505923406495115009 22722212629442554871336257)
              ·
                refine ⟨17041659472081916153502193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22722212629442554871336257 17041659472081916153502193)
                ·
                  refine ⟨12781244604061437115126645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17041659472081916153502193 12781244604061437115126645)
                  ·
                    refine ⟨1198241681630759729543123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12781244604061437115126645 1198241681630759729543123)
                    ·
                      rfl

theorem cell22_3500351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_3500351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500351 prefixEnd_3500351 := by exact prefixLift 3500351
  have htrace : WordTrace (prefixWord ++ tailWord_3500351) baseStart_3500351 baseEnd_3500351 := by
    simpa [prefixWord, tailWord_3500351, baseEnd_3500351] using wordTrace_append hprefix tailTrace_3500351
  have hstable : (prefixWord ++ tailWord_3500351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500351).length < 2 ^ (prefixWord ++ tailWord_3500351).sum := by decide
  have hdescent : baseEnd_3500351 < baseStart_3500351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500400 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 1, 4]
def baseStart_3500400 : Nat := 118140960795 + 3500400 * 2 ^ 59
def prefixEnd_3500400 : Nat := 4983230072969 + 3 ^ 40 * 3500400 * 2
def baseEnd_3500400 : Nat := 1198258455332139935067973

theorem tailTrace_3500400 : CollatzResearch.WordTrace tailWord_3500400 prefixEnd_3500400 1198258455332139935067973 := by
  unfold tailWord_3500400
  simp only [CollatzResearch.WordTrace]
  refine ⟨63835038259328047785085327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85113384345770730380113769 63835038259328047785085327)
  ·
    refine ⟨95752557388992071677627991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63835038259328047785085327 95752557388992071677627991)
    ·
      refine ⟨143628836083488107516441987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95752557388992071677627991 143628836083488107516441987)
      ·
        refine ⟨215443254125232161274662981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143628836083488107516441987 215443254125232161274662981)
        ·
          refine ⟨40395610148481030238999309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215443254125232161274662981 40395610148481030238999309)
          ·
            refine ⟨15148353805680386339624741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40395610148481030238999309 15148353805680386339624741)
            ·
              refine ⟨2840316338565072438679639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15148353805680386339624741 2840316338565072438679639)
              ·
                refine ⟨4260474507847608658019459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840316338565072438679639 4260474507847608658019459)
                ·
                  refine ⟨6390711761771412987029189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260474507847608658019459 6390711761771412987029189)
                  ·
                    refine ⟨1198258455332139935067973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6390711761771412987029189 1198258455332139935067973)
                    ·
                      rfl

theorem cell22_3500400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 4].length) (baseStart_3500400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500400 prefixEnd_3500400 := by exact prefixLift 3500400
  have htrace : WordTrace (prefixWord ++ tailWord_3500400) baseStart_3500400 baseEnd_3500400 := by
    simpa [prefixWord, tailWord_3500400, baseEnd_3500400] using wordTrace_append hprefix tailTrace_3500400
  have hstable : (prefixWord ++ tailWord_3500400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500400).length < 2 ^ (prefixWord ++ tailWord_3500400).sum := by decide
  have hdescent : baseEnd_3500400 < baseStart_3500400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500430 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_3500430 : Nat := 118140960795 + 3500430 * 2 ^ 59
def prefixEnd_3500430 : Nat := 4983230072969 + 3 ^ 40 * 3500430 * 2
def baseEnd_3500430 : Nat := 1198268724945229856817881

theorem tailTrace_3500430 : CollatzResearch.WordTrace tailWord_3500430 prefixEnd_3500430 1198268724945229856817881 := by
  unfold tailWord_3500430
  simp only [CollatzResearch.WordTrace]
  refine ⟨15958896338568426336720343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85114113805698273795841829 15958896338568426336720343)
  ·
    refine ⟨23938344507852639505080515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15958896338568426336720343 23938344507852639505080515)
    ·
      refine ⟨35907516761778959257620773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23938344507852639505080515 35907516761778959257620773)
      ·
        refine ⟨6732659392833554860803895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35907516761778959257620773 6732659392833554860803895)
        ·
          refine ⟨10098989089250332291205843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6732659392833554860803895 10098989089250332291205843)
          ·
            refine ⟨15148483633875498436808765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10098989089250332291205843 15148483633875498436808765)
            ·
              refine ⟨5680681362703311913803287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15148483633875498436808765 5680681362703311913803287)
              ·
                refine ⟨8521022044054967870704931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680681362703311913803287 8521022044054967870704931)
                ·
                  refine ⟨12781533066082451806057397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8521022044054967870704931 12781533066082451806057397)
                  ·
                    refine ⟨1198268724945229856817881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12781533066082451806057397 1198268724945229856817881)
                    ·
                      rfl

theorem cell22_3500430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_3500430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500430 prefixEnd_3500430 := by exact prefixLift 3500430
  have htrace : WordTrace (prefixWord ++ tailWord_3500430) baseStart_3500430 baseEnd_3500430 := by
    simpa [prefixWord, tailWord_3500430, baseEnd_3500430] using wordTrace_append hprefix tailTrace_3500430
  have hstable : (prefixWord ++ tailWord_3500430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500430).length < 2 ^ (prefixWord ++ tailWord_3500430).sum := by decide
  have hdescent : baseEnd_3500430 < baseStart_3500430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500441 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_3500441 : Nat := 118140960795 + 3500441 * 2 ^ 59
def prefixEnd_3500441 : Nat := 4983230072969 + 3 ^ 40 * 3500441 * 2
def baseEnd_3500441 : Nat := 1198272490470029494792847

theorem tailTrace_3500441 : CollatzResearch.WordTrace tailWord_3500441 prefixEnd_3500441 1198272490470029494792847 := by
  unfold tailWord_3500441
  simp only [CollatzResearch.WordTrace]
  refine ⟨127671571911507559572413177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85114381274338373048275451 127671571911507559572413177)
  ·
    refine ⟨95753678933630669679309883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127671571911507559572413177 95753678933630669679309883)
    ·
      refine ⟨143630518400446004518964825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95753678933630669679309883 143630518400446004518964825)
      ·
        refine ⟨107722888800334503389223619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143630518400446004518964825 107722888800334503389223619)
        ·
          refine ⟨161584333200501755083835429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107722888800334503389223619 161584333200501755083835429)
          ·
            refine ⟨30297062475094079078219143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161584333200501755083835429 30297062475094079078219143)
            ·
              refine ⟨45445593712641118617328715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30297062475094079078219143 45445593712641118617328715)
              ·
                refine ⟨68168390568961677925993073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45445593712641118617328715 68168390568961677925993073)
                ·
                  refine ⟨51126292926721258444494805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68168390568961677925993073 51126292926721258444494805)
                  ·
                    refine ⟨1198272490470029494792847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51126292926721258444494805 1198272490470029494792847)
                    ·
                      rfl

theorem cell22_3500441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_3500441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500441 prefixEnd_3500441 := by exact prefixLift 3500441
  have htrace : WordTrace (prefixWord ++ tailWord_3500441) baseStart_3500441 baseEnd_3500441 := by
    simpa [prefixWord, tailWord_3500441, baseEnd_3500441] using wordTrace_append hprefix tailTrace_3500441
  have hstable : (prefixWord ++ tailWord_3500441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500441).length < 2 ^ (prefixWord ++ tailWord_3500441).sum := by decide
  have hdescent : baseEnd_3500441 < baseStart_3500441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500449 : List Nat := [1, 2, 3, 5, 1, 2, 1, 3, 4]
def baseStart_3500449 : Nat := 118140960795 + 3500449 * 2 ^ 59
def prefixEnd_3500449 : Nat := 4983230072969 + 3 ^ 40 * 3500449 * 2
def baseEnd_3500449 : Nat := 399425076344506713530941

theorem tailTrace_3500449 : CollatzResearch.WordTrace tailWord_3500449 prefixEnd_3500449 399425076344506713530941 := by
  unfold tailWord_3500449
  simp only [CollatzResearch.WordTrace]
  refine ⟨127671863695478576938704401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85114575796985717959136267 127671863695478576938704401)
  ·
    refine ⟨95753897771608932704028301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127671863695478576938704401 95753897771608932704028301)
    ·
      refine ⟨35907711664353349764010613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95753897771608932704028301 35907711664353349764010613)
      ·
        refine ⟨3366347968533126540375995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35907711664353349764010613 3366347968533126540375995)
        ·
          refine ⟨5049521952799689810563993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366347968533126540375995 5049521952799689810563993)
          ·
            refine ⟨3787141464599767357922995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5049521952799689810563993 3787141464599767357922995)
            ·
              refine ⟨5680712196899651036884493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3787141464599767357922995 5680712196899651036884493)
              ·
                refine ⟨2130267073837369138831685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5680712196899651036884493 2130267073837369138831685)
                ·
                  refine ⟨399425076344506713530941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130267073837369138831685 399425076344506713530941)
                  ·
                    rfl

theorem cell22_3500449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 4].length) (baseStart_3500449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500449 prefixEnd_3500449 := by exact prefixLift 3500449
  have htrace : WordTrace (prefixWord ++ tailWord_3500449) baseStart_3500449 baseEnd_3500449 := by
    simpa [prefixWord, tailWord_3500449, baseEnd_3500449] using wordTrace_append hprefix tailTrace_3500449
  have hstable : (prefixWord ++ tailWord_3500449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500449).length < 2 ^ (prefixWord ++ tailWord_3500449).sum := by decide
  have hdescent : baseEnd_3500449 < baseStart_3500449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500481 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3500481 : Nat := 118140960795 + 3500481 * 2 ^ 59
def prefixEnd_3500481 : Nat := 4983230072969 + 3 ^ 40 * 3500481 * 2
def baseEnd_3500481 : Nat := 1198286183287482723792725

theorem tailTrace_3500481 : CollatzResearch.WordTrace tailWord_3500481 prefixEnd_3500481 1198286183287482723792725 := by
  unfold tailWord_3500481
  simp only [CollatzResearch.WordTrace]
  refine ⟨127673030831362646403869297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85115353887575097602579531 127673030831362646403869297)
  ·
    refine ⟨95754773123521984802901973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127673030831362646403869297 95754773123521984802901973)
    ·
      refine ⟨2244252495082546518818015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 95754773123521984802901973 2244252495082546518818015)
      ·
        refine ⟨3366378742623819778227023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244252495082546518818015 3366378742623819778227023)
        ·
          refine ⟨5049568113935729667340535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366378742623819778227023 5049568113935729667340535)
          ·
            refine ⟨7574352170903594501010803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049568113935729667340535 7574352170903594501010803)
            ·
              refine ⟨11361528256355391751516205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7574352170903594501010803 11361528256355391751516205)
              ·
                refine ⟨4260573096133271906818577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11361528256355391751516205 4260573096133271906818577)
                ·
                  refine ⟨3195429822099953930113933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4260573096133271906818577 3195429822099953930113933)
                  ·
                    refine ⟨1198286183287482723792725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3195429822099953930113933 1198286183287482723792725)
                    ·
                      rfl

theorem cell22_3500481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3500481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500481 prefixEnd_3500481 := by exact prefixLift 3500481
  have htrace : WordTrace (prefixWord ++ tailWord_3500481) baseStart_3500481 baseEnd_3500481 := by
    simpa [prefixWord, tailWord_3500481, baseEnd_3500481] using wordTrace_append hprefix tailTrace_3500481
  have hstable : (prefixWord ++ tailWord_3500481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500481).length < 2 ^ (prefixWord ++ tailWord_3500481).sum := by decide
  have hdescent : baseEnd_3500481 < baseStart_3500481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500526 : List Nat := [4, 1, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_3500526 : Nat := 118140960795 + 3500526 * 2 ^ 59
def prefixEnd_3500526 : Nat := 4983230072969 + 3 ^ 40 * 3500526 * 2
def baseEnd_3500526 : Nat := 1198301587707117606417587

theorem tailTrace_3500526 : CollatzResearch.WordTrace tailWord_3500526 prefixEnd_3500526 1198301587707117606417587 := by
  unfold tailWord_3500526
  simp only [CollatzResearch.WordTrace]
  refine ⟨15959334014524952386157179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85116448077466412726171621 15959334014524952386157179)
  ·
    refine ⟨23939001021787428579235769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15959334014524952386157179 23939001021787428579235769)
    ·
      refine ⟨17954250766340571434426827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23939001021787428579235769 17954250766340571434426827)
      ·
        refine ⟨26931376149510857151640241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17954250766340571434426827 26931376149510857151640241)
        ·
          refine ⟨20198532112133142863730181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26931376149510857151640241 20198532112133142863730181)
          ·
            refine ⟨3787224771024964286949409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20198532112133142863730181 3787224771024964286949409)
            ·
              refine ⟨2840418578268723215212057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787224771024964286949409 2840418578268723215212057)
              ·
                refine ⟨2130313933701542411409043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840418578268723215212057 2130313933701542411409043)
                ·
                  refine ⟨3195470900552313617113565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130313933701542411409043 3195470900552313617113565)
                  ·
                    refine ⟨1198301587707117606417587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3195470900552313617113565 1198301587707117606417587)
                    ·
                      rfl

theorem cell22_3500526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_3500526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500526 prefixEnd_3500526 := by exact prefixLift 3500526
  have htrace : WordTrace (prefixWord ++ tailWord_3500526) baseStart_3500526 baseEnd_3500526 := by
    simpa [prefixWord, tailWord_3500526, baseEnd_3500526] using wordTrace_append hprefix tailTrace_3500526
  have hstable : (prefixWord ++ tailWord_3500526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500526).length < 2 ^ (prefixWord ++ tailWord_3500526).sum := by decide
  have hdescent : baseEnd_3500526 < baseStart_3500526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500563 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 1, 6]
def baseStart_3500563 : Nat := 118140960795 + 3500563 * 2 ^ 59
def prefixEnd_3500563 : Nat := 4983230072969 + 3 ^ 40 * 3500563 * 2
def baseEnd_3500563 : Nat := 1198314253563261843242473

theorem tailTrace_3500563 : CollatzResearch.WordTrace tailWord_3500563 prefixEnd_3500563 1198314253563261843242473 := by
  unfold tailWord_3500563
  simp only [CollatzResearch.WordTrace]
  refine ⟨127676021617065574408354343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85117347744710382938902895 127676021617065574408354343)
  ·
    refine ⟨191514032425598361612531515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127676021617065574408354343 191514032425598361612531515)
    ·
      refine ⟨287271048638397542418797273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191514032425598361612531515 287271048638397542418797273)
      ·
        refine ⟨215453286478798156814097955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287271048638397542418797273 215453286478798156814097955)
        ·
          refine ⟨323179929718197235221146933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215453286478798156814097955 323179929718197235221146933)
          ·
            refine ⟨30298118411080990801982525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 323179929718197235221146933 30298118411080990801982525)
            ·
              refine ⟨11361794404155371550743447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30298118411080990801982525 11361794404155371550743447)
              ·
                refine ⟨17042691606233057326115171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11361794404155371550743447 17042691606233057326115171)
                ·
                  refine ⟨25564037409349585989172757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17042691606233057326115171 25564037409349585989172757)
                  ·
                    refine ⟨1198314253563261843242473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25564037409349585989172757 1198314253563261843242473)
                    ·
                      rfl

theorem cell22_3500563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_3500563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500563 prefixEnd_3500563 := by exact prefixLift 3500563
  have htrace : WordTrace (prefixWord ++ tailWord_3500563) baseStart_3500563 baseEnd_3500563 := by
    simpa [prefixWord, tailWord_3500563, baseEnd_3500563] using wordTrace_append hprefix tailTrace_3500563
  have hstable : (prefixWord ++ tailWord_3500563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500563).length < 2 ^ (prefixWord ++ tailWord_3500563).sum := by decide
  have hdescent : baseEnd_3500563 < baseStart_3500563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500565 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_3500565 : Nat := 118140960795 + 3500565 * 2 ^ 59
def prefixEnd_3500565 : Nat := 4983230072969 + 3 ^ 40 * 3500565 * 2
def baseEnd_3500565 : Nat := 1198314938204134504692467

theorem tailTrace_3500565 : CollatzResearch.WordTrace tailWord_3500565 prefixEnd_3500565 1198314938204134504692467 := by
  unfold tailWord_3500565
  simp only [CollatzResearch.WordTrace]
  refine ⟨127676094563058328749927149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85117396375372219166618099 127676094563058328749927149)
  ·
    refine ⟨47878535461146873281222681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127676094563058328749927149 47878535461146873281222681)
    ·
      refine ⟨35908901595860154960917011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47878535461146873281222681 35908901595860154960917011)
      ·
        refine ⟨53863352393790232441375517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35908901595860154960917011 53863352393790232441375517)
        ·
          refine ⟨20198757147671337165515819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53863352393790232441375517 20198757147671337165515819)
          ·
            refine ⟨30298135721507005748273729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20198757147671337165515819 30298135721507005748273729)
            ·
              refine ⟨22723601791130254311205297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30298135721507005748273729 22723601791130254311205297)
              ·
                refine ⟨17042701343347690733403973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22723601791130254311205297 17042701343347690733403973)
                ·
                  refine ⟨3195506501877692012513245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17042701343347690733403973 3195506501877692012513245)
                  ·
                    refine ⟨1198314938204134504692467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3195506501877692012513245 1198314938204134504692467)
                    ·
                      rfl

theorem cell22_3500565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_3500565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500565 prefixEnd_3500565 := by exact prefixLift 3500565
  have htrace : WordTrace (prefixWord ++ tailWord_3500565) baseStart_3500565 baseEnd_3500565 := by
    simpa [prefixWord, tailWord_3500565, baseEnd_3500565] using wordTrace_append hprefix tailTrace_3500565
  have hstable : (prefixWord ++ tailWord_3500565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500565).length < 2 ^ (prefixWord ++ tailWord_3500565).sum := by decide
  have hdescent : baseEnd_3500565 < baseStart_3500565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500608 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_3500608 : Nat := 118140960795 + 3500608 * 2 ^ 59
def prefixEnd_3500608 : Nat := 4983230072969 + 3 ^ 40 * 3500608 * 2
def baseEnd_3500608 : Nat := 1198329657982896725867335

theorem tailTrace_3500608 : CollatzResearch.WordTrace tailWord_3500608 prefixEnd_3500608 1198329657982896725867335 := by
  unfold tailWord_3500608
  simp only [CollatzResearch.WordTrace]
  refine ⟨63838831450951273546871239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85118441934601698062494985 63838831450951273546871239)
  ·
    refine ⟨95758247176426910320306859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63838831450951273546871239 95758247176426910320306859)
    ·
      refine ⟨143637370764640365480460289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95758247176426910320306859 143637370764640365480460289)
      ·
        refine ⟨107728028073480274110345217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143637370764640365480460289 107728028073480274110345217)
        ·
          refine ⟨80796021055110205582758913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107728028073480274110345217 80796021055110205582758913)
          ·
            refine ⟨60597015791332654187069185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80796021055110205582758913 60597015791332654187069185)
            ·
              refine ⟨45447761843499490640301889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60597015791332654187069185 45447761843499490640301889)
              ·
                refine ⟨34085821382624617980226417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45447761843499490640301889 34085821382624617980226417)
                ·
                  refine ⟨25564366036968463485169813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34085821382624617980226417 25564366036968463485169813)
                  ·
                    refine ⟨1198329657982896725867335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25564366036968463485169813 1198329657982896725867335)
                    ·
                      rfl

theorem cell22_3500608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_3500608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500608 prefixEnd_3500608 := by exact prefixLift 3500608
  have htrace : WordTrace (prefixWord ++ tailWord_3500608) baseStart_3500608 baseEnd_3500608 := by
    simpa [prefixWord, tailWord_3500608, baseEnd_3500608] using wordTrace_append hprefix tailTrace_3500608
  have hstable : (prefixWord ++ tailWord_3500608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500608).length < 2 ^ (prefixWord ++ tailWord_3500608).sum := by decide
  have hdescent : baseEnd_3500608 < baseStart_3500608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500623 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 7]
def baseStart_3500623 : Nat := 118140960795 + 3500623 * 2 ^ 59
def prefixEnd_3500623 : Nat := 4983230072969 + 3 ^ 40 * 3500623 * 2
def baseEnd_3500623 : Nat := 399444930929813895580763

theorem tailTrace_3500623 : CollatzResearch.WordTrace tailWord_3500623 prefixEnd_3500623 399444930929813895580763 := by
  unfold tailWord_3500623
  simp only [CollatzResearch.WordTrace]
  refine ⟨127678209996848204655538523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85118806664565469770359015 127678209996848204655538523)
  ·
    refine ⟨191517314995272306983307785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127678209996848204655538523 191517314995272306983307785)
    ·
      refine ⟨143637986246454230237480839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191517314995272306983307785 143637986246454230237480839)
      ·
        refine ⟨215456979369681345356221259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143637986246454230237480839 215456979369681345356221259)
        ·
          refine ⟨323185469054522018034331889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215456979369681345356221259 323185469054522018034331889)
          ·
            refine ⟨242389101790891513525748917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323185469054522018034331889 242389101790891513525748917)
            ·
              refine ⟨22723978292896079393038961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242389101790891513525748917 22723978292896079393038961)
              ·
                refine ⟨17042983719672059544779221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22723978292896079393038961 17042983719672059544779221)
                ·
                  refine ⟨399444930929813895580763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17042983719672059544779221 399444930929813895580763)
                  ·
                    rfl

theorem cell22_3500623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 7].length) (baseStart_3500623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500623 prefixEnd_3500623 := by exact prefixLift 3500623
  have htrace : WordTrace (prefixWord ++ tailWord_3500623) baseStart_3500623 baseEnd_3500623 := by
    simpa [prefixWord, tailWord_3500623, baseEnd_3500623] using wordTrace_append hprefix tailTrace_3500623
  have hstable : (prefixWord ++ tailWord_3500623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500623).length < 2 ^ (prefixWord ++ tailWord_3500623).sum := by decide
  have hdescent : baseEnd_3500623 < baseStart_3500623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500702 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3500702 : Nat := 118140960795 + 3500702 * 2 ^ 59
def prefixEnd_3500702 : Nat := 4983230072969 + 3 ^ 40 * 3500702 * 2
def baseEnd_3500702 : Nat := 399453945367970604672349

theorem tailTrace_3500702 : CollatzResearch.WordTrace tailWord_3500702 prefixEnd_3500702 399453945367970604672349 := by
  unfold tailWord_3500702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15960136420445250143458045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85120727575708000765109573 15960136420445250143458045)
  ·
    refine ⟨5985051157666968803796767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15960136420445250143458045 5985051157666968803796767)
    ·
      refine ⟨8977576736500453205695151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5985051157666968803796767 8977576736500453205695151)
      ·
        refine ⟨13466365104750679808542727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8977576736500453205695151 13466365104750679808542727)
        ·
          refine ⟨20199547657126019712814091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13466365104750679808542727 20199547657126019712814091)
          ·
            refine ⟨30299321485689029569221137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20199547657126019712814091 30299321485689029569221137)
            ·
              refine ⟨22724491114266772176915853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30299321485689029569221137 22724491114266772176915853)
              ·
                refine ⟨8521684167850039566343445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22724491114266772176915853 8521684167850039566343445)
                ·
                  refine ⟨399453945367970604672349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8521684167850039566343445 399453945367970604672349)
                  ·
                    rfl

theorem cell22_3500702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3500702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500702 prefixEnd_3500702 := by exact prefixLift 3500702
  have htrace : WordTrace (prefixWord ++ tailWord_3500702) baseStart_3500702 baseEnd_3500702 := by
    simpa [prefixWord, tailWord_3500702, baseEnd_3500702] using wordTrace_append hprefix tailTrace_3500702
  have hstable : (prefixWord ++ tailWord_3500702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500702).length < 2 ^ (prefixWord ++ tailWord_3500702).sum := by decide
  have hdescent : baseEnd_3500702 < baseStart_3500702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500717 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3500717 : Nat := 118140960795 + 3500717 * 2 ^ 59
def prefixEnd_3500717 : Nat := 4983230072969 + 3 ^ 40 * 3500717 * 2
def baseEnd_3500717 : Nat := 1198366970910456774892001

theorem tailTrace_3500717 : CollatzResearch.WordTrace tailWord_3500717 prefixEnd_3500717 1198366970910456774892001 := by
  unfold tailWord_3500717
  simp only [CollatzResearch.WordTrace]
  refine ⟨127681638458507658709460405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85121092305671772472973603 127681638458507658709460405)
  ·
    refine ⟨11970153605485093004011913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127681638458507658709460405 11970153605485093004011913)
    ·
      refine ⟨8977615204113819753008935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11970153605485093004011913 8977615204113819753008935)
      ·
        refine ⟨13466422806170729629513403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8977615204113819753008935 13466422806170729629513403)
        ·
          refine ⟨20199634209256094444270105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13466422806170729629513403 20199634209256094444270105)
          ·
            refine ⟨15149725656942070833202579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20199634209256094444270105 15149725656942070833202579)
            ·
              refine ⟨22724588485413106249803869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15149725656942070833202579 22724588485413106249803869)
              ·
                refine ⟨8521720682029914843676451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22724588485413106249803869 8521720682029914843676451)
                ·
                  refine ⟨12782581023044872265514677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8521720682029914843676451 12782581023044872265514677)
                  ·
                    refine ⟨1198366970910456774892001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12782581023044872265514677 1198366970910456774892001)
                    ·
                      rfl

theorem cell22_3500717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3500717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500717 prefixEnd_3500717 := by exact prefixLift 3500717
  have htrace : WordTrace (prefixWord ++ tailWord_3500717) baseStart_3500717 baseEnd_3500717 := by
    simpa [prefixWord, tailWord_3500717, baseEnd_3500717] using wordTrace_append hprefix tailTrace_3500717
  have hstable : (prefixWord ++ tailWord_3500717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500717).length < 2 ^ (prefixWord ++ tailWord_3500717).sum := by decide
  have hdescent : baseEnd_3500717 < baseStart_3500717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500796 : List Nat := [2, 2, 2, 1, 3, 2, 3, 3, 1, 3]
def baseStart_3500796 : Nat := 118140960795 + 3500796 * 2 ^ 59
def prefixEnd_3500796 : Nat := 4983230072969 + 3 ^ 40 * 3500796 * 2
def baseEnd_3500796 : Nat := 1198394014224926902166759

theorem tailTrace_3500796 : CollatzResearch.WordTrace tailWord_3500796 prefixEnd_3500796 1198394014224926902166759 := by
  unfold tailWord_3500796
  simp only [CollatzResearch.WordTrace]
  refine ⟨63842259912610727600793121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85123013216814303467724161 63842259912610727600793121)
  ·
    refine ⟨47881694934458045700594841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63842259912610727600793121 47881694934458045700594841)
    ·
      refine ⟨35911271200843534275446131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47881694934458045700594841 35911271200843534275446131)
      ·
        refine ⟨53866906801265301413169197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35911271200843534275446131 53866906801265301413169197)
        ·
          refine ⟨20200090050474488029938449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53866906801265301413169197 20200090050474488029938449)
          ·
            refine ⟨15150067537855866022453837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20200090050474488029938449 15150067537855866022453837)
            ·
              refine ⟨5681275326695949758420189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15150067537855866022453837 5681275326695949758420189)
              ·
                refine ⟨2130478247510981159407571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5681275326695949758420189 2130478247510981159407571)
                ·
                  refine ⟨3195717371266471739111357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130478247510981159407571 3195717371266471739111357)
                  ·
                    refine ⟨1198394014224926902166759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3195717371266471739111357 1198394014224926902166759)
                    ·
                      rfl

theorem cell22_3500796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_3500796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500796 prefixEnd_3500796 := by exact prefixLift 3500796
  have htrace : WordTrace (prefixWord ++ tailWord_3500796) baseStart_3500796 baseEnd_3500796 := by
    simpa [prefixWord, tailWord_3500796, baseEnd_3500796] using wordTrace_append hprefix tailTrace_3500796
  have hstable : (prefixWord ++ tailWord_3500796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500796).length < 2 ^ (prefixWord ++ tailWord_3500796).sum := by decide
  have hdescent : baseEnd_3500796 < baseStart_3500796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500867 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 2, 4]
def baseStart_3500867 : Nat := 118140960795 + 3500867 * 2 ^ 59
def prefixEnd_3500867 : Nat := 4983230072969 + 3 ^ 40 * 3500867 * 2
def baseEnd_3500867 : Nat := 1198418318975906383641541

theorem tailTrace_3500867 : CollatzResearch.WordTrace tailWord_3500867 prefixEnd_3500867 1198418318975906383641541 := by
  unfold tailWord_3500867
  simp only [CollatzResearch.WordTrace]
  refine ⟨127687109407964234327420855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85124739605309489551613903 127687109407964234327420855)
  ·
    refine ⟨191530664111946351491131283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127687109407964234327420855 191530664111946351491131283)
    ·
      refine ⟨287295996167919527236696925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191530664111946351491131283 287295996167919527236696925)
      ·
        refine ⟨107735998562969822713761347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287295996167919527236696925 107735998562969822713761347)
        ·
          refine ⟨161603997844454734070642021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107735998562969822713761347 161603997844454734070642021)
          ·
            refine ⟨30300749595835262638245379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161603997844454734070642021 30300749595835262638245379)
            ·
              refine ⟨45451124393752893957368069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30300749595835262638245379 45451124393752893957368069)
              ·
                refine ⟨8522085823828667617006513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45451124393752893957368069 8522085823828667617006513)
                ·
                  refine ⟨6391564367871500712754885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8522085823828667617006513 6391564367871500712754885)
                  ·
                    refine ⟨1198418318975906383641541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6391564367871500712754885 1198418318975906383641541)
                    ·
                      rfl

theorem cell22_3500867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 4].length) (baseStart_3500867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500867 prefixEnd_3500867 := by exact prefixLift 3500867
  have htrace : WordTrace (prefixWord ++ tailWord_3500867) baseStart_3500867 baseEnd_3500867 := by
    simpa [prefixWord, tailWord_3500867, baseEnd_3500867] using wordTrace_append hprefix tailTrace_3500867
  have hstable : (prefixWord ++ tailWord_3500867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500867).length < 2 ^ (prefixWord ++ tailWord_3500867).sum := by decide
  have hdescent : baseEnd_3500867 < baseStart_3500867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500899 : List Nat := [1, 1, 1, 5, 3, 2, 3, 6]
def baseStart_3500899 : Nat := 118140960795 + 3500899 * 2 ^ 59
def prefixEnd_3500899 : Nat := 4983230072969 + 3 ^ 40 * 3500899 * 2
def baseEnd_3500899 : Nat := 133158808136652107426827

theorem tailTrace_3500899 : CollatzResearch.WordTrace tailWord_3500899 prefixEnd_3500899 133158808136652107426827 := by
  unfold tailWord_3500899
  simp only [CollatzResearch.WordTrace]
  refine ⟨127688276543848303792585751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85125517695898869195057167 127688276543848303792585751)
  ·
    refine ⟨191532414815772455688878627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127688276543848303792585751 191532414815772455688878627)
    ·
      refine ⟨287298622223658683533317941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191532414815772455688878627 287298622223658683533317941)
      ·
        refine ⟨26934245833468001581248557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 287298622223658683533317941 26934245833468001581248557)
        ·
          refine ⟨10100342187550500592968209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26934245833468001581248557 10100342187550500592968209)
          ·
            refine ⟨7575256640662875444726157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10100342187550500592968209 7575256640662875444726157)
            ·
              refine ⟨2840721240248578291772309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7575256640662875444726157 2840721240248578291772309)
              ·
                refine ⟨133158808136652107426827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2840721240248578291772309 133158808136652107426827)
                ·
                  rfl

theorem cell22_3500899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 6].length) (baseStart_3500899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500899 prefixEnd_3500899 := by exact prefixLift 3500899
  have htrace : WordTrace (prefixWord ++ tailWord_3500899) baseStart_3500899 baseEnd_3500899 := by
    simpa [prefixWord, tailWord_3500899, baseEnd_3500899] using wordTrace_append hprefix tailTrace_3500899
  have hstable : (prefixWord ++ tailWord_3500899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500899).length < 2 ^ (prefixWord ++ tailWord_3500899).sum := by decide
  have hdescent : baseEnd_3500899 < baseStart_3500899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500931 : List Nat := [1, 1, 1, 3, 4, 1, 1, 6, 1, 3]
def baseStart_3500931 : Nat := 118140960795 + 3500931 * 2 ^ 59
def prefixEnd_3500931 : Nat := 4983230072969 + 3 ^ 40 * 3500931 * 2
def baseEnd_3500931 : Nat := 1198440227483831550041345

theorem tailTrace_3500931 : CollatzResearch.WordTrace tailWord_3500931 prefixEnd_3500931 1198440227483831550041345 := by
  unfold tailWord_3500931
  simp only [CollatzResearch.WordTrace]
  refine ⟨127689443679732373257750647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85126295786488248838500431 127689443679732373257750647)
  ·
    refine ⟨191534165519598559886625971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127689443679732373257750647 191534165519598559886625971)
    ·
      refine ⟨287301248279397839829938957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191534165519598559886625971 287301248279397839829938957)
      ·
        refine ⟨107737968104774189936227109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287301248279397839829938957 107737968104774189936227109)
        ·
          refine ⟨20200869019645160613042583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107737968104774189936227109 20200869019645160613042583)
          ·
            refine ⟨30301303529467740919563875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20200869019645160613042583 30301303529467740919563875)
            ·
              refine ⟨45451955294201611379345813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30301303529467740919563875 45451955294201611379345813)
              ·
                refine ⟨2130560404415700533406835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45451955294201611379345813 2130560404415700533406835)
                ·
                  refine ⟨3195840606623550800110253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130560404415700533406835 3195840606623550800110253)
                  ·
                    refine ⟨1198440227483831550041345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3195840606623550800110253 1198440227483831550041345)
                    ·
                      rfl

theorem cell22_3500931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 3].length) (baseStart_3500931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500931 prefixEnd_3500931 := by exact prefixLift 3500931
  have htrace : WordTrace (prefixWord ++ tailWord_3500931) baseStart_3500931 baseEnd_3500931 := by
    simpa [prefixWord, tailWord_3500931, baseEnd_3500931] using wordTrace_append hprefix tailTrace_3500931
  have hstable : (prefixWord ++ tailWord_3500931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500931).length < 2 ^ (prefixWord ++ tailWord_3500931).sum := by decide
  have hdescent : baseEnd_3500931 < baseStart_3500931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500950 : List Nat := [5, 3, 1, 1, 1, 3, 2, 6]
def baseStart_3500950 : Nat := 118140960795 + 3500950 * 2 ^ 59
def prefixEnd_3500950 : Nat := 4983230072969 + 3 ^ 40 * 3500950 * 2
def baseEnd_3500950 : Nat := 133160747952457981535143

theorem tailTrace_3500950 : CollatzResearch.WordTrace tailWord_3500950 prefixEnd_3500950 133160747952457981535143 := by
  unfold tailWord_3500950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7980633541666471218918269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85126757777775693001794869 7980633541666471218918269)
  ·
    refine ⟨2992737578124926707094351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7980633541666471218918269 2992737578124926707094351)
    ·
      refine ⟨4489106367187390060641527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2992737578124926707094351 4489106367187390060641527)
      ·
        refine ⟨6733659550781085090962291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489106367187390060641527 6733659550781085090962291)
        ·
          refine ⟨10100489326171627636443437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6733659550781085090962291 10100489326171627636443437)
          ·
            refine ⟨3787683497314360363666289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10100489326171627636443437 3787683497314360363666289)
            ·
              refine ⟨2840762622985770272749717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787683497314360363666289 2840762622985770272749717)
              ·
                refine ⟨133160747952457981535143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2840762622985770272749717 133160747952457981535143)
                ·
                  rfl

theorem cell22_3500950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_3500950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3500950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3500950 prefixEnd_3500950 := by exact prefixLift 3500950
  have htrace : WordTrace (prefixWord ++ tailWord_3500950) baseStart_3500950 baseEnd_3500950 := by
    simpa [prefixWord, tailWord_3500950, baseEnd_3500950] using wordTrace_append hprefix tailTrace_3500950
  have hstable : (prefixWord ++ tailWord_3500950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500950).length < 2 ^ (prefixWord ++ tailWord_3500950).sum := by decide
  have hdescent : baseEnd_3500950 < baseStart_3500950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501004 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_3501004 : Nat := 118140960795 + 3501004 * 2 ^ 59
def prefixEnd_3501004 : Nat := 4983230072969 + 3 ^ 40 * 3501004 * 2
def baseEnd_3501004 : Nat := 1198465216875683692966121

theorem tailTrace_3501004 : CollatzResearch.WordTrace tailWord_3501004 prefixEnd_3501004 1198465216875683692966121 := by
  unfold tailWord_3501004
  simp only [CollatzResearch.WordTrace]
  refine ⟨63846053104233953362579033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85128070805645271150105377 63846053104233953362579033)
  ·
    refine ⟨47884539828175465021934275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63846053104233953362579033 47884539828175465021934275)
    ·
      refine ⟨71826809742263197532901413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47884539828175465021934275 71826809742263197532901413)
      ·
        refine ⟨13467526826674349537419015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71826809742263197532901413 13467526826674349537419015)
        ·
          refine ⟨20201290240011524306128523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13467526826674349537419015 20201290240011524306128523)
          ·
            refine ⟨30301935360017286459192785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20201290240011524306128523 30301935360017286459192785)
            ·
              refine ⟨22726451520012964844394589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30301935360017286459192785 22726451520012964844394589)
              ·
                refine ⟨8522419320004861816647971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22726451520012964844394589 8522419320004861816647971)
                ·
                  refine ⟨12783628980007292724971957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8522419320004861816647971 12783628980007292724971957)
                  ·
                    refine ⟨1198465216875683692966121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12783628980007292724971957 1198465216875683692966121)
                    ·
                      rfl

theorem cell22_3501004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_3501004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501004 prefixEnd_3501004 := by exact prefixLift 3501004
  have htrace : WordTrace (prefixWord ++ tailWord_3501004) baseStart_3501004 baseEnd_3501004 := by
    simpa [prefixWord, tailWord_3501004, baseEnd_3501004] using wordTrace_append hprefix tailTrace_3501004
  have hstable : (prefixWord ++ tailWord_3501004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501004).length < 2 ^ (prefixWord ++ tailWord_3501004).sum := by decide
  have hdescent : baseEnd_3501004 < baseStart_3501004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501021 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3501021 : Nat := 118140960795 + 3501021 * 2 ^ 59
def prefixEnd_3501021 : Nat := 4983230072969 + 3 ^ 40 * 3501021 * 2
def baseEnd_3501021 : Nat := 1198471036323101315291069

theorem tailTrace_3501021 : CollatzResearch.WordTrace tailWord_3501021 prefixEnd_3501021 1198471036323101315291069 := by
  unfold tailWord_3501021
  simp only [CollatzResearch.WordTrace]
  refine ⟨127692726249406318628526917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85128484166270879085684611 127692726249406318628526917)
  ·
    refine ⟨23942386171763684742848797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127692726249406318628526917 23942386171763684742848797)
    ·
      refine ⟨8978394814411381778568299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23942386171763684742848797 8978394814411381778568299)
      ·
        refine ⟨13467592221617072667852449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8978394814411381778568299 13467592221617072667852449)
        ·
          refine ⟨10100694166212804500889337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13467592221617072667852449 10100694166212804500889337)
          ·
            refine ⟨7575520624659603375667003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10100694166212804500889337 7575520624659603375667003)
            ·
              refine ⟨11363280936989405063500505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575520624659603375667003 11363280936989405063500505)
              ·
                refine ⟨8522460702742053797625379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11363280936989405063500505 8522460702742053797625379)
                ·
                  refine ⟨12783691054113080696438069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8522460702742053797625379 12783691054113080696438069)
                  ·
                    refine ⟨1198471036323101315291069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12783691054113080696438069 1198471036323101315291069)
                    ·
                      rfl

theorem cell22_3501021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3501021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501021 prefixEnd_3501021 := by exact prefixLift 3501021
  have htrace : WordTrace (prefixWord ++ tailWord_3501021) baseStart_3501021 baseEnd_3501021 := by
    simpa [prefixWord, tailWord_3501021, baseEnd_3501021] using wordTrace_append hprefix tailTrace_3501021
  have hstable : (prefixWord ++ tailWord_3501021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501021).length < 2 ^ (prefixWord ++ tailWord_3501021).sum := by decide
  have hdescent : baseEnd_3501021 < baseStart_3501021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501066 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_3501066 : Nat := 118140960795 + 3501066 * 2 ^ 59
def prefixEnd_3501066 : Nat := 4983230072969 + 3 ^ 40 * 3501066 * 2
def baseEnd_3501066 : Nat := 1198486440742736197915931

theorem tailTrace_3501066 : CollatzResearch.WordTrace tailWord_3501066 prefixEnd_3501066 1198486440742736197915931 := by
  unfold tailWord_3501066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31923591883560822828478763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85129578356162194209276701 31923591883560822828478763)
  ·
    refine ⟨47885387825341234242718145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31923591883560822828478763 47885387825341234242718145)
    ·
      refine ⟨35914040869005925682038609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47885387825341234242718145 35914040869005925682038609)
      ·
        refine ⟨26935530651754444261528957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35914040869005925682038609 26935530651754444261528957)
        ·
          refine ⟨10100823994407916598073359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26935530651754444261528957 10100823994407916598073359)
          ·
            refine ⟨15151235991611874897110039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10100823994407916598073359 15151235991611874897110039)
            ·
              refine ⟨22726853987417812345665059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15151235991611874897110039 22726853987417812345665059)
              ·
                refine ⟨34090280981126718518497589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22726853987417812345665059 34090280981126718518497589)
                ·
                  refine ⟨3195963841980629861109149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34090280981126718518497589 3195963841980629861109149)
                  ·
                    refine ⟨1198486440742736197915931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3195963841980629861109149 1198486440742736197915931)
                    ·
                      rfl

theorem cell22_3501066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_3501066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501066 prefixEnd_3501066 := by exact prefixLift 3501066
  have htrace : WordTrace (prefixWord ++ tailWord_3501066) baseStart_3501066 baseEnd_3501066 := by
    simpa [prefixWord, tailWord_3501066, baseEnd_3501066] using wordTrace_append hprefix tailTrace_3501066
  have hstable : (prefixWord ++ tailWord_3501066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501066).length < 2 ^ (prefixWord ++ tailWord_3501066).sum := by decide
  have hdescent : baseEnd_3501066 < baseStart_3501066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501113 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 5]
def baseStart_3501113 : Nat := 118140960795 + 3501113 * 2 ^ 59
def prefixEnd_3501113 : Nat := 4983230072969 + 3 ^ 40 * 3501113 * 2
def baseEnd_3501113 : Nat := 399500843267747913996929

theorem tailTrace_3501113 : CollatzResearch.WordTrace tailWord_3501113 prefixEnd_3501113 399500843267747913996929 := by
  unfold tailWord_3501113
  simp only [CollatzResearch.WordTrace]
  refine ⟨127696081765073018340875993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85130721176715345560583995 127696081765073018340875993)
  ·
    refine ⟨95772061323804763755656995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127696081765073018340875993 95772061323804763755656995)
    ·
      refine ⟨143658091985707145633485493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95772061323804763755656995 143658091985707145633485493)
      ·
        refine ⟨13467946123660044903139265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143658091985707145633485493 13467946123660044903139265)
        ·
          refine ⟨10100959592745033677354449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13467946123660044903139265 10100959592745033677354449)
          ·
            refine ⟨7575719694558775258015837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10100959592745033677354449 7575719694558775258015837)
            ·
              refine ⟨2840894885459540721755939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7575719694558775258015837 2840894885459540721755939)
              ·
                refine ⟨4261342328189311082633909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840894885459540721755939 4261342328189311082633909)
                ·
                  refine ⟨399500843267747913996929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4261342328189311082633909 399500843267747913996929)
                  ·
                    rfl

theorem cell22_3501113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 5].length) (baseStart_3501113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501113 prefixEnd_3501113 := by exact prefixLift 3501113
  have htrace : WordTrace (prefixWord ++ tailWord_3501113) baseStart_3501113 baseEnd_3501113 := by
    simpa [prefixWord, tailWord_3501113, baseEnd_3501113] using wordTrace_append hprefix tailTrace_3501113
  have hstable : (prefixWord ++ tailWord_3501113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501113).length < 2 ^ (prefixWord ++ tailWord_3501113).sum := by decide
  have hdescent : baseEnd_3501113 < baseStart_3501113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501184 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_3501184 : Nat := 118140960795 + 3501184 * 2 ^ 59
def prefixEnd_3501184 : Nat := 4983230072969 + 3 ^ 40 * 3501184 * 2
def baseEnd_3501184 : Nat := 1198526834554223223465569

theorem tailTrace_3501184 : CollatzResearch.WordTrace tailWord_3501184 prefixEnd_3501184 1198526834554223223465569 := by
  unfold tailWord_3501184
  simp only [CollatzResearch.WordTrace]
  refine ⟨63849335673907898733355303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85132447565210531644473737 63849335673907898733355303)
  ·
    refine ⟨95774003510861848100032955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63849335673907898733355303 95774003510861848100032955)
    ·
      refine ⟨143661005266292772150049433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95774003510861848100032955 143661005266292772150049433)
      ·
        refine ⟨107745753949719579112537075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143661005266292772150049433 107745753949719579112537075)
        ·
          refine ⟨161618630924579368668805613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107745753949719579112537075 161618630924579368668805613)
          ·
            refine ⟨60606986596717263250802105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161618630924579368668805613 60606986596717263250802105)
            ·
              refine ⟨45455239947537947438101579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60606986596717263250802105 45455239947537947438101579)
              ·
                refine ⟨68182859921306921157152369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45455239947537947438101579 68182859921306921157152369)
                ·
                  refine ⟨51137144940980190867864277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68182859921306921157152369 51137144940980190867864277)
                  ·
                    refine ⟨1198526834554223223465569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51137144940980190867864277 1198526834554223223465569)
                    ·
                      rfl

theorem cell22_3501184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_3501184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501184 prefixEnd_3501184 := by exact prefixLift 3501184
  have htrace : WordTrace (prefixWord ++ tailWord_3501184) baseStart_3501184 baseEnd_3501184 := by
    simpa [prefixWord, tailWord_3501184, baseEnd_3501184] using wordTrace_append hprefix tailTrace_3501184
  have hstable : (prefixWord ++ tailWord_3501184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501184).length < 2 ^ (prefixWord ++ tailWord_3501184).sum := by decide
  have hdescent : baseEnd_3501184 < baseStart_3501184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501188 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_3501188 : Nat := 118140960795 + 3501188 * 2 ^ 59
def prefixEnd_3501188 : Nat := 4983230072969 + 3 ^ 40 * 3501188 * 2
def baseEnd_3501188 : Nat := 1198528203835968546365557

theorem tailTrace_3501188 : CollatzResearch.WordTrace tailWord_3501188 prefixEnd_3501188 1198528203835968546365557 := by
  unfold tailWord_3501188
  simp only [CollatzResearch.WordTrace]
  refine ⟨63849408619900653074928109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85132544826534204099904145 63849408619900653074928109)
  ·
    refine ⟨23943528232462744903098041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63849408619900653074928109 23943528232462744903098041)
    ·
      refine ⟨17957646174347058677323531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23943528232462744903098041 17957646174347058677323531)
      ·
        refine ⟨26936469261520588015985297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17957646174347058677323531 26936469261520588015985297)
        ·
          refine ⟨20202351946140441011988973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26936469261520588015985297 20202351946140441011988973)
          ·
            refine ⟨7575881979802665379495865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20202351946140441011988973 7575881979802665379495865)
            ·
              refine ⟨5681911484851999034621899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7575881979802665379495865 5681911484851999034621899)
              ·
                refine ⟨8522867227277998551932849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681911484851999034621899 8522867227277998551932849)
                ·
                  refine ⟨6392150420458498913949637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8522867227277998551932849 6392150420458498913949637)
                  ·
                    refine ⟨1198528203835968546365557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6392150420458498913949637 1198528203835968546365557)
                    ·
                      rfl

theorem cell22_3501188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_3501188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501188 prefixEnd_3501188 := by exact prefixLift 3501188
  have htrace : WordTrace (prefixWord ++ tailWord_3501188) baseStart_3501188 baseEnd_3501188 := by
    simpa [prefixWord, tailWord_3501188, baseEnd_3501188] using wordTrace_append hprefix tailTrace_3501188
  have hstable : (prefixWord ++ tailWord_3501188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501188).length < 2 ^ (prefixWord ++ tailWord_3501188).sum := by decide
  have hdescent : baseEnd_3501188 < baseStart_3501188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501231 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 5]
def baseStart_3501231 : Nat := 118140960795 + 3501231 * 2 ^ 59
def prefixEnd_3501231 : Nat := 4983230072969 + 3 ^ 40 * 3501231 * 2
def baseEnd_3501231 : Nat := 399514307871576922513475

theorem tailTrace_3501231 : CollatzResearch.WordTrace tailWord_3501231 prefixEnd_3501231 399514307871576922513475 := by
  unfold tailWord_3501231
  simp only [CollatzResearch.WordTrace]
  refine ⟨127700385578645524493671547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85133590385763682995781031 127700385578645524493671547)
  ·
    refine ⟨191550578367968286740507321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127700385578645524493671547 191550578367968286740507321)
    ·
      refine ⟨143662933775976215055380491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191550578367968286740507321 143662933775976215055380491)
      ·
        refine ⟨215494400663964322583070737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143662933775976215055380491 215494400663964322583070737)
        ·
          refine ⟨161620800497973241937303053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215494400663964322583070737 161620800497973241937303053)
          ·
            refine ⟨60607800186739965726488645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161620800497973241937303053 60607800186739965726488645)
            ·
              refine ⟨11363962535013743573716621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60607800186739965726488645 11363962535013743573716621)
              ·
                refine ⟨4261485950630153840143733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11363962535013743573716621 4261485950630153840143733)
                ·
                  refine ⟨399514307871576922513475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4261485950630153840143733 399514307871576922513475)
                  ·
                    rfl

theorem cell22_3501231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 5].length) (baseStart_3501231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501231 prefixEnd_3501231 := by exact prefixLift 3501231
  have htrace : WordTrace (prefixWord ++ tailWord_3501231) baseStart_3501231 baseEnd_3501231 := by
    simpa [prefixWord, tailWord_3501231, baseEnd_3501231] using wordTrace_append hprefix tailTrace_3501231
  have hstable : (prefixWord ++ tailWord_3501231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501231).length < 2 ^ (prefixWord ++ tailWord_3501231).sum := by decide
  have hdescent : baseEnd_3501231 < baseStart_3501231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501293 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 6]
def baseStart_3501293 : Nat := 118140960795 + 3501293 * 2 ^ 59
def prefixEnd_3501293 : Nat := 4983230072969 + 3 ^ 40 * 3501293 * 2
def baseEnd_3501293 : Nat := 399521382493927757496745

theorem tailTrace_3501293 : CollatzResearch.WordTrace tailWord_3501293 prefixEnd_3501293 399521382493927757496745 := by
  unfold tailWord_3501293
  simp only [CollatzResearch.WordTrace]
  refine ⟨127702646904420909082428533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85135097936280606054952355 127702646904420909082428533)
  ·
    refine ⟨11972123147289460226477675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127702646904420909082428533 11972123147289460226477675)
    ·
      refine ⟨17958184720934190339716513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11972123147289460226477675 17958184720934190339716513)
      ·
        refine ⟨13468638540700642754787385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17958184720934190339716513 13468638540700642754787385)
        ·
          refine ⟨10101478905525482066090539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13468638540700642754787385 10101478905525482066090539)
          ·
            refine ⟨15152218358288223099135809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10101478905525482066090539 15152218358288223099135809)
            ·
              refine ⟨11364163768716167324351857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15152218358288223099135809 11364163768716167324351857)
              ·
                refine ⟨8523122826537125493263893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11364163768716167324351857 8523122826537125493263893)
                ·
                  refine ⟨399521382493927757496745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8523122826537125493263893 399521382493927757496745)
                  ·
                    rfl

theorem cell22_3501293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_3501293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501293 prefixEnd_3501293 := by exact prefixLift 3501293
  have htrace : WordTrace (prefixWord ++ tailWord_3501293) baseStart_3501293 baseEnd_3501293 := by
    simpa [prefixWord, tailWord_3501293, baseEnd_3501293] using wordTrace_append hprefix tailTrace_3501293
  have hstable : (prefixWord ++ tailWord_3501293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501293).length < 2 ^ (prefixWord ++ tailWord_3501293).sum := by decide
  have hdescent : baseEnd_3501293 < baseStart_3501293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501295 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 1, 4]
def baseStart_3501295 : Nat := 118140960795 + 3501295 * 2 ^ 59
def prefixEnd_3501295 : Nat := 4983230072969 + 3 ^ 40 * 3501295 * 2
def baseEnd_3501295 : Nat := 1198564832122655933940229

theorem tailTrace_3501295 : CollatzResearch.WordTrace tailWord_3501295 prefixEnd_3501295 1198564832122655933940229 := by
  unfold tailWord_3501295
  simp only [CollatzResearch.WordTrace]
  refine ⟨127702719850413663424001339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85135146566942442282667559 127702719850413663424001339)
  ·
    refine ⟨191554079775620495136002009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127702719850413663424001339 191554079775620495136002009)
    ·
      refine ⟨143665559831715371352001507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191554079775620495136002009 143665559831715371352001507)
      ·
        refine ⟨215498339747573057028002261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143665559831715371352001507 215498339747573057028002261)
        ·
          refine ⟨5050742337833743524093803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 215498339747573057028002261 5050742337833743524093803)
          ·
            refine ⟨7576113506750615286140705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050742337833743524093803 7576113506750615286140705)
            ·
              refine ⟨5682085130062961464605529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7576113506750615286140705 5682085130062961464605529)
              ·
                refine ⟨4261563847547221098454147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5682085130062961464605529 4261563847547221098454147)
                ·
                  refine ⟨6392345771320831647681221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261563847547221098454147 6392345771320831647681221)
                  ·
                    refine ⟨1198564832122655933940229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6392345771320831647681221 1198564832122655933940229)
                    ·
                      rfl

theorem cell22_3501295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_3501295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501295 prefixEnd_3501295 := by exact prefixLift 3501295
  have htrace : WordTrace (prefixWord ++ tailWord_3501295) baseStart_3501295 baseEnd_3501295 := by
    simpa [prefixWord, tailWord_3501295, baseEnd_3501295] using wordTrace_append hprefix tailTrace_3501295
  have hstable : (prefixWord ++ tailWord_3501295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501295).length < 2 ^ (prefixWord ++ tailWord_3501295).sum := by decide
  have hdescent : baseEnd_3501295 < baseStart_3501295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501306 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_3501306 : Nat := 118140960795 + 3501306 * 2 ^ 59
def prefixEnd_3501306 : Nat := 4983230072969 + 3 ^ 40 * 3501306 * 2
def baseEnd_3501306 : Nat := 1198568597647455571915195

theorem tailTrace_3501306 : CollatzResearch.WordTrace tailWord_3501306 prefixEnd_3501306 1198568597647455571915195 := by
  unfold tailWord_3501306
  simp only [CollatzResearch.WordTrace]
  refine ⟨31925780263343453075662943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85135414035582541535101181 31925780263343453075662943)
  ·
    refine ⟨47888670395015179613494415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31925780263343453075662943 47888670395015179613494415)
    ·
      refine ⟨71833005592522769420241623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47888670395015179613494415 71833005592522769420241623)
      ·
        refine ⟨107749508388784154130362435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71833005592522769420241623 107749508388784154130362435)
        ·
          refine ⟨161624262583176231195543653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107749508388784154130362435 161624262583176231195543653)
          ·
            refine ⟨30304549234345543349164435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161624262583176231195543653 30304549234345543349164435)
            ·
              refine ⟨45456823851518315023746653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30304549234345543349164435 45456823851518315023746653)
              ·
                refine ⟨17046308944319368133904995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45456823851518315023746653 17046308944319368133904995)
                ·
                  refine ⟨25569463416479052200857493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17046308944319368133904995 25569463416479052200857493)
                  ·
                    refine ⟨1198568597647455571915195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25569463416479052200857493 1198568597647455571915195)
                    ·
                      rfl

theorem cell22_3501306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_3501306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501306 prefixEnd_3501306 := by exact prefixLift 3501306
  have htrace : WordTrace (prefixWord ++ tailWord_3501306) baseStart_3501306 baseEnd_3501306 := by
    simpa [prefixWord, tailWord_3501306, baseEnd_3501306] using wordTrace_append hprefix tailTrace_3501306
  have hstable : (prefixWord ++ tailWord_3501306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501306).length < 2 ^ (prefixWord ++ tailWord_3501306).sum := by decide
  have hdescent : baseEnd_3501306 < baseStart_3501306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501323 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 2, 4]
def baseStart_3501323 : Nat := 118140960795 + 3501323 * 2 ^ 59
def prefixEnd_3501323 : Nat := 4983230072969 + 3 ^ 40 * 3501323 * 2
def baseEnd_3501323 : Nat := 1198574417094873194240143

theorem tailTrace_3501323 : CollatzResearch.WordTrace tailWord_3501323 prefixEnd_3501323 1198574417094873194240143 := by
  unfold tailWord_3501323
  simp only [CollatzResearch.WordTrace]
  refine ⟨127703741094312224206020623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85135827396208149470680415 127703741094312224206020623)
  ·
    refine ⟨191555611641468336309030935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127703741094312224206020623 191555611641468336309030935)
    ·
      refine ⟨287333417462202504463546403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191555611641468336309030935 287333417462202504463546403)
      ·
        refine ⟨431000126193303756695319605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287333417462202504463546403 431000126193303756695319605)
        ·
          refine ⟨40406261830622227190186213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 431000126193303756695319605 40406261830622227190186213)
          ·
            refine ⟨7576174093241667598159915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40406261830622227190186213 7576174093241667598159915)
            ·
              refine ⟨11364261139862501397239873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7576174093241667598159915 11364261139862501397239873)
              ·
                refine ⟨8523195854896876047929905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11364261139862501397239873 8523195854896876047929905)
                ·
                  refine ⟨6392396891172657035947429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8523195854896876047929905 6392396891172657035947429)
                  ·
                    refine ⟨1198574417094873194240143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6392396891172657035947429 1198574417094873194240143)
                    ·
                      rfl

theorem cell22_3501323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 4].length) (baseStart_3501323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501323 prefixEnd_3501323 := by exact prefixLift 3501323
  have htrace : WordTrace (prefixWord ++ tailWord_3501323) baseStart_3501323 baseEnd_3501323 := by
    simpa [prefixWord, tailWord_3501323, baseEnd_3501323] using wordTrace_append hprefix tailTrace_3501323
  have hstable : (prefixWord ++ tailWord_3501323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501323).length < 2 ^ (prefixWord ++ tailWord_3501323).sum := by decide
  have hdescent : baseEnd_3501323 < baseStart_3501323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501338 : List Nat := [3, 1, 1, 3, 3, 2, 2, 7]
def baseStart_3501338 : Nat := 118140960795 + 3501338 * 2 ^ 59
def prefixEnd_3501338 : Nat := 4983230072969 + 3 ^ 40 * 3501338 * 2
def baseEnd_3501338 : Nat := 133175505766824239457233

theorem tailTrace_3501338 : CollatzResearch.WordTrace tailWord_3501338 prefixEnd_3501338 133175505766824239457233 := by
  unfold tailWord_3501338
  simp only [CollatzResearch.WordTrace]
  refine ⟨31926072047314470441954167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85136192126171921178544445 31926072047314470441954167)
  ·
    refine ⟨47889108070971705662931251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31926072047314470441954167 47889108070971705662931251)
    ·
      refine ⟨71833662106457558494396877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47889108070971705662931251 71833662106457558494396877)
      ·
        refine ⟨26937623289921584435398829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71833662106457558494396877 26937623289921584435398829)
        ·
          refine ⟨10101608733720594163274561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26937623289921584435398829 10101608733720594163274561)
          ·
            refine ⟨7576206550290445622455921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10101608733720594163274561 7576206550290445622455921)
            ·
              refine ⟨5682154912717834216841941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7576206550290445622455921 5682154912717834216841941)
              ·
                refine ⟨133175505766824239457233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5682154912717834216841941 133175505766824239457233)
                ·
                  rfl

theorem cell22_3501338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_3501338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501338 prefixEnd_3501338 := by exact prefixLift 3501338
  have htrace : WordTrace (prefixWord ++ tailWord_3501338) baseStart_3501338 baseEnd_3501338 := by
    simpa [prefixWord, tailWord_3501338, baseEnd_3501338] using wordTrace_append hprefix tailTrace_3501338
  have hstable : (prefixWord ++ tailWord_3501338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501338).length < 2 ^ (prefixWord ++ tailWord_3501338).sum := by decide
  have hdescent : baseEnd_3501338 < baseStart_3501338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501357 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3501357 : Nat := 118140960795 + 3501357 * 2 ^ 59
def prefixEnd_3501357 : Nat := 4983230072969 + 3 ^ 40 * 3501357 * 2
def baseEnd_3501357 : Nat := 1198586055989708438890039

theorem tailTrace_3501357 : CollatzResearch.WordTrace tailWord_3501357 prefixEnd_3501357 1198586055989708438890039 := by
  unfold tailWord_3501357
  simp only [CollatzResearch.WordTrace]
  refine ⟨127704981176189048012758325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85136654117459365341838883 127704981176189048012758325)
  ·
    refine ⟨11972341985267723251196093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127704981176189048012758325 11972341985267723251196093)
    ·
      refine ⟨4489628244475396219198535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11972341985267723251196093 4489628244475396219198535)
      ·
        refine ⟨6734442366713094328797803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489628244475396219198535 6734442366713094328797803)
        ·
          refine ⟨10101663550069641493196705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734442366713094328797803 10101663550069641493196705)
          ·
            refine ⟨7576247662552231119897529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10101663550069641493196705 7576247662552231119897529)
            ·
              refine ⟨5682185746914173339923147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7576247662552231119897529 5682185746914173339923147)
              ·
                refine ⟨8523278620371260009884721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682185746914173339923147 8523278620371260009884721)
                ·
                  refine ⟨6392458965278445007413541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8523278620371260009884721 6392458965278445007413541)
                  ·
                    refine ⟨1198586055989708438890039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6392458965278445007413541 1198586055989708438890039)
                    ·
                      rfl

theorem cell22_3501357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3501357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501357 prefixEnd_3501357 := by exact prefixLift 3501357
  have htrace : WordTrace (prefixWord ++ tailWord_3501357) baseStart_3501357 baseEnd_3501357 := by
    simpa [prefixWord, tailWord_3501357, baseEnd_3501357] using wordTrace_append hprefix tailTrace_3501357
  have hstable : (prefixWord ++ tailWord_3501357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501357).length < 2 ^ (prefixWord ++ tailWord_3501357).sum := by decide
  have hdescent : baseEnd_3501357 < baseStart_3501357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501381 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_3501381 : Nat := 118140960795 + 3501381 * 2 ^ 59
def prefixEnd_3501381 : Nat := 4983230072969 + 3 ^ 40 * 3501381 * 2
def baseEnd_3501381 : Nat := 1198594271680180376289965

theorem tailTrace_3501381 : CollatzResearch.WordTrace tailWord_3501381 prefixEnd_3501381 1198594271680180376289965 := by
  unfold tailWord_3501381
  simp only [CollatzResearch.WordTrace]
  refine ⟨127705856528102100111631997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85137237685401400074421331 127705856528102100111631997)
  ·
    refine ⟨47889696198038287541861999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127705856528102100111631997 47889696198038287541861999)
    ·
      refine ⟨71834544297057431312792999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47889696198038287541861999 71834544297057431312792999)
      ·
        refine ⟨107751816445586146969189499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71834544297057431312792999 107751816445586146969189499)
        ·
          refine ⟨161627724668379220453784249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107751816445586146969189499 161627724668379220453784249)
          ·
            refine ⟨121220793501284415340338187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161627724668379220453784249 121220793501284415340338187)
            ·
              refine ⟨181831190251926623010507281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121220793501284415340338187 181831190251926623010507281)
              ·
                refine ⟨136373392688944967257880461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181831190251926623010507281 136373392688944967257880461)
                ·
                  refine ⟨51140022258354362721705173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136373392688944967257880461 51140022258354362721705173)
                  ·
                    refine ⟨1198594271680180376289965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51140022258354362721705173 1198594271680180376289965)
                    ·
                      rfl

theorem cell22_3501381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_3501381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501381 prefixEnd_3501381 := by exact prefixLift 3501381
  have htrace : WordTrace (prefixWord ++ tailWord_3501381) baseStart_3501381 baseEnd_3501381 := by
    simpa [prefixWord, tailWord_3501381, baseEnd_3501381] using wordTrace_append hprefix tailTrace_3501381
  have hstable : (prefixWord ++ tailWord_3501381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501381).length < 2 ^ (prefixWord ++ tailWord_3501381).sum := by decide
  have hdescent : baseEnd_3501381 < baseStart_3501381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501383 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 5]
def baseStart_3501383 : Nat := 118140960795 + 3501383 * 2 ^ 59
def prefixEnd_3501383 : Nat := 4983230072969 + 3 ^ 40 * 3501383 * 2
def baseEnd_3501383 : Nat := 399531652107017679246653

theorem tailTrace_3501383 : CollatzResearch.WordTrace tailWord_3501383 prefixEnd_3501383 399531652107017679246653 := by
  unfold tailWord_3501383
  simp only [CollatzResearch.WordTrace]
  refine ⟨127705929474094854453204803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85137286316063236302136535 127705929474094854453204803)
  ·
    refine ⟨191558894211142281679807205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127705929474094854453204803 191558894211142281679807205)
    ·
      refine ⟨35917292664589177814963851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191558894211142281679807205 35917292664589177814963851)
      ·
        refine ⟨53875938996883766722445777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35917292664589177814963851 53875938996883766722445777)
        ·
          refine ⟨40406954247662825041834333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53875938996883766722445777 40406954247662825041834333)
          ·
            refine ⟨15152607842873559390687875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40406954247662825041834333 15152607842873559390687875)
            ·
              refine ⟨22728911764310339086031813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15152607842873559390687875 22728911764310339086031813)
              ·
                refine ⟨4261670955808188578630965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22728911764310339086031813 4261670955808188578630965)
                ·
                  refine ⟨399531652107017679246653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4261670955808188578630965 399531652107017679246653)
                  ·
                    rfl

theorem cell22_3501383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 5].length) (baseStart_3501383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501383 prefixEnd_3501383 := by exact prefixLift 3501383
  have htrace : WordTrace (prefixWord ++ tailWord_3501383) baseStart_3501383 baseEnd_3501383 := by
    simpa [prefixWord, tailWord_3501383, baseEnd_3501383] using wordTrace_append hprefix tailTrace_3501383
  have hstable : (prefixWord ++ tailWord_3501383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501383).length < 2 ^ (prefixWord ++ tailWord_3501383).sum := by decide
  have hdescent : baseEnd_3501383 < baseStart_3501383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501389 : List Nat := [1, 6, 1, 3, 2, 1, 1, 7]
def baseStart_3501389 : Nat := 118140960795 + 3501389 * 2 ^ 59
def prefixEnd_3501389 : Nat := 4983230072969 + 3 ^ 40 * 3501389 * 2
def baseEnd_3501389 : Nat := 133177445582630113565549

theorem tailTrace_3501389 : CollatzResearch.WordTrace tailWord_3501389 prefixEnd_3501389 133177445582630113565549 := by
  unfold tailWord_3501389
  simp only [CollatzResearch.WordTrace]
  refine ⟨127706148312073117477923221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85137432208048744985282147 127706148312073117477923221)
  ·
    refine ⟨5986225702128427381777651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127706148312073117477923221 5986225702128427381777651)
    ·
      refine ⟨8979338553192641072666477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5986225702128427381777651 8979338553192641072666477)
      ·
        refine ⟨3367251957447240402249929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8979338553192641072666477 3367251957447240402249929)
        ·
          refine ⟨2525438968085430301687447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3367251957447240402249929 2525438968085430301687447)
          ·
            refine ⟨3788158452128145452531171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525438968085430301687447 3788158452128145452531171)
            ·
              refine ⟨5682237678192218178796757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788158452128145452531171 5682237678192218178796757)
              ·
                refine ⟨133177445582630113565549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5682237678192218178796757 133177445582630113565549)
                ·
                  rfl

theorem cell22_3501389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 7].length) (baseStart_3501389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501389 prefixEnd_3501389 := by exact prefixLift 3501389
  have htrace : WordTrace (prefixWord ++ tailWord_3501389) baseStart_3501389 baseEnd_3501389 := by
    simpa [prefixWord, tailWord_3501389, baseEnd_3501389] using wordTrace_append hprefix tailTrace_3501389
  have hstable : (prefixWord ++ tailWord_3501389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501389).length < 2 ^ (prefixWord ++ tailWord_3501389).sum := by decide
  have hdescent : baseEnd_3501389 < baseStart_3501389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501413 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_3501413 : Nat := 118140960795 + 3501413 * 2 ^ 59
def prefixEnd_3501413 : Nat := 4983230072969 + 3 ^ 40 * 3501413 * 2
def baseEnd_3501413 : Nat := 1198605225934142959489867

theorem tailTrace_3501413 : CollatzResearch.WordTrace tailWord_3501413 prefixEnd_3501413 1198605225934142959489867 := by
  unfold tailWord_3501413
  simp only [CollatzResearch.WordTrace]
  refine ⟨127707023663986169576796893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85138015775990779717864595 127707023663986169576796893)
  ·
    refine ⟨47890133873994813591298835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127707023663986169576796893 47890133873994813591298835)
    ·
      refine ⟨71835200810992220386948253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47890133873994813591298835 71835200810992220386948253)
      ·
        refine ⟨26938200304122082645105595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71835200810992220386948253 26938200304122082645105595)
        ·
          refine ⟨40407300456183123967658393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26938200304122082645105595 40407300456183123967658393)
          ·
            refine ⟨30305475342137342975743795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40407300456183123967658393 30305475342137342975743795)
            ·
              refine ⟨45458213013206014463615693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30305475342137342975743795 45458213013206014463615693)
              ·
                refine ⟨17046829879952255423855885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45458213013206014463615693 17046829879952255423855885)
                ·
                  refine ⟨6392561204982095783945957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17046829879952255423855885 6392561204982095783945957)
                  ·
                    refine ⟨1198605225934142959489867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6392561204982095783945957 1198605225934142959489867)
                    ·
                      rfl

theorem cell22_3501413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_3501413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501413 prefixEnd_3501413 := by exact prefixLift 3501413
  have htrace : WordTrace (prefixWord ++ tailWord_3501413) baseStart_3501413 baseEnd_3501413 := by
    simpa [prefixWord, tailWord_3501413, baseEnd_3501413] using wordTrace_append hprefix tailTrace_3501413
  have hstable : (prefixWord ++ tailWord_3501413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501413).length < 2 ^ (prefixWord ++ tailWord_3501413).sum := by decide
  have hdescent : baseEnd_3501413 < baseStart_3501413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501445 : List Nat := [1, 3, 1, 1, 3, 1, 4, 4, 4]
def baseStart_3501445 : Nat := 118140960795 + 3501445 * 2 ^ 59
def prefixEnd_3501445 : Nat := 4983230072969 + 3 ^ 40 * 3501445 * 2
def baseEnd_3501445 : Nat := 399538726729368514229923

theorem tailTrace_3501445 : CollatzResearch.WordTrace tailWord_3501445 prefixEnd_3501445 399538726729368514229923 := by
  unfold tailWord_3501445
  simp only [CollatzResearch.WordTrace]
  refine ⟨127708190799870239041961789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85138793866580159361307859 127708190799870239041961789)
  ·
    refine ⟨47890571549951339640735671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127708190799870239041961789 47890571549951339640735671)
    ·
      refine ⟨71835857324927009461103507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47890571549951339640735671 71835857324927009461103507)
      ·
        refine ⟨107753785987390514191655261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71835857324927009461103507 107753785987390514191655261)
        ·
          refine ⟨40407669745271442821870723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107753785987390514191655261 40407669745271442821870723)
          ·
            refine ⟨60611504617907164232806085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40407669745271442821870723 60611504617907164232806085)
            ·
              refine ⟨11364657115857593293651141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60611504617907164232806085 11364657115857593293651141)
              ·
                refine ⟨2130873209223298742559589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11364657115857593293651141 2130873209223298742559589)
                ·
                  refine ⟨399538726729368514229923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130873209223298742559589 399538726729368514229923)
                  ·
                    rfl

theorem cell22_3501445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_3501445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501445 prefixEnd_3501445 := by exact prefixLift 3501445
  have htrace : WordTrace (prefixWord ++ tailWord_3501445) baseStart_3501445 baseEnd_3501445 := by
    simpa [prefixWord, tailWord_3501445, baseEnd_3501445] using wordTrace_append hprefix tailTrace_3501445
  have hstable : (prefixWord ++ tailWord_3501445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501445).length < 2 ^ (prefixWord ++ tailWord_3501445).sum := by decide
  have hdescent : baseEnd_3501445 < baseStart_3501445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501550 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3501550 : Nat := 118140960795 + 3501550 * 2 ^ 59
def prefixEnd_3501550 : Nat := 4983230072969 + 3 ^ 40 * 3501550 * 2
def baseEnd_3501550 : Nat := 1198652123833920268814447

theorem tailTrace_3501550 : CollatzResearch.WordTrace tailWord_3501550 prefixEnd_3501550 1198652123833920268814447 := by
  unfold tailWord_3501550
  simp only [CollatzResearch.WordTrace]
  refine ⟨15964002558061230246816763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85141346976326561316356069 15964002558061230246816763)
  ·
    refine ⟨23946003837091845370225145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15964002558061230246816763 23946003837091845370225145)
    ·
      refine ⟨17959502877818884027668859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23946003837091845370225145 17959502877818884027668859)
      ·
        refine ⟨26939254316728326041503289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17959502877818884027668859 26939254316728326041503289)
        ·
          refine ⟨20204440737546244531127467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26939254316728326041503289 20204440737546244531127467)
          ·
            refine ⟨30306661106319366796691201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20204440737546244531127467 30306661106319366796691201)
            ·
              refine ⟨22729995829739525097518401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30306661106319366796691201 22729995829739525097518401)
              ·
                refine ⟨17047496872304643823138801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22729995829739525097518401 17047496872304643823138801)
                ·
                  refine ⟨12785622654228482867354101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17047496872304643823138801 12785622654228482867354101)
                  ·
                    refine ⟨1198652123833920268814447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12785622654228482867354101 1198652123833920268814447)
                    ·
                      rfl

theorem cell22_3501550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3501550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501550 prefixEnd_3501550 := by exact prefixLift 3501550
  have htrace : WordTrace (prefixWord ++ tailWord_3501550) baseStart_3501550 baseEnd_3501550 := by
    simpa [prefixWord, tailWord_3501550, baseEnd_3501550] using wordTrace_append hprefix tailTrace_3501550
  have hstable : (prefixWord ++ tailWord_3501550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501550).length < 2 ^ (prefixWord ++ tailWord_3501550).sum := by decide
  have hdescent : baseEnd_3501550 < baseStart_3501550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501565 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_3501565 : Nat := 118140960795 + 3501565 * 2 ^ 59
def prefixEnd_3501565 : Nat := 4983230072969 + 3 ^ 40 * 3501565 * 2
def baseEnd_3501565 : Nat := 1198657258640465229689401

theorem tailTrace_3501565 : CollatzResearch.WordTrace tailWord_3501565 prefixEnd_3501565 1198657258640465229689401 := by
  unfold tailWord_3501565
  simp only [CollatzResearch.WordTrace]
  refine ⟨127712567559435499536330149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85141711706290333024220099 127712567559435499536330149)
  ·
    refine ⟨23946106417394156163061903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127712567559435499536330149 23946106417394156163061903)
    ·
      refine ⟨35919159626091234244592855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23946106417394156163061903 35919159626091234244592855)
      ·
        refine ⟨53878739439136851366889283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35919159626091234244592855 53878739439136851366889283)
        ·
          refine ⟨80818109158705277050333925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53878739439136851366889283 80818109158705277050333925)
          ·
            refine ⟨15153395467257239446937611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80818109158705277050333925 15153395467257239446937611)
            ·
              refine ⟨22730093200885859170406417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15153395467257239446937611 22730093200885859170406417)
              ·
                refine ⟨17047569900664394377804813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22730093200885859170406417 17047569900664394377804813)
                ·
                  refine ⟨6392838712749147891676805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17047569900664394377804813 6392838712749147891676805)
                  ·
                    refine ⟨1198657258640465229689401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6392838712749147891676805 1198657258640465229689401)
                    ·
                      rfl

theorem cell22_3501565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_3501565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501565 prefixEnd_3501565 := by exact prefixLift 3501565
  have htrace : WordTrace (prefixWord ++ tailWord_3501565) baseStart_3501565 baseEnd_3501565 := by
    simpa [prefixWord, tailWord_3501565, baseEnd_3501565] using wordTrace_append hprefix tailTrace_3501565
  have hstable : (prefixWord ++ tailWord_3501565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501565).length < 2 ^ (prefixWord ++ tailWord_3501565).sum := by decide
  have hdescent : baseEnd_3501565 < baseStart_3501565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501614 : List Nat := [4, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_3501614 : Nat := 118140960795 + 3501614 * 2 ^ 59
def prefixEnd_3501614 : Nat := 4983230072969 + 3 ^ 40 * 3501614 * 2
def baseEnd_3501614 : Nat := 399558010780615145071417

theorem tailTrace_3501614 : CollatzResearch.WordTrace tailWord_3501614 prefixEnd_3501614 399558010780615145071417 := by
  unfold tailWord_3501614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15964294342032247613107987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85142903157505320603242597 15964294342032247613107987)
  ·
    refine ⟨23946441513048371419661981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15964294342032247613107987 23946441513048371419661981)
    ·
      refine ⟨8979915567393139282373243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23946441513048371419661981 8979915567393139282373243)
      ·
        refine ⟨13469873351089708923559865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8979915567393139282373243 13469873351089708923559865)
        ·
          refine ⟨10102405013317281692669899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13469873351089708923559865 10102405013317281692669899)
          ·
            refine ⟨15153607519975922539004849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102405013317281692669899 15153607519975922539004849)
            ·
              refine ⟨11365205639981941904253637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15153607519975922539004849 11365205639981941904253637)
              ·
                refine ⟨2130976057496614107047557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11365205639981941904253637 2130976057496614107047557)
                ·
                  refine ⟨399558010780615145071417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130976057496614107047557 399558010780615145071417)
                  ·
                    rfl

theorem cell22_3501614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_3501614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501614 prefixEnd_3501614 := by exact prefixLift 3501614
  have htrace : WordTrace (prefixWord ++ tailWord_3501614) baseStart_3501614 baseEnd_3501614 := by
    simpa [prefixWord, tailWord_3501614, baseEnd_3501614] using wordTrace_append hprefix tailTrace_3501614
  have hstable : (prefixWord ++ tailWord_3501614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501614).length < 2 ^ (prefixWord ++ tailWord_3501614).sum := by decide
  have hdescent : baseEnd_3501614 < baseStart_3501614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501629 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_3501629 : Nat := 118140960795 + 3501629 * 2 ^ 59
def prefixEnd_3501629 : Nat := 4983230072969 + 3 ^ 40 * 3501629 * 2
def baseEnd_3501629 : Nat := 1198679167148390396089205

theorem tailTrace_3501629 : CollatzResearch.WordTrace tailWord_3501629 prefixEnd_3501629 1198679167148390396089205 := by
  unfold tailWord_3501629
  simp only [CollatzResearch.WordTrace]
  refine ⟨127714901831203638466659941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85143267887469092311106627 127714901831203638466659941)
  ·
    refine ⟨23946544093350682212498739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127714901831203638466659941 23946544093350682212498739)
    ·
      refine ⟨35919816140026023318748109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23946544093350682212498739 35919816140026023318748109)
      ·
        refine ⟨13469931052509758744530541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35919816140026023318748109 13469931052509758744530541)
        ·
          refine ⟨5051224144691159529198953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13469931052509758744530541 5051224144691159529198953)
          ·
            refine ⟨3788418108518369646899215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5051224144691159529198953 3788418108518369646899215)
            ·
              refine ⟨5682627162777554470348823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788418108518369646899215 5682627162777554470348823)
              ·
                refine ⟨8523940744166331705523235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682627162777554470348823 8523940744166331705523235)
                ·
                  refine ⟨12785911116249497558284853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523940744166331705523235 12785911116249497558284853)
                  ·
                    refine ⟨1198679167148390396089205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12785911116249497558284853 1198679167148390396089205)
                    ·
                      rfl

theorem cell22_3501629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_3501629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501629 prefixEnd_3501629 := by exact prefixLift 3501629
  have htrace : WordTrace (prefixWord ++ tailWord_3501629) baseStart_3501629 baseEnd_3501629 := by
    simpa [prefixWord, tailWord_3501629, baseEnd_3501629] using wordTrace_append hprefix tailTrace_3501629
  have hstable : (prefixWord ++ tailWord_3501629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501629).length < 2 ^ (prefixWord ++ tailWord_3501629).sum := by decide
  have hdescent : baseEnd_3501629 < baseStart_3501629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501661 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3501661 : Nat := 118140960795 + 3501661 * 2 ^ 59
def prefixEnd_3501661 : Nat := 4983230072969 + 3 ^ 40 * 3501661 * 2
def baseEnd_3501661 : Nat := 1198690121402352979289107

theorem tailTrace_3501661 : CollatzResearch.WordTrace tailWord_3501661 prefixEnd_3501661 1198690121402352979289107 := by
  unfold tailWord_3501661
  simp only [CollatzResearch.WordTrace]
  refine ⟨127716068967087707931824837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85144045978058471954549891 127716068967087707931824837)
  ·
    refine ⟨23946762931328945237217157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127716068967087707931824837 23946762931328945237217157)
    ·
      refine ⟨4490018049624177231978217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23946762931328945237217157 4490018049624177231978217)
      ·
        refine ⟨3367513537218132923983663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4490018049624177231978217 3367513537218132923983663)
        ·
          refine ⟨5051270305827199385975495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3367513537218132923983663 5051270305827199385975495)
          ·
            refine ⟨7576905458740799078963243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051270305827199385975495 7576905458740799078963243)
            ·
              refine ⟨11365358188111198618444865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7576905458740799078963243 11365358188111198618444865)
              ·
                refine ⟨8524018641083398963833649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11365358188111198618444865 8524018641083398963833649)
                ·
                  refine ⟨6393013980812549222875237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8524018641083398963833649 6393013980812549222875237)
                  ·
                    refine ⟨1198690121402352979289107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6393013980812549222875237 1198690121402352979289107)
                    ·
                      rfl

theorem cell22_3501661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3501661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501661 prefixEnd_3501661 := by exact prefixLift 3501661
  have htrace : WordTrace (prefixWord ++ tailWord_3501661) baseStart_3501661 baseEnd_3501661 := by
    simpa [prefixWord, tailWord_3501661, baseEnd_3501661] using wordTrace_append hprefix tailTrace_3501661
  have hstable : (prefixWord ++ tailWord_3501661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501661).length < 2 ^ (prefixWord ++ tailWord_3501661).sum := by decide
  have hdescent : baseEnd_3501661 < baseStart_3501661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501674 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_3501674 : Nat := 118140960795 + 3501674 * 2 ^ 59
def prefixEnd_3501674 : Nat := 4983230072969 + 3 ^ 40 * 3501674 * 2
def baseEnd_3501674 : Nat := 1198694571568025278714067

theorem tailTrace_3501674 : CollatzResearch.WordTrace tailWord_3501674 prefixEnd_3501674 1198694571568025278714067 := by
  unfold tailWord_3501674
  simp only [CollatzResearch.WordTrace]
  refine ⟨31929135779010152788012019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85144362077360407434698717 31929135779010152788012019)
  ·
    refine ⟨47893703668515229182018029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31929135779010152788012019 47893703668515229182018029)
    ·
      refine ⟨17960138875693210943256761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47893703668515229182018029 17960138875693210943256761)
      ·
        refine ⟨13470104156769908207442571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17960138875693210943256761 13470104156769908207442571)
        ·
          refine ⟨20205156235154862311163857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13470104156769908207442571 20205156235154862311163857)
          ·
            refine ⟨15153867176366146733372893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20205156235154862311163857 15153867176366146733372893)
            ·
              refine ⟨5682700191137305025014835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15153867176366146733372893 5682700191137305025014835)
              ·
                refine ⟨8524050286705957537522253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682700191137305025014835 8524050286705957537522253)
                ·
                  refine ⟨3196518857514734076570845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8524050286705957537522253 3196518857514734076570845)
                  ·
                    refine ⟨1198694571568025278714067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196518857514734076570845 1198694571568025278714067)
                    ·
                      rfl

theorem cell22_3501674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_3501674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501674 prefixEnd_3501674 := by exact prefixLift 3501674
  have htrace : WordTrace (prefixWord ++ tailWord_3501674) baseStart_3501674 baseEnd_3501674 := by
    simpa [prefixWord, tailWord_3501674, baseEnd_3501674] using wordTrace_append hprefix tailTrace_3501674
  have hstable : (prefixWord ++ tailWord_3501674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501674).length < 2 ^ (prefixWord ++ tailWord_3501674).sum := by decide
  have hdescent : baseEnd_3501674 < baseStart_3501674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501717 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_3501717 : Nat := 118140960795 + 3501717 * 2 ^ 59
def prefixEnd_3501717 : Nat := 4983230072969 + 3 ^ 40 * 3501717 * 2
def baseEnd_3501717 : Nat := 1198709291346787499888935

theorem tailTrace_3501717 : CollatzResearch.WordTrace tailWord_3501717 prefixEnd_3501717 1198709291346787499888935 := by
  unfold tailWord_3501717
  simp only [CollatzResearch.WordTrace]
  refine ⟨127718111454884829495863405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85145407636589886330575603 127718111454884829495863405)
  ·
    refine ⟨47894291795581811060948777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127718111454884829495863405 47894291795581811060948777)
    ·
      refine ⟨35920718846686358295711583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47894291795581811060948777 35920718846686358295711583)
      ·
        refine ⟨53881078270029537443567375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35920718846686358295711583 53881078270029537443567375)
        ·
          refine ⟨80821617405044306165351063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53881078270029537443567375 80821617405044306165351063)
          ·
            refine ⟨121232426107566459248026595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80821617405044306165351063 121232426107566459248026595)
            ·
              refine ⟨181848639161349688872039893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121232426107566459248026595 181848639161349688872039893)
              ·
                refine ⟨4262077480344133332938435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 181848639161349688872039893 4262077480344133332938435)
                ·
                  refine ⟨6393116220516199999407653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262077480344133332938435 6393116220516199999407653)
                  ·
                    refine ⟨1198709291346787499888935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6393116220516199999407653 1198709291346787499888935)
                    ·
                      rfl

theorem cell22_3501717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_3501717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501717 prefixEnd_3501717 := by exact prefixLift 3501717
  have htrace : WordTrace (prefixWord ++ tailWord_3501717) baseStart_3501717 baseEnd_3501717 := by
    simpa [prefixWord, tailWord_3501717, baseEnd_3501717] using wordTrace_append hprefix tailTrace_3501717
  have hstable : (prefixWord ++ tailWord_3501717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501717).length < 2 ^ (prefixWord ++ tailWord_3501717).sum := by decide
  have hdescent : baseEnd_3501717 < baseStart_3501717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501747 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 1, 5]
def baseStart_3501747 : Nat := 118140960795 + 3501747 * 2 ^ 59
def prefixEnd_3501747 : Nat := 4983230072969 + 3 ^ 40 * 3501747 * 2
def baseEnd_3501747 : Nat := 1198719560959877421638843

theorem tailTrace_3501747 : CollatzResearch.WordTrace tailWord_3501747 prefixEnd_3501747 1198719560959877421638843 := by
  unfold tailWord_3501747
  simp only [CollatzResearch.WordTrace]
  refine ⟨127719205644776144619455495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85146137096517429746303663 127719205644776144619455495)
  ·
    refine ⟨191578808467164216929183243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127719205644776144619455495 191578808467164216929183243)
    ·
      refine ⟨287368212700746325393774865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191578808467164216929183243 287368212700746325393774865)
      ·
        refine ⟨215526159525559744045331149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287368212700746325393774865 215526159525559744045331149)
        ·
          refine ⟨80822309822084904016999181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215526159525559744045331149 80822309822084904016999181)
          ·
            refine ⟨30308366183281839006374693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80822309822084904016999181 30308366183281839006374693)
            ·
              refine ⟨5682818659365344813695255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30308366183281839006374693 5682818659365344813695255)
              ·
                refine ⟨8524227989048017220542883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682818659365344813695255 8524227989048017220542883)
                ·
                  refine ⟨12786341983572025830814325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524227989048017220542883 12786341983572025830814325)
                  ·
                    refine ⟨1198719560959877421638843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12786341983572025830814325 1198719560959877421638843)
                    ·
                      rfl

theorem cell22_3501747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 5].length) (baseStart_3501747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501747 prefixEnd_3501747 := by exact prefixLift 3501747
  have htrace : WordTrace (prefixWord ++ tailWord_3501747) baseStart_3501747 baseEnd_3501747 := by
    simpa [prefixWord, tailWord_3501747, baseEnd_3501747] using wordTrace_append hprefix tailTrace_3501747
  have hstable : (prefixWord ++ tailWord_3501747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501747).length < 2 ^ (prefixWord ++ tailWord_3501747).sum := by decide
  have hdescent : baseEnd_3501747 < baseStart_3501747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501749 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 6]
def baseStart_3501749 : Nat := 118140960795 + 3501749 * 2 ^ 59
def prefixEnd_3501749 : Nat := 4983230072969 + 3 ^ 40 * 3501749 * 2
def baseEnd_3501749 : Nat := 399573415200250027696279

theorem tailTrace_3501749 : CollatzResearch.WordTrace tailWord_3501749 prefixEnd_3501749 399573415200250027696279 := by
  unfold tailWord_3501749
  simp only [CollatzResearch.WordTrace]
  refine ⟨127719278590768898961028301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85146185727179265974018867 127719278590768898961028301)
  ·
    refine ⟨47894729471538337110385613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127719278590768898961028301 47894729471538337110385613)
    ·
      refine ⟨17960523551826876416394605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47894729471538337110385613 17960523551826876416394605)
      ·
        refine ⟨6735196331935078656147977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17960523551826876416394605 6735196331935078656147977)
        ·
          refine ⟨5051397248951308992110983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6735196331935078656147977 5051397248951308992110983)
          ·
            refine ⟨7577095873426963488166475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051397248951308992110983 7577095873426963488166475)
            ·
              refine ⟨11365643810140445232249713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7577095873426963488166475 11365643810140445232249713)
              ·
                refine ⟨8524232857605333924187285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11365643810140445232249713 8524232857605333924187285)
                ·
                  refine ⟨399573415200250027696279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8524232857605333924187285 399573415200250027696279)
                  ·
                    rfl

theorem cell22_3501749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_3501749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501749 prefixEnd_3501749 := by exact prefixLift 3501749
  have htrace : WordTrace (prefixWord ++ tailWord_3501749) baseStart_3501749 baseEnd_3501749 := by
    simpa [prefixWord, tailWord_3501749, baseEnd_3501749] using wordTrace_append hprefix tailTrace_3501749
  have hstable : (prefixWord ++ tailWord_3501749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501749).length < 2 ^ (prefixWord ++ tailWord_3501749).sum := by decide
  have hdescent : baseEnd_3501749 < baseStart_3501749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501764 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3501764 : Nat := 118140960795 + 3501764 * 2 ^ 59
def prefixEnd_3501764 : Nat := 4983230072969 + 3 ^ 40 * 3501764 * 2
def baseEnd_3501764 : Nat := 1198725380407295043963791

theorem tailTrace_3501764 : CollatzResearch.WordTrace tailWord_3501764 prefixEnd_3501764 1198725380407295043963791 := by
  unfold tailWord_3501764
  simp only [CollatzResearch.WordTrace]
  refine ⟨63859912842857278261412173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85146550457143037681882897 63859912842857278261412173)
  ·
    refine ⟨23947467316071479348029565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63859912842857278261412173 23947467316071479348029565)
    ·
      refine ⟨8980300243526804755511087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23947467316071479348029565 8980300243526804755511087)
      ·
        refine ⟨13470450365290207133266631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8980300243526804755511087 13470450365290207133266631)
        ·
          refine ⟨20205675547935310699899947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13470450365290207133266631 20205675547935310699899947)
          ·
            refine ⟨30308513321902966049849921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20205675547935310699899947 30308513321902966049849921)
            ·
              refine ⟨22731384991427224537387441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30308513321902966049849921 22731384991427224537387441)
              ·
                refine ⟨17048538743570418403040581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22731384991427224537387441 17048538743570418403040581)
                ·
                  refine ⟨3196601014419453450570109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17048538743570418403040581 3196601014419453450570109)
                  ·
                    refine ⟨1198725380407295043963791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196601014419453450570109 1198725380407295043963791)
                    ·
                      rfl

theorem cell22_3501764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3501764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501764 prefixEnd_3501764 := by exact prefixLift 3501764
  have htrace : WordTrace (prefixWord ++ tailWord_3501764) baseStart_3501764 baseEnd_3501764 := by
    simpa [prefixWord, tailWord_3501764, baseEnd_3501764] using wordTrace_append hprefix tailTrace_3501764
  have hstable : (prefixWord ++ tailWord_3501764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501764).length < 2 ^ (prefixWord ++ tailWord_3501764).sum := by decide
  have hdescent : baseEnd_3501764 < baseStart_3501764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501775 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 1, 9]
def baseStart_3501775 : Nat := 118140960795 + 3501775 * 2 ^ 59
def prefixEnd_3501775 : Nat := 4983230072969 + 3 ^ 40 * 3501775 * 2
def baseEnd_3501775 : Nat := 1198729145932094681938757

theorem tailTrace_3501775 : CollatzResearch.WordTrace tailWord_3501775 prefixEnd_3501775 1198729145932094681938757 := by
  unfold tailWord_3501775
  simp only [CollatzResearch.WordTrace]
  refine ⟨127720226888674705401474779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85146817925783136934316519 127720226888674705401474779)
  ·
    refine ⟨191580340333012058102212169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127720226888674705401474779 191580340333012058102212169)
    ·
      refine ⟨143685255249759043576659127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191580340333012058102212169 143685255249759043576659127)
      ·
        refine ⟨215527882874638565364988691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143685255249759043576659127 215527882874638565364988691)
        ·
          refine ⟨323291824311957848047483037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215527882874638565364988691 323291824311957848047483037)
          ·
            refine ⟨121234434116984193017806139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323291824311957848047483037 121234434116984193017806139)
            ·
              refine ⟨181851651175476289526709209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121234434116984193017806139 181851651175476289526709209)
              ·
                refine ⟨136388738381607217145031907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181851651175476289526709209 136388738381607217145031907)
                ·
                  refine ⟨204583107572410825717547861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136388738381607217145031907 204583107572410825717547861)
                  ·
                    refine ⟨1198729145932094681938757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 204583107572410825717547861 1198729145932094681938757)
                    ·
                      rfl

theorem cell22_3501775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_3501775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501775 prefixEnd_3501775 := by exact prefixLift 3501775
  have htrace : WordTrace (prefixWord ++ tailWord_3501775) baseStart_3501775 baseEnd_3501775 := by
    simpa [prefixWord, tailWord_3501775, baseEnd_3501775] using wordTrace_append hprefix tailTrace_3501775
  have hstable : (prefixWord ++ tailWord_3501775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501775).length < 2 ^ (prefixWord ++ tailWord_3501775).sum := by decide
  have hdescent : baseEnd_3501775 < baseStart_3501775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501809 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 3, 3]
def baseStart_3501809 : Nat := 118140960795 + 3501809 * 2 ^ 59
def prefixEnd_3501809 : Nat := 4983230072969 + 3 ^ 40 * 3501809 * 2
def baseEnd_3501809 : Nat := 1198740784826929926588653

theorem tailTrace_3501809 : CollatzResearch.WordTrace tailWord_3501809 prefixEnd_3501809 1198740784826929926588653 := by
  unfold tailWord_3501809
  simp only [CollatzResearch.WordTrace]
  refine ⟨127721466970551529208212481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85147644647034352805474987 127721466970551529208212481)
  ·
    refine ⟨95791100227913646906159361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127721466970551529208212481 95791100227913646906159361)
    ·
      refine ⟨71843325170935235179619521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95791100227913646906159361 71843325170935235179619521)
      ·
        refine ⟨53882493878201426384714641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71843325170935235179619521 53882493878201426384714641)
        ·
          refine ⟨40411870408651069788535981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53882493878201426384714641 40411870408651069788535981)
          ·
            refine ⟨15154451403244151170700993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40411870408651069788535981 15154451403244151170700993)
            ·
              refine ⟨11365838552433113378025745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15154451403244151170700993 11365838552433113378025745)
              ·
                refine ⟨8524378914324835033519309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11365838552433113378025745 8524378914324835033519309)
                ·
                  refine ⟨3196642092871813137569741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8524378914324835033519309 3196642092871813137569741)
                  ·
                    refine ⟨1198740784826929926588653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196642092871813137569741 1198740784826929926588653)
                    ·
                      rfl

theorem cell22_3501809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_3501809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501809 prefixEnd_3501809 := by exact prefixLift 3501809
  have htrace : WordTrace (prefixWord ++ tailWord_3501809) baseStart_3501809 baseEnd_3501809 := by
    simpa [prefixWord, tailWord_3501809, baseEnd_3501809] using wordTrace_append hprefix tailTrace_3501809
  have hstable : (prefixWord ++ tailWord_3501809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501809).length < 2 ^ (prefixWord ++ tailWord_3501809).sum := by decide
  have hdescent : baseEnd_3501809 < baseStart_3501809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501894 : List Nat := [6, 1, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3501894 : Nat := 118140960795 + 3501894 * 2 ^ 59
def prefixEnd_3501894 : Nat := 4983230072969 + 3 ^ 40 * 3501894 * 2
def baseEnd_3501894 : Nat := 1198769882064018038213393

theorem tailTrace_3501894 : CollatzResearch.WordTrace tailWord_3501894 prefixEnd_3501894 1198769882064018038213393 := by
  unfold tailWord_3501894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991392724226362147658023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85149711450162392483371157 3991392724226362147658023)
  ·
    refine ⟨5987089086339543221487035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3991392724226362147658023 5987089086339543221487035)
    ·
      refine ⟨8980633629509314832230553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5987089086339543221487035 8980633629509314832230553)
      ·
        refine ⟨6735475222131986124172915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8980633629509314832230553 6735475222131986124172915)
        ·
          refine ⟨10103212833197979186259373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6735475222131986124172915 10103212833197979186259373)
          ·
            refine ⟨3788704812449242194847265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10103212833197979186259373 3788704812449242194847265)
            ·
              refine ⟨2841528609336931646135449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3788704812449242194847265 2841528609336931646135449)
              ·
                refine ⟨2131146457002698734601587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2841528609336931646135449 2131146457002698734601587)
                ·
                  refine ⟨3196719685504048101902381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131146457002698734601587 3196719685504048101902381)
                  ·
                    refine ⟨1198769882064018038213393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196719685504048101902381 1198769882064018038213393)
                    ·
                      rfl

theorem cell22_3501894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3501894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501894 prefixEnd_3501894 := by exact prefixLift 3501894
  have htrace : WordTrace (prefixWord ++ tailWord_3501894) baseStart_3501894 baseEnd_3501894 := by
    simpa [prefixWord, tailWord_3501894, baseEnd_3501894] using wordTrace_append hprefix tailTrace_3501894
  have hstable : (prefixWord ++ tailWord_3501894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501894).length < 2 ^ (prefixWord ++ tailWord_3501894).sum := by decide
  have hdescent : baseEnd_3501894 < baseStart_3501894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501950 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3501950 : Nat := 118140960795 + 3501950 * 2 ^ 59
def prefixEnd_3501950 : Nat := 4983230072969 + 3 ^ 40 * 3501950 * 2
def baseEnd_3501950 : Nat := 1198789052008452558813221

theorem tailTrace_3501950 : CollatzResearch.WordTrace tailWord_3501950 prefixEnd_3501950 1198789052008452558813221 := by
  unfold tailWord_3501950
  simp only [CollatzResearch.WordTrace]
  refine ⟨15965826207880088786136913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85151073108693806859396869 15965826207880088786136913)
  ·
    refine ⟨11974369655910066589602685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15965826207880088786136913 11974369655910066589602685)
    ·
      refine ⟨4490388620966274971101007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11974369655910066589602685 4490388620966274971101007)
      ·
        refine ⟨6735582931449412456651511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4490388620966274971101007 6735582931449412456651511)
        ·
          refine ⟨10103374397174118684977267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6735582931449412456651511 10103374397174118684977267)
          ·
            refine ⟨15155061595761178027465901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10103374397174118684977267 15155061595761178027465901)
            ·
              refine ⟨5683148098410441760299713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15155061595761178027465901 5683148098410441760299713)
              ·
                refine ⟨4262361073807831320224785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5683148098410441760299713 4262361073807831320224785)
                ·
                  refine ⟨3196770805355873490168589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262361073807831320224785 3196770805355873490168589)
                  ·
                    refine ⟨1198789052008452558813221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196770805355873490168589 1198789052008452558813221)
                    ·
                      rfl

theorem cell22_3501950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3501950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501950 prefixEnd_3501950 := by exact prefixLift 3501950
  have htrace : WordTrace (prefixWord ++ tailWord_3501950) baseStart_3501950 baseEnd_3501950 := by
    simpa [prefixWord, tailWord_3501950, baseEnd_3501950] using wordTrace_append hprefix tailTrace_3501950
  have hstable : (prefixWord ++ tailWord_3501950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501950).length < 2 ^ (prefixWord ++ tailWord_3501950).sum := by decide
  have hdescent : baseEnd_3501950 < baseStart_3501950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501961 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 3, 3]
def baseStart_3501961 : Nat := 118140960795 + 3501961 * 2 ^ 59
def prefixEnd_3501961 : Nat := 4983230072969 + 3 ^ 40 * 3501961 * 2
def baseEnd_3501961 : Nat := 1198792817533252196788187

theorem tailTrace_3501961 : CollatzResearch.WordTrace tailWord_3501961 prefixEnd_3501961 1198792817533252196788187 := by
  unfold tailWord_3501961
  simp only [CollatzResearch.WordTrace]
  refine ⟨127727010866000859167745737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85151340577333906111830491 127727010866000859167745737)
  ·
    refine ⟨95795258149500644375809303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127727010866000859167745737 95795258149500644375809303)
    ·
      refine ⟨143692887224250966563713955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95795258149500644375809303 143692887224250966563713955)
      ·
        refine ⟨215539330836376449845570933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143692887224250966563713955 215539330836376449845570933)
        ·
          refine ⟨20206812265910292173022275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215539330836376449845570933 20206812265910292173022275)
          ·
            refine ⟨30310218398865438259533413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20206812265910292173022275 30310218398865438259533413)
            ·
              refine ⟨5683165949787269673662515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30310218398865438259533413 5683165949787269673662515)
              ·
                refine ⟨8524748924680904510493773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683165949787269673662515 8524748924680904510493773)
                ·
                  refine ⟨3196780846755339191435165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8524748924680904510493773 3196780846755339191435165)
                  ·
                    refine ⟨1198792817533252196788187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196780846755339191435165 1198792817533252196788187)
                    ·
                      rfl

theorem cell22_3501961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_3501961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3501961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3501961 prefixEnd_3501961 := by exact prefixLift 3501961
  have htrace : WordTrace (prefixWord ++ tailWord_3501961) baseStart_3501961 baseEnd_3501961 := by
    simpa [prefixWord, tailWord_3501961, baseEnd_3501961] using wordTrace_append hprefix tailTrace_3501961
  have hstable : (prefixWord ++ tailWord_3501961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501961).length < 2 ^ (prefixWord ++ tailWord_3501961).sum := by decide
  have hdescent : baseEnd_3501961 < baseStart_3501961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502012 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 3, 3]
def baseStart_3502012 : Nat := 118140960795 + 3502012 * 2 ^ 59
def prefixEnd_3502012 : Nat := 4983230072969 + 3 ^ 40 * 3502012 * 2
def baseEnd_3502012 : Nat := 1198810275875505063763031

theorem tailTrace_3502012 : CollatzResearch.WordTrace tailWord_3502012 prefixEnd_3502012 1198810275875505063763031 := by
  unfold tailWord_3502012
  simp only [CollatzResearch.WordTrace]
  refine ⟨63864435494408047438926145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85152580659210729918568193 63864435494408047438926145)
  ·
    refine ⟨47898326620806035579194609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63864435494408047438926145 47898326620806035579194609)
    ·
      refine ⟨35923744965604526684395957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47898326620806035579194609 35923744965604526684395957)
      ·
        refine ⟨3367851090525424376662121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35923744965604526684395957 3367851090525424376662121)
        ·
          refine ⟨2525888317894068282496591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3367851090525424376662121 2525888317894068282496591)
          ·
            refine ⟨3788832476841102423744887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525888317894068282496591 3788832476841102423744887)
            ·
              refine ⟨5683248715261653635617331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788832476841102423744887 5683248715261653635617331)
              ·
                refine ⟨8524873072892480453425997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683248715261653635617331 8524873072892480453425997)
                ·
                  refine ⟨3196827402334680170034749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8524873072892480453425997 3196827402334680170034749)
                  ·
                    refine ⟨1198810275875505063763031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196827402334680170034749 1198810275875505063763031)
                    ·
                      rfl

theorem cell22_3502012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_3502012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502012 prefixEnd_3502012 := by exact prefixLift 3502012
  have htrace : WordTrace (prefixWord ++ tailWord_3502012) baseStart_3502012 baseEnd_3502012 := by
    simpa [prefixWord, tailWord_3502012, baseEnd_3502012] using wordTrace_append hprefix tailTrace_3502012
  have hstable : (prefixWord ++ tailWord_3502012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502012).length < 2 ^ (prefixWord ++ tailWord_3502012).sum := by decide
  have hdescent : baseEnd_3502012 < baseStart_3502012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502049 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_3502049 : Nat := 118140960795 + 3502049 * 2 ^ 59
def prefixEnd_3502049 : Nat := 4983230072969 + 3 ^ 40 * 3502049 * 2
def baseEnd_3502049 : Nat := 1198822941731649300587917

theorem tailTrace_3502049 : CollatzResearch.WordTrace tailWord_3502049 prefixEnd_3502049 1198822941731649300587917 := by
  unfold tailWord_3502049
  simp only [CollatzResearch.WordTrace]
  refine ⟨127730220489682050196949201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85153480326454700131299467 127730220489682050196949201)
  ·
    refine ⟨95797665367261537647711901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127730220489682050196949201 95797665367261537647711901)
    ·
      refine ⟨35924124512723076617891963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95797665367261537647711901 35924124512723076617891963)
      ·
        refine ⟨53886186769084614926837945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35924124512723076617891963 53886186769084614926837945)
        ·
          refine ⟨40414640076813461195128459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53886186769084614926837945 40414640076813461195128459)
          ·
            refine ⟨60621960115220191792692689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40414640076813461195128459 60621960115220191792692689)
            ·
              refine ⟨45466470086415143844519517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60621960115220191792692689 45466470086415143844519517)
              ·
                refine ⟨17049926282405678941694819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45466470086415143844519517 17049926282405678941694819)
                ·
                  refine ⟨25574889423608518412542229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17049926282405678941694819 25574889423608518412542229)
                  ·
                    refine ⟨1198822941731649300587917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25574889423608518412542229 1198822941731649300587917)
                    ·
                      rfl

theorem cell22_3502049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_3502049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502049 prefixEnd_3502049 := by exact prefixLift 3502049
  have htrace : WordTrace (prefixWord ++ tailWord_3502049) baseStart_3502049 baseEnd_3502049 := by
    simpa [prefixWord, tailWord_3502049, baseEnd_3502049] using wordTrace_append hprefix tailTrace_3502049
  have hstable : (prefixWord ++ tailWord_3502049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502049).length < 2 ^ (prefixWord ++ tailWord_3502049).sum := by decide
  have hdescent : baseEnd_3502049 < baseStart_3502049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502051 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 1, 5]
def baseStart_3502051 : Nat := 118140960795 + 3502051 * 2 ^ 59
def prefixEnd_3502051 : Nat := 4983230072969 + 3 ^ 40 * 3502051 * 2
def baseEnd_3502051 : Nat := 1198823626372521962037911

theorem tailTrace_3502051 : CollatzResearch.WordTrace tailWord_3502051 prefixEnd_3502051 1198823626372521962037911 := by
  unfold tailWord_3502051
  simp only [CollatzResearch.WordTrace]
  refine ⟨127730293435674804538522007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85153528957116536359014671 127730293435674804538522007)
  ·
    refine ⟨191595440153512206807783011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127730293435674804538522007 191595440153512206807783011)
    ·
      refine ⟨287393160230268310211674517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191595440153512206807783011 287393160230268310211674517)
      ·
        refine ⟨13471554385793827041172243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 287393160230268310211674517 13471554385793827041172243)
        ·
          refine ⟨20207331578690740561758365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13471554385793827041172243 20207331578690740561758365)
          ·
            refine ⟨7577749342009027710659387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20207331578690740561758365 7577749342009027710659387)
            ·
              refine ⟨11366624013013541565989081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7577749342009027710659387 11366624013013541565989081)
              ·
                refine ⟨8524968009760156174491811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11366624013013541565989081 8524968009760156174491811)
                ·
                  refine ⟨12787452014640234261737717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524968009760156174491811 12787452014640234261737717)
                  ·
                    refine ⟨1198823626372521962037911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12787452014640234261737717 1198823626372521962037911)
                    ·
                      rfl

theorem cell22_3502051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 5].length) (baseStart_3502051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502051 prefixEnd_3502051 := by exact prefixLift 3502051
  have htrace : WordTrace (prefixWord ++ tailWord_3502051) baseStart_3502051 baseEnd_3502051 := by
    simpa [prefixWord, tailWord_3502051, baseEnd_3502051] using wordTrace_append hprefix tailTrace_3502051
  have hstable : (prefixWord ++ tailWord_3502051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502051).length < 2 ^ (prefixWord ++ tailWord_3502051).sum := by decide
  have hdescent : baseEnd_3502051 < baseStart_3502051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502055 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 1, 4]
def baseStart_3502055 : Nat := 118140960795 + 3502055 * 2 ^ 59
def prefixEnd_3502055 : Nat := 4983230072969 + 3 ^ 40 * 3502055 * 2
def baseEnd_3502055 : Nat := 1198824995654267284937899

theorem tailTrace_3502055 : CollatzResearch.WordTrace tailWord_3502055 prefixEnd_3502055 1198824995654267284937899 := by
  unfold tailWord_3502055
  simp only [CollatzResearch.WordTrace]
  refine ⟨127730439327660313221667619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85153626218440208814445079 127730439327660313221667619)
  ·
    refine ⟨191595658991490469832501429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127730439327660313221667619 191595658991490469832501429)
    ·
      refine ⟨17962093030452231546797009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191595658991490469832501429 17962093030452231546797009)
      ·
        refine ⟨13471569772839173660097757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17962093030452231546797009 13471569772839173660097757)
        ·
          refine ⟨5051838664814690122536659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13471569772839173660097757 5051838664814690122536659)
          ·
            refine ⟨7577757997222035183804989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051838664814690122536659 7577757997222035183804989)
            ·
              refine ⟨2841659248958263193926871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7577757997222035183804989 2841659248958263193926871)
              ·
                refine ⟨4262488873437394790890307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2841659248958263193926871 4262488873437394790890307)
                ·
                  refine ⟨6393733310156092186335461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262488873437394790890307 6393733310156092186335461)
                  ·
                    refine ⟨1198824995654267284937899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6393733310156092186335461 1198824995654267284937899)
                    ·
                      rfl

theorem cell22_3502055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_3502055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502055 prefixEnd_3502055 := by exact prefixLift 3502055
  have htrace : WordTrace (prefixWord ++ tailWord_3502055) baseStart_3502055 baseEnd_3502055 := by
    simpa [prefixWord, tailWord_3502055, baseEnd_3502055] using wordTrace_append hprefix tailTrace_3502055
  have hstable : (prefixWord ++ tailWord_3502055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502055).length < 2 ^ (prefixWord ++ tailWord_3502055).sum := by decide
  have hdescent : baseEnd_3502055 < baseStart_3502055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502070 : List Nat := [5, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_3502070 : Nat := 118140960795 + 3502070 * 2 ^ 59
def prefixEnd_3502070 : Nat := 4983230072969 + 3 ^ 40 * 3502070 * 2
def baseEnd_3502070 : Nat := 399610043486937415270951

theorem tailTrace_3502070 : CollatzResearch.WordTrace tailWord_3502070 prefixEnd_3502070 399610043486937415270951 := by
  unfold tailWord_3502070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7983186651412873173966479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85153990948403980522309109 7983186651412873173966479)
  ·
    refine ⟨11974779977119309760949719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7983186651412873173966479 11974779977119309760949719)
    ·
      refine ⟨17962169965678964641424579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11974779977119309760949719 17962169965678964641424579)
      ·
        refine ⟨26943254948518446962136869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17962169965678964641424579 26943254948518446962136869)
        ·
          refine ⟨5051860302847208805400663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26943254948518446962136869 5051860302847208805400663)
          ·
            refine ⟨7577790454270813208100995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051860302847208805400663 7577790454270813208100995)
            ·
              refine ⟨11366685681406219812151493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7577790454270813208100995 11366685681406219812151493)
              ·
                refine ⟨2131253565263666214778405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11366685681406219812151493 2131253565263666214778405)
                ·
                  refine ⟨399610043486937415270951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2131253565263666214778405 399610043486937415270951)
                  ·
                    rfl

theorem cell22_3502070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_3502070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502070 prefixEnd_3502070 := by exact prefixLift 3502070
  have htrace : WordTrace (prefixWord ++ tailWord_3502070) baseStart_3502070 baseEnd_3502070 := by
    simpa [prefixWord, tailWord_3502070, baseEnd_3502070] using wordTrace_append hprefix tailTrace_3502070
  have hstable : (prefixWord ++ tailWord_3502070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502070).length < 2 ^ (prefixWord ++ tailWord_3502070).sum := by decide
  have hdescent : baseEnd_3502070 < baseStart_3502070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502096 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 3, 3]
def baseStart_3502096 : Nat := 118140960795 + 3502096 * 2 ^ 59
def prefixEnd_3502096 : Nat := 4983230072969 + 3 ^ 40 * 3502096 * 2
def baseEnd_3502096 : Nat := 1198839030792156844662773

theorem tailTrace_3502096 : CollatzResearch.WordTrace tailWord_3502096 prefixEnd_3502096 1198839030792156844662773 := by
  unfold tailWord_3502096
  simp only [CollatzResearch.WordTrace]
  refine ⟨63865967360255888611955071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85154623147007851482606761 63865967360255888611955071)
  ·
    refine ⟨95798951040383832917932607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63865967360255888611955071 95798951040383832917932607)
    ·
      refine ⟨143698426560575749376898911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95798951040383832917932607 143698426560575749376898911)
      ·
        refine ⟨215547639840863624065348367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143698426560575749376898911 215547639840863624065348367)
        ·
          refine ⟨323321459761295436098022551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215547639840863624065348367 323321459761295436098022551)
          ·
            refine ⟨484982189641943154147033827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323321459761295436098022551 484982189641943154147033827)
            ·
              refine ⟨727473284462914731220550741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484982189641943154147033827 727473284462914731220550741)
              ·
                refine ⟨8525077552299782006490829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 727473284462914731220550741 8525077552299782006490829)
                ·
                  refine ⟨3196904082112418252434061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8525077552299782006490829 3196904082112418252434061)
                  ·
                    refine ⟨1198839030792156844662773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196904082112418252434061 1198839030792156844662773)
                    ·
                      rfl

theorem cell22_3502096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_3502096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502096 prefixEnd_3502096 := by exact prefixLift 3502096
  have htrace : WordTrace (prefixWord ++ tailWord_3502096) baseStart_3502096 baseEnd_3502096 := by
    simpa [prefixWord, tailWord_3502096, baseEnd_3502096] using wordTrace_append hprefix tailTrace_3502096
  have hstable : (prefixWord ++ tailWord_3502096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502096).length < 2 ^ (prefixWord ++ tailWord_3502096).sum := by decide
  have hdescent : baseEnd_3502096 < baseStart_3502096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502100 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3502100 : Nat := 118140960795 + 3502100 * 2 ^ 59
def prefixEnd_3502100 : Nat := 4983230072969 + 3 ^ 40 * 3502100 * 2
def baseEnd_3502100 : Nat := 1198840400073902167562761

theorem tailTrace_3502100 : CollatzResearch.WordTrace tailWord_3502100 prefixEnd_3502100 1198840400073902167562761 := by
  unfold tailWord_3502100
  simp only [CollatzResearch.WordTrace]
  refine ⟨63866040306248642953527877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85154720408331523938037169 63866040306248642953527877)
  ·
    refine ⟨11974882557421620553786477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63866040306248642953527877 11974882557421620553786477)
    ·
      refine ⟨4490580959033107707669929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11974882557421620553786477 4490580959033107707669929)
      ·
        refine ⟨3367935719274830780752447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4490580959033107707669929 3367935719274830780752447)
        ·
          refine ⟨5051903578912246171128671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3367935719274830780752447 5051903578912246171128671)
          ·
            refine ⟨7577855368368369256693007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051903578912246171128671 7577855368368369256693007)
            ·
              refine ⟨11366783052552553885039511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7577855368368369256693007 11366783052552553885039511)
              ·
                refine ⟨17050174578828830827559267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11366783052552553885039511 17050174578828830827559267)
                ·
                  refine ⟨25575261868243246241338901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17050174578828830827559267 25575261868243246241338901)
                  ·
                    refine ⟨1198840400073902167562761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25575261868243246241338901 1198840400073902167562761)
                    ·
                      rfl

theorem cell22_3502100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3502100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502100 prefixEnd_3502100 := by exact prefixLift 3502100
  have htrace : WordTrace (prefixWord ++ tailWord_3502100) baseStart_3502100 baseEnd_3502100 := by
    simpa [prefixWord, tailWord_3502100, baseEnd_3502100] using wordTrace_append hprefix tailTrace_3502100
  have hstable : (prefixWord ++ tailWord_3502100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502100).length < 2 ^ (prefixWord ++ tailWord_3502100).sum := by decide
  have hdescent : baseEnd_3502100 < baseStart_3502100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502119 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3502119 : Nat := 118140960795 + 3502119 * 2 ^ 59
def prefixEnd_3502119 : Nat := 4983230072969 + 3 ^ 40 * 3502119 * 2
def baseEnd_3502119 : Nat := 1198846904162192451337703

theorem tailTrace_3502119 : CollatzResearch.WordTrace tailWord_3502119 prefixEnd_3502119 1198846904162192451337703 := by
  unfold tailWord_3502119
  simp only [CollatzResearch.WordTrace]
  refine ⟨127732773599428452151997411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85155182399618968101331607 127732773599428452151997411)
  ·
    refine ⟨191599160399142678227996117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127732773599428452151997411 191599160399142678227996117)
    ·
      refine ⟨4490605321854906520968659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 191599160399142678227996117 4490605321854906520968659)
      ·
        refine ⟨6735907982782359781452989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4490605321854906520968659 6735907982782359781452989)
        ·
          refine ⟨2525965493543384918044871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6735907982782359781452989 2525965493543384918044871)
          ·
            refine ⟨3788948240315077377067307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525965493543384918044871 3788948240315077377067307)
            ·
              refine ⟨5683422360472616065600961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788948240315077377067307 5683422360472616065600961)
              ·
                refine ⟨4262566770354462049200721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5683422360472616065600961 4262566770354462049200721)
                ·
                  refine ⟨3196925077765846536900541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262566770354462049200721 3196925077765846536900541)
                  ·
                    refine ⟨1198846904162192451337703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196925077765846536900541 1198846904162192451337703)
                    ·
                      rfl

theorem cell22_3502119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3502119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502119 prefixEnd_3502119 := by exact prefixLift 3502119
  have htrace : WordTrace (prefixWord ++ tailWord_3502119) baseStart_3502119 baseEnd_3502119 := by
    simpa [prefixWord, tailWord_3502119, baseEnd_3502119] using wordTrace_append hprefix tailTrace_3502119
  have hstable : (prefixWord ++ tailWord_3502119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502119).length < 2 ^ (prefixWord ++ tailWord_3502119).sum := by decide
  have hdescent : baseEnd_3502119 < baseStart_3502119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502130 : List Nat := [3, 2, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_3502130 : Nat := 118140960795 + 3502130 * 2 ^ 59
def prefixEnd_3502130 : Nat := 4983230072969 + 3 ^ 40 * 3502130 * 2
def baseEnd_3502130 : Nat := 1198850669686992089312669

theorem tailTrace_3502130 : CollatzResearch.WordTrace tailWord_3502130 prefixEnd_3502130 1198850669686992089312669 := by
  unfold tailWord_3502130
  simp only [CollatzResearch.WordTrace]
  refine ⟨31933293700597150257661961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85155449868259067353765229 31933293700597150257661961)
  ·
    refine ⟨23949970275447862693246471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31933293700597150257661961 23949970275447862693246471)
    ·
      refine ⟨35924955413171794039869707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23949970275447862693246471 35924955413171794039869707)
      ·
        refine ⟨53887433119757691059804561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35924955413171794039869707 53887433119757691059804561)
        ·
          refine ⟨40415574839818268294853421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53887433119757691059804561 40415574839818268294853421)
          ·
            refine ⟨15155840564931850610570033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40415574839818268294853421 15155840564931850610570033)
            ·
              refine ⟨11366880423698887957927525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15155840564931850610570033 11366880423698887957927525)
              ·
                refine ⟨2131290079443541492111411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11366880423698887957927525 2131290079443541492111411)
                ·
                  refine ⟨3196935119165312238167117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131290079443541492111411 3196935119165312238167117)
                  ·
                    refine ⟨1198850669686992089312669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196935119165312238167117 1198850669686992089312669)
                    ·
                      rfl

theorem cell22_3502130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_3502130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502130 prefixEnd_3502130 := by exact prefixLift 3502130
  have htrace : WordTrace (prefixWord ++ tailWord_3502130) baseStart_3502130 baseEnd_3502130 := by
    simpa [prefixWord, tailWord_3502130, baseEnd_3502130] using wordTrace_append hprefix tailTrace_3502130
  have hstable : (prefixWord ++ tailWord_3502130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502130).length < 2 ^ (prefixWord ++ tailWord_3502130).sum := by decide
  have hdescent : baseEnd_3502130 < baseStart_3502130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502141 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_3502141 : Nat := 118140960795 + 3502141 * 2 ^ 59
def prefixEnd_3502141 : Nat := 4983230072969 + 3 ^ 40 * 3502141 * 2
def baseEnd_3502141 : Nat := 1198854435211791727287635

theorem tailTrace_3502141 : CollatzResearch.WordTrace tailWord_3502141 prefixEnd_3502141 1198854435211791727287635 := by
  unfold tailWord_3502141
  simp only [CollatzResearch.WordTrace]
  refine ⟨127733576005348749909298277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85155717336899166606198851 127733576005348749909298277)
  ·
    refine ⟨23950045501002890607993427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127733576005348749909298277 23950045501002890607993427)
    ·
      refine ⟨35925068251504335911990141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23950045501002890607993427 35925068251504335911990141)
      ·
        refine ⟨13471900594314125966996303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35925068251504335911990141 13471900594314125966996303)
        ·
          refine ⟨20207850891471188950494455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13471900594314125966996303 20207850891471188950494455)
          ·
            refine ⟨30311776337206783425741683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20207850891471188950494455 30311776337206783425741683)
            ·
              refine ⟨45467664505810175138612525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30311776337206783425741683 45467664505810175138612525)
              ·
                refine ⟨17050374189678815676979697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45467664505810175138612525 17050374189678815676979697)
                ·
                  refine ⟨12787780642259111757734773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17050374189678815676979697 12787780642259111757734773)
                  ·
                    refine ⟨1198854435211791727287635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12787780642259111757734773 1198854435211791727287635)
                    ·
                      rfl

theorem cell22_3502141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_3502141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502141 prefixEnd_3502141 := by exact prefixLift 3502141
  have htrace : WordTrace (prefixWord ++ tailWord_3502141) baseStart_3502141 baseEnd_3502141 := by
    simpa [prefixWord, tailWord_3502141, baseEnd_3502141] using wordTrace_append hprefix tailTrace_3502141
  have hstable : (prefixWord ++ tailWord_3502141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502141).length < 2 ^ (prefixWord ++ tailWord_3502141).sum := by decide
  have hdescent : baseEnd_3502141 < baseStart_3502141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502156 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_3502156 : Nat := 118140960795 + 3502156 * 2 ^ 59
def prefixEnd_3502156 : Nat := 4983230072969 + 3 ^ 40 * 3502156 * 2
def baseEnd_3502156 : Nat := 1198859570018336688162589

theorem tailTrace_3502156 : CollatzResearch.WordTrace tailWord_3502156 prefixEnd_3502156 1198859570018336688162589 := by
  unfold tailWord_3502156
  simp only [CollatzResearch.WordTrace]
  refine ⟨63867061550147203735547161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85156082066862938314062881 63867061550147203735547161)
  ·
    refine ⟨47900296162610402801660371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63867061550147203735547161 47900296162610402801660371)
    ·
      refine ⟨71850444243915604202490557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47900296162610402801660371 71850444243915604202490557)
      ·
        refine ⟨26943916591468351575933959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71850444243915604202490557 26943916591468351575933959)
        ·
          refine ⟨40415874887202527363900939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26943916591468351575933959 40415874887202527363900939)
          ·
            refine ⟨60623812330803791045851409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40415874887202527363900939 60623812330803791045851409)
            ·
              refine ⟨45467859248102843284388557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60623812330803791045851409 45467859248102843284388557)
              ·
                refine ⟨17050447218038566231645709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45467859248102843284388557 17050447218038566231645709)
                ·
                  refine ⟨6393917706764462336867141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17050447218038566231645709 6393917706764462336867141)
                  ·
                    refine ⟨1198859570018336688162589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6393917706764462336867141 1198859570018336688162589)
                    ·
                      rfl

theorem cell22_3502156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_3502156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502156 prefixEnd_3502156 := by exact prefixLift 3502156
  have htrace : WordTrace (prefixWord ++ tailWord_3502156) baseStart_3502156 baseEnd_3502156 := by
    simpa [prefixWord, tailWord_3502156, baseEnd_3502156] using wordTrace_append hprefix tailTrace_3502156
  have hstable : (prefixWord ++ tailWord_3502156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502156).length < 2 ^ (prefixWord ++ tailWord_3502156).sum := by decide
  have hdescent : baseEnd_3502156 < baseStart_3502156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502188 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 6]
def baseStart_3502188 : Nat := 118140960795 + 3502188 * 2 ^ 59
def prefixEnd_3502188 : Nat := 4983230072969 + 3 ^ 40 * 3502188 * 2
def baseEnd_3502188 : Nat := 399623508090766423787497

theorem tailTrace_3502188 : CollatzResearch.WordTrace tailWord_3502188 prefixEnd_3502188 399623508090766423787497 := by
  unfold tailWord_3502188
  simp only [CollatzResearch.WordTrace]
  refine ⟨63867645118089238468129609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85156860157452317957506145 63867645118089238468129609)
  ·
    refine ⟨47900733838566928851097207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63867645118089238468129609 47900733838566928851097207)
    ·
      refine ⟨71851100757850393276645811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47900733838566928851097207 71851100757850393276645811)
      ·
        refine ⟨107776651136775589914968717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71851100757850393276645811 107776651136775589914968717)
        ·
          refine ⟨40416244176290846218113269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107776651136775589914968717 40416244176290846218113269)
          ·
            refine ⟨3789022891527266832948119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40416244176290846218113269 3789022891527266832948119)
            ·
              refine ⟨5683534337290900249422179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3789022891527266832948119 5683534337290900249422179)
              ·
                refine ⟨8525301505936350374133269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683534337290900249422179 8525301505936350374133269)
                ·
                  refine ⟨399623508090766423787497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8525301505936350374133269 399623508090766423787497)
                  ·
                    rfl

theorem cell22_3502188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_3502188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502188 prefixEnd_3502188 := by exact prefixLift 3502188
  have htrace : WordTrace (prefixWord ++ tailWord_3502188) baseStart_3502188 baseEnd_3502188 := by
    simpa [prefixWord, tailWord_3502188, baseEnd_3502188] using wordTrace_append hprefix tailTrace_3502188
  have hstable : (prefixWord ++ tailWord_3502188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502188).length < 2 ^ (prefixWord ++ tailWord_3502188).sum := by decide
  have hdescent : baseEnd_3502188 < baseStart_3502188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502218 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_3502218 : Nat := 118140960795 + 3502218 * 2 ^ 59
def prefixEnd_3502218 : Nat := 4983230072969 + 3 ^ 40 * 3502218 * 2
def baseEnd_3502218 : Nat := 1198880793885389193112399

theorem tailTrace_3502218 : CollatzResearch.WordTrace tailWord_3502218 prefixEnd_3502218 1198880793885389193112399 := by
  unfold tailWord_3502218
  simp only [CollatzResearch.WordTrace]
  refine ⟨31934096106517448014962827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85157589617379861373234205 31934096106517448014962827)
  ·
    refine ⟨47901144159776172022444241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31934096106517448014962827 47901144159776172022444241)
    ·
      refine ⟨35925858119832129016833181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47901144159776172022444241 35925858119832129016833181)
      ·
        refine ⟨13472196794937048381312443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35925858119832129016833181 13472196794937048381312443)
        ·
          refine ⟨20208295192405572571968665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13472196794937048381312443 20208295192405572571968665)
          ·
            refine ⟨15156221394304179428976499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20208295192405572571968665 15156221394304179428976499)
            ·
              refine ⟨22734332091456269143464749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15156221394304179428976499 22734332091456269143464749)
              ·
                refine ⟨8525374534296100928799281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22734332091456269143464749 8525374534296100928799281)
                ·
                  refine ⟨6394030900722075696599461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8525374534296100928799281 6394030900722075696599461)
                  ·
                    refine ⟨1198880793885389193112399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6394030900722075696599461 1198880793885389193112399)
                    ·
                      rfl

theorem cell22_3502218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_3502218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502218 prefixEnd_3502218 := by exact prefixLift 3502218
  have htrace : WordTrace (prefixWord ++ tailWord_3502218) baseStart_3502218 baseEnd_3502218 := by
    simpa [prefixWord, tailWord_3502218, baseEnd_3502218] using wordTrace_append hprefix tailTrace_3502218
  have hstable : (prefixWord ++ tailWord_3502218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502218).length < 2 ^ (prefixWord ++ tailWord_3502218).sum := by decide
  have hdescent : baseEnd_3502218 < baseStart_3502218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502282 : List Nat := [3, 1, 2, 1, 3, 1, 4, 3, 1, 3]
def baseStart_3502282 : Nat := 118140960795 + 3502282 * 2 ^ 59
def prefixEnd_3502282 : Nat := 4983230072969 + 3 ^ 40 * 3502282 * 2
def baseEnd_3502282 : Nat := 1198902702393314359512203

theorem tailTrace_3502282 : CollatzResearch.WordTrace tailWord_3502282 prefixEnd_3502282 1198902702393314359512203 := by
  unfold tailWord_3502282
  simp only [CollatzResearch.WordTrace]
  refine ⟨31934679674459482747545275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85159145798558620660120733 31934679674459482747545275)
  ·
    refine ⟨47902019511689224121317913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31934679674459482747545275 47902019511689224121317913)
    ·
      refine ⟨35926514633766918090988435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47902019511689224121317913 35926514633766918090988435)
      ·
        refine ⟨53889771950650377136482653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35926514633766918090988435 53889771950650377136482653)
        ·
          refine ⟨20208664481493891426180995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53889771950650377136482653 20208664481493891426180995)
          ·
            refine ⟨30312996722240837139271493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20208664481493891426180995 30312996722240837139271493)
            ·
              refine ⟨5683686885420156963613405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30312996722240837139271493 5683686885420156963613405)
              ·
                refine ⟨2131382582032558861355027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5683686885420156963613405 2131382582032558861355027)
                ·
                  refine ⟨3197073873048838292032541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131382582032558861355027 3197073873048838292032541)
                  ·
                    refine ⟨1198902702393314359512203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3197073873048838292032541 1198902702393314359512203)
                    ·
                      rfl

theorem cell22_3502282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_3502282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502282 prefixEnd_3502282 := by exact prefixLift 3502282
  have htrace : WordTrace (prefixWord ++ tailWord_3502282) baseStart_3502282 baseEnd_3502282 := by
    simpa [prefixWord, tailWord_3502282, baseEnd_3502282] using wordTrace_append hprefix tailTrace_3502282
  have hstable : (prefixWord ++ tailWord_3502282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502282).length < 2 ^ (prefixWord ++ tailWord_3502282).sum := by decide
  have hdescent : baseEnd_3502282 < baseStart_3502282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502353 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_3502353 : Nat := 118140960795 + 3502353 * 2 ^ 59
def prefixEnd_3502353 : Nat := 4983230072969 + 3 ^ 40 * 3502353 * 2
def baseEnd_3502353 : Nat := 1198927007144293840986985

theorem tailTrace_3502353 : CollatzResearch.WordTrace tailWord_3502353 prefixEnd_3502353 1198927007144293840986985 := by
  unfold tailWord_3502353
  simp only [CollatzResearch.WordTrace]
  refine ⟨127741308280580710116015713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85160872187053806744010475 127741308280580710116015713)
  ·
    refine ⟨95805981210435532587011785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127741308280580710116015713 95805981210435532587011785)
    ·
      refine ⟨71854485907826649440258839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95805981210435532587011785 71854485907826649440258839)
      ·
        refine ⟨107781728861739974160388259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71854485907826649440258839 107781728861739974160388259)
        ·
          refine ⟨161672593292609961240582389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107781728861739974160388259 161672593292609961240582389)
          ·
            refine ⟨15156805621182183866304599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161672593292609961240582389 15156805621182183866304599)
            ·
              refine ⟨22735208431773275799456899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15156805621182183866304599 22735208431773275799456899)
              ·
                refine ⟨34102812647659913699185349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22735208431773275799456899 34102812647659913699185349)
                ·
                  refine ⟨6394277371436233818597253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34102812647659913699185349 6394277371436233818597253)
                  ·
                    refine ⟨1198927007144293840986985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6394277371436233818597253 1198927007144293840986985)
                    ·
                      rfl

theorem cell22_3502353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_3502353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502353 prefixEnd_3502353 := by exact prefixLift 3502353
  have htrace : WordTrace (prefixWord ++ tailWord_3502353) baseStart_3502353 baseEnd_3502353 := by
    simpa [prefixWord, tailWord_3502353, baseEnd_3502353] using wordTrace_append hprefix tailTrace_3502353
  have hstable : (prefixWord ++ tailWord_3502353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502353).length < 2 ^ (prefixWord ++ tailWord_3502353).sum := by decide
  have hdescent : baseEnd_3502353 < baseStart_3502353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502368 : List Nat := [2, 1, 1, 5, 2, 1, 1, 9]
def baseStart_3502368 : Nat := 118140960795 + 3502368 * 2 ^ 59
def prefixEnd_3502368 : Nat := 4983230072969 + 3 ^ 40 * 3502368 * 2
def baseEnd_3502368 : Nat := 133214682438982089095771

theorem tailTrace_3502368 : CollatzResearch.WordTrace tailWord_3502368 prefixEnd_3502368 133214682438982089095771 := by
  unfold tailWord_3502368
  simp only [CollatzResearch.WordTrace]
  refine ⟨63870927687763183838905879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85161236917017578451874505 63870927687763183838905879)
  ·
    refine ⟨95806391531644775758358819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63870927687763183838905879 95806391531644775758358819)
    ·
      refine ⟨143709587297467163637538229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95806391531644775758358819 143709587297467163637538229)
      ·
        refine ⟨13472773809137546591019209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143709587297467163637538229 13472773809137546591019209)
        ·
          refine ⟨10104580356853159943264407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13472773809137546591019209 10104580356853159943264407)
          ·
            refine ⟨15156870535279739914896611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104580356853159943264407 15156870535279739914896611)
            ·
              refine ⟨22735305802919609872344917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15156870535279739914896611 22735305802919609872344917)
              ·
                refine ⟨133214682438982089095771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22735305802919609872344917 133214682438982089095771)
                ·
                  rfl

theorem cell22_3502368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 9].length) (baseStart_3502368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502368 prefixEnd_3502368 := by exact prefixLift 3502368
  have htrace : WordTrace (prefixWord ++ tailWord_3502368) baseStart_3502368 baseEnd_3502368 := by
    simpa [prefixWord, tailWord_3502368, baseEnd_3502368] using wordTrace_append hprefix tailTrace_3502368
  have hstable : (prefixWord ++ tailWord_3502368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502368).length < 2 ^ (prefixWord ++ tailWord_3502368).sum := by decide
  have hdescent : baseEnd_3502368 < baseStart_3502368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502372 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_3502372 : Nat := 118140960795 + 3502372 * 2 ^ 59
def prefixEnd_3502372 : Nat := 4983230072969 + 3 ^ 40 * 3502372 * 2
def baseEnd_3502372 : Nat := 1198933511232584124761927

theorem tailTrace_3502372 : CollatzResearch.WordTrace tailWord_3502372 prefixEnd_3502372 1198933511232584124761927 := by
  unfold tailWord_3502372
  simp only [CollatzResearch.WordTrace]
  refine ⟨63871000633755938180478685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85161334178341250907304913 63871000633755938180478685)
  ·
    refine ⟨23951625237658476817679507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63871000633755938180478685 23951625237658476817679507)
    ·
      refine ⟨35927437856487715226519261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23951625237658476817679507 35927437856487715226519261)
      ·
        refine ⟨13472789196182893209944723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35927437856487715226519261 13472789196182893209944723)
        ·
          refine ⟨20209183794274339814917085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13472789196182893209944723 20209183794274339814917085)
          ·
            refine ⟨7578443922852877430593907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20209183794274339814917085 7578443922852877430593907)
            ·
              refine ⟨11367665884279316145890861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578443922852877430593907 11367665884279316145890861)
              ·
                refine ⟨4262874706604743554709073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11367665884279316145890861 4262874706604743554709073)
                ·
                  refine ⟨3197156029953557666031805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262874706604743554709073 3197156029953557666031805)
                  ·
                    refine ⟨1198933511232584124761927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3197156029953557666031805 1198933511232584124761927)
                    ·
                      rfl

theorem cell22_3502372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_3502372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502372 prefixEnd_3502372 := by exact prefixLift 3502372
  have htrace : WordTrace (prefixWord ++ tailWord_3502372) baseStart_3502372 baseEnd_3502372 := by
    simpa [prefixWord, tailWord_3502372, baseEnd_3502372] using wordTrace_append hprefix tailTrace_3502372
  have hstable : (prefixWord ++ tailWord_3502372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502372).length < 2 ^ (prefixWord ++ tailWord_3502372).sum := by decide
  have hdescent : baseEnd_3502372 < baseStart_3502372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502475 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 6]
def baseStart_3502475 : Nat := 118140960795 + 3502475 * 2 ^ 59
def prefixEnd_3502475 : Nat := 4983230072969 + 3 ^ 40 * 3502475 * 2
def baseEnd_3502475 : Nat := 399656256745842063145537

theorem tailTrace_3502475 : CollatzResearch.WordTrace tailWord_3502475 prefixEnd_3502475 399656256745842063145537 := by
  unfold tailWord_3502475
  simp only [CollatzResearch.WordTrace]
  refine ⟨127745757986138724951956879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85163838657425816634637919 127745757986138724951956879)
  ·
    refine ⟨191618636979208087427935319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127745757986138724951956879 191618636979208087427935319)
    ·
      refine ⟨287427955468812131141902979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191618636979208087427935319 287427955468812131141902979)
      ·
        refine ⟨431141933203218196712854469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287427955468812131141902979 431141933203218196712854469)
        ·
          refine ⟨80839112475603411883660213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431141933203218196712854469 80839112475603411883660213)
          ·
            refine ⟨7578666794587819864093145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80839112475603411883660213 7578666794587819864093145)
            ·
              refine ⟨5684000095940864898069859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7578666794587819864093145 5684000095940864898069859)
              ·
                refine ⟨8526000143911297347104789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5684000095940864898069859 8526000143911297347104789)
                ·
                  refine ⟨399656256745842063145537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8526000143911297347104789 399656256745842063145537)
                  ·
                    rfl

theorem cell22_3502475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 6].length) (baseStart_3502475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502475 prefixEnd_3502475 := by exact prefixLift 3502475
  have htrace : WordTrace (prefixWord ++ tailWord_3502475) baseStart_3502475 baseEnd_3502475 := by
    simpa [prefixWord, tailWord_3502475, baseEnd_3502475] using wordTrace_append hprefix tailTrace_3502475
  have hstable : (prefixWord ++ tailWord_3502475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502475).length < 2 ^ (prefixWord ++ tailWord_3502475).sum := by decide
  have hdescent : baseEnd_3502475 < baseStart_3502475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502494 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3502494 : Nat := 118140960795 + 3502494 * 2 ^ 59
def prefixEnd_3502494 : Nat := 4983230072969 + 3 ^ 40 * 3502494 * 2
def baseEnd_3502494 : Nat := 1198975274325816473211553

theorem tailTrace_3502494 : CollatzResearch.WordTrace tailWord_3502494 prefixEnd_3502494 1198975274325816473211553 := by
  unfold tailWord_3502494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15968306371633736399612317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85164300648713260797932357 15968306371633736399612317)
  ·
    refine ⟨5988114889362651149854619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15968306371633736399612317 5988114889362651149854619)
    ·
      refine ⟨8982172334043976724781929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5988114889362651149854619 8982172334043976724781929)
      ·
        refine ⟨6736629250532982543586447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8982172334043976724781929 6736629250532982543586447)
        ·
          refine ⟨10104943875799473815379671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736629250532982543586447 10104943875799473815379671)
          ·
            refine ⟨15157415813699210723069507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104943875799473815379671 15157415813699210723069507)
            ·
              refine ⟨22736123720548816084604261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15157415813699210723069507 22736123720548816084604261)
              ·
                refine ⟨4263023197602903015863299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22736123720548816084604261 4263023197602903015863299)
                ·
                  refine ⟨6394534796404354523794949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263023197602903015863299 6394534796404354523794949)
                  ·
                    refine ⟨1198975274325816473211553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6394534796404354523794949 1198975274325816473211553)
                    ·
                      rfl

theorem cell22_3502494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3502494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502494 prefixEnd_3502494 := by exact prefixLift 3502494
  have htrace : WordTrace (prefixWord ++ tailWord_3502494) baseStart_3502494 baseEnd_3502494 := by
    simpa [prefixWord, tailWord_3502494, baseEnd_3502494] using wordTrace_append hprefix tailTrace_3502494
  have hstable : (prefixWord ++ tailWord_3502494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502494).length < 2 ^ (prefixWord ++ tailWord_3502494).sum := by decide
  have hdescent : baseEnd_3502494 < baseStart_3502494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502595 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 5, 4]
def baseStart_3502595 : Nat := 118140960795 + 3502595 * 2 ^ 59
def prefixEnd_3502595 : Nat := 4983230072969 + 3 ^ 40 * 3502595 * 2
def baseEnd_3502595 : Nat := 1199009848689885876436243

theorem tailTrace_3502595 : CollatzResearch.WordTrace tailWord_3502595 prefixEnd_3502595 1199009848689885876436243 := by
  unfold tailWord_3502595
  simp only [CollatzResearch.WordTrace]
  refine ⟨127750134745703985446325239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85166756497135990297550159 127750134745703985446325239)
  ·
    refine ⟨191625202118555978169487859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127750134745703985446325239 191625202118555978169487859)
    ·
      refine ⟨287437803177833967254231789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191625202118555978169487859 287437803177833967254231789)
      ·
        refine ⟨107789176191687737720336921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287437803177833967254231789 107789176191687737720336921)
        ·
          refine ⟨80841882143765803290252691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107789176191687737720336921 80841882143765803290252691)
          ·
            refine ⟨121262823215648704935379037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80841882143765803290252691 121262823215648704935379037)
            ·
              refine ⟨45473558705868264350767139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121262823215648704935379037 45473558705868264350767139)
              ·
                refine ⟨68210338058802396526150709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45473558705868264350767139 68210338058802396526150709)
                ·
                  refine ⟨6394719193012724674326629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68210338058802396526150709 6394719193012724674326629)
                  ·
                    refine ⟨1199009848689885876436243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6394719193012724674326629 1199009848689885876436243)
                    ·
                      rfl

theorem cell22_3502595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 4].length) (baseStart_3502595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502595 prefixEnd_3502595 := by exact prefixLift 3502595
  have htrace : WordTrace (prefixWord ++ tailWord_3502595) baseStart_3502595 baseEnd_3502595 := by
    simpa [prefixWord, tailWord_3502595, baseEnd_3502595] using wordTrace_append hprefix tailTrace_3502595
  have hstable : (prefixWord ++ tailWord_3502595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502595).length < 2 ^ (prefixWord ++ tailWord_3502595).sum := by decide
  have hdescent : baseEnd_3502595 < baseStart_3502595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502629 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 1, 4]
def baseStart_3502629 : Nat := 118140960795 + 3502629 * 2 ^ 59
def prefixEnd_3502629 : Nat := 4983230072969 + 3 ^ 40 * 3502629 * 2
def baseEnd_3502629 : Nat := 1199021487584721121086139

theorem tailTrace_3502629 : CollatzResearch.WordTrace tailWord_3502629 prefixEnd_3502629 1199021487584721121086139 := by
  unfold tailWord_3502629
  simp only [CollatzResearch.WordTrace]
  refine ⟨127751374827580809253062941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85167583218387206168708627 127751374827580809253062941)
  ·
    refine ⟨47906765560342803469898603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127751374827580809253062941 47906765560342803469898603)
    ·
      refine ⟨71860148340514205204847905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47906765560342803469898603 71860148340514205204847905)
      ·
        refine ⟨53895111255385653903635929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71860148340514205204847905 53895111255385653903635929)
        ·
          refine ⟨40421333441539240427726947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53895111255385653903635929 40421333441539240427726947)
          ·
            refine ⟨60632000162308860641590421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40421333441539240427726947 60632000162308860641590421)
            ·
              refine ⟨2842125007608227842574551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60632000162308860641590421 2842125007608227842574551)
              ·
                refine ⟨4263187511412341763861827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842125007608227842574551 4263187511412341763861827)
                ·
                  refine ⟨6394781267118512645792741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263187511412341763861827 6394781267118512645792741)
                  ·
                    refine ⟨1199021487584721121086139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6394781267118512645792741 1199021487584721121086139)
                    ·
                      rfl

theorem cell22_3502629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_3502629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502629 prefixEnd_3502629 := by exact prefixLift 3502629
  have htrace : WordTrace (prefixWord ++ tailWord_3502629) baseStart_3502629 baseEnd_3502629 := by
    simpa [prefixWord, tailWord_3502629, baseEnd_3502629] using wordTrace_append hprefix tailTrace_3502629
  have hstable : (prefixWord ++ tailWord_3502629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502629).length < 2 ^ (prefixWord ++ tailWord_3502629).sum := by decide
  have hdescent : baseEnd_3502629 < baseStart_3502629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502655 : List Nat := [1, 1, 2, 2, 3, 2, 2, 9]
def baseStart_3502655 : Nat := 118140960795 + 3502655 * 2 ^ 59
def prefixEnd_3502655 : Nat := 4983230072969 + 3 ^ 40 * 3502655 * 2
def baseEnd_3502655 : Nat := 133225598657340635548451

theorem tailTrace_3502655 : CollatzResearch.WordTrace tailWord_3502655 prefixEnd_3502655 133225598657340635548451 := by
  unfold tailWord_3502655
  simp only [CollatzResearch.WordTrace]
  refine ⟨127752323125486615693509419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85168215416991077129006279 127752323125486615693509419)
  ·
    refine ⟨191628484688229923540264129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127752323125486615693509419 191628484688229923540264129)
    ·
      refine ⟨143721363516172442655198097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191628484688229923540264129 143721363516172442655198097)
      ·
        refine ⟨107791022637129331991398573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143721363516172442655198097 107791022637129331991398573)
        ·
          refine ⟨40421633488923499496774465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107791022637129331991398573 40421633488923499496774465)
          ·
            refine ⟨30316225116692624622580849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40421633488923499496774465 30316225116692624622580849)
            ·
              refine ⟨22737168837519468466935637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30316225116692624622580849 22737168837519468466935637)
              ·
                refine ⟨133225598657340635548451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22737168837519468466935637 133225598657340635548451)
                ·
                  rfl

theorem cell22_3502655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 9].length) (baseStart_3502655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502655 prefixEnd_3502655 := by exact prefixLift 3502655
  have htrace : WordTrace (prefixWord ++ tailWord_3502655) baseStart_3502655 baseEnd_3502655 := by
    simpa [prefixWord, tailWord_3502655, baseEnd_3502655] using wordTrace_append hprefix tailTrace_3502655
  have hstable : (prefixWord ++ tailWord_3502655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502655).length < 2 ^ (prefixWord ++ tailWord_3502655).sum := by decide
  have hdescent : baseEnd_3502655 < baseStart_3502655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502657 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3502657 : Nat := 118140960795 + 3502657 * 2 ^ 59
def prefixEnd_3502657 : Nat := 4983230072969 + 3 ^ 40 * 3502657 * 2
def baseEnd_3502657 : Nat := 1199031072556938381386053

theorem tailTrace_3502657 : CollatzResearch.WordTrace tailWord_3502657 prefixEnd_3502657 1199031072556938381386053 := by
  unfold tailWord_3502657
  simp only [CollatzResearch.WordTrace]
  refine ⟨127752396071479370035082225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85168264047652913356721483 127752396071479370035082225)
  ·
    refine ⟨95814297053609527526311669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127752396071479370035082225 95814297053609527526311669)
    ·
      refine ⟨8982590348775893205591719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95814297053609527526311669 8982590348775893205591719)
      ·
        refine ⟨13473885523163839808387579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8982590348775893205591719 13473885523163839808387579)
        ·
          refine ⟨20210828284745759712581369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13473885523163839808387579 20210828284745759712581369)
          ·
            refine ⟨15158121213559319784436027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20210828284745759712581369 15158121213559319784436027)
            ·
              refine ⟨22737181820338979676654041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15158121213559319784436027 22737181820338979676654041)
              ·
                refine ⟨17052886365254234757490531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22737181820338979676654041 17052886365254234757490531)
                ·
                  refine ⟨25579329547881352136235797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17052886365254234757490531 25579329547881352136235797)
                  ·
                    refine ⟨1199031072556938381386053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25579329547881352136235797 1199031072556938381386053)
                    ·
                      rfl

theorem cell22_3502657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3502657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502657 prefixEnd_3502657 := by exact prefixLift 3502657
  have htrace : WordTrace (prefixWord ++ tailWord_3502657) baseStart_3502657 baseEnd_3502657 := by
    simpa [prefixWord, tailWord_3502657, baseEnd_3502657] using wordTrace_append hprefix tailTrace_3502657
  have hstable : (prefixWord ++ tailWord_3502657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502657).length < 2 ^ (prefixWord ++ tailWord_3502657).sum := by decide
  have hdescent : baseEnd_3502657 < baseStart_3502657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502687 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 5, 3]
def baseStart_3502687 : Nat := 118140960795 + 3502687 * 2 ^ 59
def prefixEnd_3502687 : Nat := 4983230072969 + 3 ^ 40 * 3502687 * 2
def baseEnd_3502687 : Nat := 1199041342170028303135961

theorem tailTrace_3502687 : CollatzResearch.WordTrace tailWord_3502687 prefixEnd_3502687 1199041342170028303135961 := by
  unfold tailWord_3502687
  simp only [CollatzResearch.WordTrace]
  refine ⟨127753490261370685158674315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85168993507580456772449543 127753490261370685158674315)
  ·
    refine ⟨191630235392056027738011473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127753490261370685158674315 191630235392056027738011473)
    ·
      refine ⟨143722676544042020803508605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191630235392056027738011473 143722676544042020803508605)
      ·
        refine ⟨53896003704015757801315727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143722676544042020803508605 53896003704015757801315727)
        ·
          refine ⟨80844005556023636701973591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53896003704015757801315727 80844005556023636701973591)
          ·
            refine ⟨121266008334035455052960387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80844005556023636701973591 121266008334035455052960387)
            ·
              refine ⟨181899012501053182579440581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121266008334035455052960387 181899012501053182579440581)
              ·
                refine ⟨34106064843947471733645109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181899012501053182579440581 34106064843947471733645109)
                ·
                  refine ⟨3197443579120075475029229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34106064843947471733645109 3197443579120075475029229)
                  ·
                    refine ⟨1199041342170028303135961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3197443579120075475029229 1199041342170028303135961)
                    ·
                      rfl

theorem cell22_3502687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_3502687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502687 prefixEnd_3502687 := by exact prefixLift 3502687
  have htrace : WordTrace (prefixWord ++ tailWord_3502687) baseStart_3502687 baseEnd_3502687 := by
    simpa [prefixWord, tailWord_3502687, baseEnd_3502687] using wordTrace_append hprefix tailTrace_3502687
  have hstable : (prefixWord ++ tailWord_3502687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502687).length < 2 ^ (prefixWord ++ tailWord_3502687).sum := by decide
  have hdescent : baseEnd_3502687 < baseStart_3502687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502710 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_3502710 : Nat := 118140960795 + 3502710 * 2 ^ 59
def prefixEnd_3502710 : Nat := 4983230072969 + 3 ^ 40 * 3502710 * 2
def baseEnd_3502710 : Nat := 1199049215540063909810891

theorem tailTrace_3502710 : CollatzResearch.WordTrace tailWord_3502710 prefixEnd_3502710 1199049215540063909810891 := by
  unfold tailWord_3502710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984645571267960005422599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85169552760191573391174389 7984645571267960005422599)
  ·
    refine ⟨11976968356901940008133899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7984645571267960005422599 11976968356901940008133899)
    ·
      refine ⟨17965452535352910012200849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11976968356901940008133899 17965452535352910012200849)
      ·
        refine ⟨13474089401514682509150637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17965452535352910012200849 13474089401514682509150637)
        ·
          refine ⟨5052783525568005940931489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13474089401514682509150637 5052783525568005940931489)
          ·
            refine ⟨3789587644176004455698617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5052783525568005940931489 3789587644176004455698617)
            ·
              refine ⟨2842190733132003341773963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3789587644176004455698617 2842190733132003341773963)
              ·
                refine ⟨4263286099698005012660945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842190733132003341773963 4263286099698005012660945)
                ·
                  refine ⟨3197464574773503759495709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4263286099698005012660945 3197464574773503759495709)
                  ·
                    refine ⟨1199049215540063909810891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3197464574773503759495709 1199049215540063909810891)
                    ·
                      rfl

theorem cell22_3502710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_3502710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502710 prefixEnd_3502710 := by exact prefixLift 3502710
  have htrace : WordTrace (prefixWord ++ tailWord_3502710) baseStart_3502710 baseEnd_3502710 := by
    simpa [prefixWord, tailWord_3502710, baseEnd_3502710] using wordTrace_append hprefix tailTrace_3502710
  have hstable : (prefixWord ++ tailWord_3502710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502710).length < 2 ^ (prefixWord ++ tailWord_3502710).sum := by decide
  have hdescent : baseEnd_3502710 < baseStart_3502710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502766 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3502766 : Nat := 118140960795 + 3502766 * 2 ^ 59
def prefixEnd_3502766 : Nat := 4983230072969 + 3 ^ 40 * 3502766 * 2
def baseEnd_3502766 : Nat := 1199068385484498430410719

theorem tailTrace_3502766 : CollatzResearch.WordTrace tailWord_3502766 prefixEnd_3502766 1199068385484498430410719 := by
  unfold tailWord_3502766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15969546453510560206350019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85170914418722987767200101 15969546453510560206350019)
  ·
    refine ⟨23954319680265840309525029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15969546453510560206350019 23954319680265840309525029)
    ·
      refine ⟨4491434940049845058035943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23954319680265840309525029 4491434940049845058035943)
      ·
        refine ⟨6737152410074767587053915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4491434940049845058035943 6737152410074767587053915)
        ·
          refine ⟨10105728615112151380580873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737152410074767587053915 10105728615112151380580873)
          ·
            refine ⟨7579296461334113535435655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10105728615112151380580873 7579296461334113535435655)
            ·
              refine ⟨11368944692001170303153483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7579296461334113535435655 11368944692001170303153483)
              ·
                refine ⟨17053417038001755454730225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11368944692001170303153483 17053417038001755454730225)
                ·
                  refine ⟨12790062778501316591047669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17053417038001755454730225 12790062778501316591047669)
                  ·
                    refine ⟨1199068385484498430410719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12790062778501316591047669 1199068385484498430410719)
                    ·
                      rfl

theorem cell22_3502766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3502766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502766 prefixEnd_3502766 := by exact prefixLift 3502766
  have htrace : WordTrace (prefixWord ++ tailWord_3502766) baseStart_3502766 baseEnd_3502766 := by
    simpa [prefixWord, tailWord_3502766, baseEnd_3502766] using wordTrace_append hprefix tailTrace_3502766
  have hstable : (prefixWord ++ tailWord_3502766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502766).length < 2 ^ (prefixWord ++ tailWord_3502766).sum := by decide
  have hdescent : baseEnd_3502766 < baseStart_3502766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502794 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_3502794 : Nat := 118140960795 + 3502794 * 2 ^ 59
def prefixEnd_3502794 : Nat := 4983230072969 + 3 ^ 40 * 3502794 * 2
def baseEnd_3502794 : Nat := 1199077970456715690710633

theorem tailTrace_3502794 : CollatzResearch.WordTrace tailWord_3502794 prefixEnd_3502794 1199077970456715690710633 := by
  unfold tailWord_3502794
  simp only [CollatzResearch.WordTrace]
  refine ⟨31939348217995760608204859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85171595247988694955212957 31939348217995760608204859)
  ·
    refine ⟨47909022326993640912307289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31939348217995760608204859 47909022326993640912307289)
    ·
      refine ⟨35931766745245230684230467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47909022326993640912307289 35931766745245230684230467)
      ·
        refine ⟨53897650117867846026345701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35931766745245230684230467 53897650117867846026345701)
        ·
          refine ⟨10105809397100221129939819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53897650117867846026345701 10105809397100221129939819)
          ·
            refine ⟨15158714095650331694909729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10105809397100221129939819 15158714095650331694909729)
            ·
              refine ⟨11369035571737748771182297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15158714095650331694909729 11369035571737748771182297)
              ·
                refine ⟨8526776678803311578386723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11369035571737748771182297 8526776678803311578386723)
                ·
                  refine ⟨12790165018204967367580085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8526776678803311578386723 12790165018204967367580085)
                  ·
                    refine ⟨1199077970456715690710633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12790165018204967367580085 1199077970456715690710633)
                    ·
                      rfl

theorem cell22_3502794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_3502794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502794 prefixEnd_3502794 := by exact prefixLift 3502794
  have htrace : WordTrace (prefixWord ++ tailWord_3502794) baseStart_3502794 baseEnd_3502794 := by
    simpa [prefixWord, tailWord_3502794, baseEnd_3502794] using wordTrace_append hprefix tailTrace_3502794
  have hstable : (prefixWord ++ tailWord_3502794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502794).length < 2 ^ (prefixWord ++ tailWord_3502794).sum := by decide
  have hdescent : baseEnd_3502794 < baseStart_3502794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502796 : List Nat := [2, 2, 1, 5, 1, 1, 1, 5, 4]
def baseStart_3502796 : Nat := 118140960795 + 3502796 * 2 ^ 59
def prefixEnd_3502796 : Nat := 4983230072969 + 3 ^ 40 * 3502796 * 2
def baseEnd_3502796 : Nat := 399692885032529450720209

theorem tailTrace_3502796 : CollatzResearch.WordTrace tailWord_3502796 prefixEnd_3502796 399692885032529450720209 := by
  unfold tailWord_3502796
  simp only [CollatzResearch.WordTrace]
  refine ⟨63878732908987898387196121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85171643878650531182928161 63878732908987898387196121)
  ·
    refine ⟨47909049681740923790397091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63878732908987898387196121 47909049681740923790397091)
    ·
      refine ⟨71863574522611385685595637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47909049681740923790397091 71863574522611385685595637)
      ·
        refine ⟨6737210111494817408024591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71863574522611385685595637 6737210111494817408024591)
        ·
          refine ⟨10105815167242226112036887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737210111494817408024591 10105815167242226112036887)
          ·
            refine ⟨15158722750863339168055331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10105815167242226112036887 15158722750863339168055331)
            ·
              refine ⟨22738084126295008752082997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15158722750863339168055331 22738084126295008752082997)
              ·
                refine ⟨2131695386840157070507781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22738084126295008752082997 2131695386840157070507781)
                ·
                  refine ⟨399692885032529450720209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2131695386840157070507781 399692885032529450720209)
                  ·
                    rfl

theorem cell22_3502796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_3502796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502796 prefixEnd_3502796 := by exact prefixLift 3502796
  have htrace : WordTrace (prefixWord ++ tailWord_3502796) baseStart_3502796 baseEnd_3502796 := by
    simpa [prefixWord, tailWord_3502796, baseEnd_3502796] using wordTrace_append hprefix tailTrace_3502796
  have hstable : (prefixWord ++ tailWord_3502796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502796).length < 2 ^ (prefixWord ++ tailWord_3502796).sum := by decide
  have hdescent : baseEnd_3502796 < baseStart_3502796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502798 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_3502798 : Nat := 118140960795 + 3502798 * 2 ^ 59
def prefixEnd_3502798 : Nat := 4983230072969 + 3 ^ 40 * 3502798 * 2
def baseEnd_3502798 : Nat := 1199079339738461013610621

theorem tailTrace_3502798 : CollatzResearch.WordTrace tailWord_3502798 prefixEnd_3502798 1199079339738461013610621 := by
  unfold tailWord_3502798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15969692345496068889495631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85171692509312367410643365 15969692345496068889495631)
  ·
    refine ⟨23954538518244103334243447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15969692345496068889495631 23954538518244103334243447)
    ·
      refine ⟨35931807777366155001365171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23954538518244103334243447 35931807777366155001365171)
      ·
        refine ⟨53897711666049232502047757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35931807777366155001365171 53897711666049232502047757)
        ·
          refine ⟨20211641874768462188267909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53897711666049232502047757 20211641874768462188267909)
          ·
            refine ⟨3789682851519086660300233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20211641874768462188267909 3789682851519086660300233)
            ·
              refine ⟨2842262138639314995225175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3789682851519086660300233 2842262138639314995225175)
              ·
                refine ⟨4263393207958972492837763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842262138639314995225175 4263393207958972492837763)
                ·
                  refine ⟨6395089811938458739256645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263393207958972492837763 6395089811938458739256645)
                  ·
                    refine ⟨1199079339738461013610621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6395089811938458739256645 1199079339738461013610621)
                    ·
                      rfl

theorem cell22_3502798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_3502798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502798 prefixEnd_3502798 := by exact prefixLift 3502798
  have htrace : WordTrace (prefixWord ++ tailWord_3502798) baseStart_3502798 baseEnd_3502798 := by
    simpa [prefixWord, tailWord_3502798, baseEnd_3502798] using wordTrace_append hprefix tailTrace_3502798
  have hstable : (prefixWord ++ tailWord_3502798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502798).length < 2 ^ (prefixWord ++ tailWord_3502798).sum := by decide
  have hdescent : baseEnd_3502798 < baseStart_3502798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502807 : List Nat := [1, 1, 3, 2, 1, 5, 9]
def baseStart_3502807 : Nat := 118140960795 + 3502807 * 2 ^ 59
def prefixEnd_3502807 : Nat := 4983230072969 + 3 ^ 40 * 3502807 * 2
def baseEnd_3502807 : Nat := 44410460023051407042059

theorem tailTrace_3502807 : CollatzResearch.WordTrace tailWord_3502807 prefixEnd_3502807 44410460023051407042059 := by
  unfold tailWord_3502807
  simp only [CollatzResearch.WordTrace]
  refine ⟨127757867020935945653042675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85171911347290630435361783 127757867020935945653042675)
  ·
    refine ⟨191636800531403918479564013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127757867020935945653042675 191636800531403918479564013)
    ·
      refine ⟨71863800199276469429836505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191636800531403918479564013 71863800199276469429836505)
      ·
        refine ⟨53897850149457352072377379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71863800199276469429836505 53897850149457352072377379)
        ·
          refine ⟨80846775224186028108566069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53897850149457352072377379 80846775224186028108566069)
          ·
            refine ⟨7579385177267440135178069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80846775224186028108566069 7579385177267440135178069)
            ·
              refine ⟨44410460023051407042059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7579385177267440135178069 44410460023051407042059)
              ·
                rfl

theorem cell22_3502807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 9].length) (baseStart_3502807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502807 prefixEnd_3502807 := by exact prefixLift 3502807
  have htrace : WordTrace (prefixWord ++ tailWord_3502807) baseStart_3502807 baseEnd_3502807 := by
    simpa [prefixWord, tailWord_3502807, baseEnd_3502807] using wordTrace_append hprefix tailTrace_3502807
  have hstable : (prefixWord ++ tailWord_3502807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502807).length < 2 ^ (prefixWord ++ tailWord_3502807).sum := by decide
  have hdescent : baseEnd_3502807 < baseStart_3502807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502869 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 5]
def baseStart_3502869 : Nat := 118140960795 + 3502869 * 2 ^ 59
def prefixEnd_3502869 : Nat := 4983230072969 + 3 ^ 40 * 3502869 * 2
def baseEnd_3502869 : Nat := 399701214829813498361801

theorem tailTrace_3502869 : CollatzResearch.WordTrace tailWord_3502869 prefixEnd_3502869 399701214829813498361801 := by
  unfold tailWord_3502869
  simp only [CollatzResearch.WordTrace]
  refine ⟨127760128346711330241799661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85173418897807553494533107 127760128346711330241799661)
  ·
    refine ⟨47910048130016748840674873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127760128346711330241799661 47910048130016748840674873)
    ·
      refine ⟨35932536097512561630506155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47910048130016748840674873 35932536097512561630506155)
      ·
        refine ⟨53898804146268842445759233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35932536097512561630506155 53898804146268842445759233)
        ·
          refine ⟨40424103109701631834319425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53898804146268842445759233 40424103109701631834319425)
          ·
            refine ⟨30318077332276223875739569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40424103109701631834319425 30318077332276223875739569)
            ·
              refine ⟨22738557999207167906804677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30318077332276223875739569 22738557999207167906804677)
              ·
                refine ⟨4263479624851343982525877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22738557999207167906804677 4263479624851343982525877)
                ·
                  refine ⟨399701214829813498361801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4263479624851343982525877 399701214829813498361801)
                  ·
                    rfl

theorem cell22_3502869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_3502869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502869 prefixEnd_3502869 := by exact prefixLift 3502869
  have htrace : WordTrace (prefixWord ++ tailWord_3502869) baseStart_3502869 baseEnd_3502869 := by
    simpa [prefixWord, tailWord_3502869, baseEnd_3502869] using wordTrace_append hprefix tailTrace_3502869
  have hstable : (prefixWord ++ tailWord_3502869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502869).length < 2 ^ (prefixWord ++ tailWord_3502869).sum := by decide
  have hdescent : baseEnd_3502869 < baseStart_3502869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502944 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_3502944 : Nat := 118140960795 + 3502944 * 2 ^ 59
def prefixEnd_3502944 : Nat := 4983230072969 + 3 ^ 40 * 3502944 * 2
def baseEnd_3502944 : Nat := 1199129318522165299460173

theorem tailTrace_3502944 : CollatzResearch.WordTrace tailWord_3502944 prefixEnd_3502944 1199129318522165299460173 := by
  unfold tailWord_3502944
  simp only [CollatzResearch.WordTrace]
  refine ⟨63881431910719809025389943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85175242547626412033853257 63881431910719809025389943)
  ·
    refine ⟨95822147866079713538084915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63881431910719809025389943 95822147866079713538084915)
    ·
      refine ⟨143733221799119570307127373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95822147866079713538084915 143733221799119570307127373)
      ·
        refine ⟨53899958174669838865172765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143733221799119570307127373 53899958174669838865172765)
        ·
          refine ⟨20212484315501189574439787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53899958174669838865172765 20212484315501189574439787)
          ·
            refine ⟨30318726473251784361659681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20212484315501189574439787 30318726473251784361659681)
            ·
              refine ⟨22739044854938838271244761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30318726473251784361659681 22739044854938838271244761)
              ·
                refine ⟨17054283641204128703433571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22739044854938838271244761 17054283641204128703433571)
                ·
                  refine ⟨25581425461806193055150357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17054283641204128703433571 25581425461806193055150357)
                  ·
                    refine ⟨1199129318522165299460173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25581425461806193055150357 1199129318522165299460173)
                    ·
                      rfl

theorem cell22_3502944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_3502944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502944 prefixEnd_3502944 := by exact prefixLift 3502944
  have htrace : WordTrace (prefixWord ++ tailWord_3502944) baseStart_3502944 baseEnd_3502944 := by
    simpa [prefixWord, tailWord_3502944, baseEnd_3502944] using wordTrace_append hprefix tailTrace_3502944
  have hstable : (prefixWord ++ tailWord_3502944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502944).length < 2 ^ (prefixWord ++ tailWord_3502944).sum := by decide
  have hdescent : baseEnd_3502944 < baseStart_3502944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502961 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_3502961 : Nat := 118140960795 + 3502961 * 2 ^ 59
def prefixEnd_3502961 : Nat := 4983230072969 + 3 ^ 40 * 3502961 * 2
def baseEnd_3502961 : Nat := 1199135137969582921785121

theorem tailTrace_3502961 : CollatzResearch.WordTrace tailWord_3502961 prefixEnd_3502961 1199135137969582921785121 := by
  unfold tailWord_3502961
  simp only [CollatzResearch.WordTrace]
  refine ⟨127763483862378029954148737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85175655908252019969432491 127763483862378029954148737)
  ·
    refine ⟨95822612896783522465611553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127763483862378029954148737 95822612896783522465611553)
    ·
      refine ⟨71866959672587641849208665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95822612896783522465611553 71866959672587641849208665)
      ·
        refine ⟨53900219754440731386906499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71866959672587641849208665 53900219754440731386906499)
        ·
          refine ⟨80850329631661097080359749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53900219754440731386906499 80850329631661097080359749)
          ·
            refine ⟨15159436805936455702567453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80850329631661097080359749 15159436805936455702567453)
            ·
              refine ⟨5684788802226170888462795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15159436805936455702567453 5684788802226170888462795)
              ·
                refine ⟨8527183203339256332694193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5684788802226170888462795 8527183203339256332694193)
                ·
                  refine ⟨6395387402504442249520645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8527183203339256332694193 6395387402504442249520645)
                  ·
                    refine ⟨1199135137969582921785121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6395387402504442249520645 1199135137969582921785121)
                    ·
                      rfl

theorem cell22_3502961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_3502961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3502961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3502961 prefixEnd_3502961 := by exact prefixLift 3502961
  have htrace : WordTrace (prefixWord ++ tailWord_3502961) baseStart_3502961 baseEnd_3502961 := by
    simpa [prefixWord, tailWord_3502961, baseEnd_3502961] using wordTrace_append hprefix tailTrace_3502961
  have hstable : (prefixWord ++ tailWord_3502961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502961).length < 2 ^ (prefixWord ++ tailWord_3502961).sum := by decide
  have hdescent : baseEnd_3502961 < baseStart_3502961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503093 : List Nat := [1, 3, 5, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3503093 : Nat := 118140960795 + 3503093 * 2 ^ 59
def prefixEnd_3503093 : Nat := 4983230072969 + 3 ^ 40 * 3503093 * 2
def baseEnd_3503093 : Nat := 1199180324267178577484717

theorem tailTrace_3503093 : CollatzResearch.WordTrace tailWord_3503093 prefixEnd_3503093 1199180324267178577484717 := by
  unfold tailWord_3503093
  simp only [CollatzResearch.WordTrace]
  refine ⟨127768298297899816497953933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85178865531933210998635955 127768298297899816497953933)
  ·
    refine ⟨47913111861712431186732725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127768298297899816497953933 47913111861712431186732725)
    ·
      refine ⟨4491854237035540423756193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47913111861712431186732725 4491854237035540423756193)
      ·
        refine ⟨3368890677776655317817145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4491854237035540423756193 3368890677776655317817145)
        ·
          refine ⟨2526668008332491488362859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3368890677776655317817145 2526668008332491488362859)
          ·
            refine ⟨3790002012498737232544289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526668008332491488362859 3790002012498737232544289)
            ·
              refine ⟨2842501509374052924408217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3790002012498737232544289 2842501509374052924408217)
              ·
                refine ⟨2131876132030539693306163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2842501509374052924408217 2131876132030539693306163)
                ·
                  refine ⟨3197814198045809539959245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131876132030539693306163 3197814198045809539959245)
                  ·
                    refine ⟨1199180324267178577484717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3197814198045809539959245 1199180324267178577484717)
                    ·
                      rfl

theorem cell22_3503093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3503093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503093 prefixEnd_3503093 := by exact prefixLift 3503093
  have htrace : WordTrace (prefixWord ++ tailWord_3503093) baseStart_3503093 baseEnd_3503093 := by
    simpa [prefixWord, tailWord_3503093, baseEnd_3503093] using wordTrace_append hprefix tailTrace_3503093
  have hstable : (prefixWord ++ tailWord_3503093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503093).length < 2 ^ (prefixWord ++ tailWord_3503093).sum := by decide
  have hdescent : baseEnd_3503093 < baseStart_3503093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503100 : List Nat := [2, 2, 2, 1, 2, 3, 4, 2, 4]
def baseStart_3503100 : Nat := 118140960795 + 3503100 * 2 ^ 59
def prefixEnd_3503100 : Nat := 4983230072969 + 3 ^ 40 * 3503100 * 2
def baseEnd_3503100 : Nat := 399727573503410964186565

theorem tailTrace_3503100 : CollatzResearch.WordTrace tailWord_3503100 prefixEnd_3503100 399727573503410964186565 := by
  unfold tailWord_3503100
  simp only [CollatzResearch.WordTrace]
  refine ⟨63884276804437228346729377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85179035739249637795639169 63884276804437228346729377)
  ·
    refine ⟨47913207603327921260047033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63884276804437228346729377 47913207603327921260047033)
    ·
      refine ⟨35934905702495940945035275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47913207603327921260047033 35934905702495940945035275)
      ·
        refine ⟨53902358553743911417552913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35934905702495940945035275 53902358553743911417552913)
        ·
          refine ⟨40426768915307933563164685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53902358553743911417552913 40426768915307933563164685)
          ·
            refine ⟨15160038343240475086186757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40426768915307933563164685 15160038343240475086186757)
            ·
              refine ⟨2842507189357589078660017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15160038343240475086186757 2842507189357589078660017)
              ·
                refine ⟨2131880392018191808995013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2842507189357589078660017 2131880392018191808995013)
                ·
                  refine ⟨399727573503410964186565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2131880392018191808995013 399727573503410964186565)
                  ·
                    rfl

theorem cell22_3503100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_3503100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503100 prefixEnd_3503100 := by exact prefixLift 3503100
  have htrace : WordTrace (prefixWord ++ tailWord_3503100) baseStart_3503100 baseEnd_3503100 := by
    simpa [prefixWord, tailWord_3503100, baseEnd_3503100] using wordTrace_append hprefix tailTrace_3503100
  have hstable : (prefixWord ++ tailWord_3503100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503100).length < 2 ^ (prefixWord ++ tailWord_3503100).sum := by decide
  have hdescent : baseEnd_3503100 < baseStart_3503100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503128 : List Nat := [2, 1, 2, 3, 2, 3, 3, 6]
def baseStart_3503128 : Nat := 118140960795 + 3503128 * 2 ^ 59
def prefixEnd_3503128 : Nat := 4983230072969 + 3 ^ 40 * 3503128 * 2
def baseEnd_3503128 : Nat := 133243589498050016984401

theorem tailTrace_3503128 : CollatzResearch.WordTrace tailWord_3503128 prefixEnd_3503128 133243589498050016984401 := by
  unfold tailWord_3503128
  simp only [CollatzResearch.WordTrace]
  refine ⟨63884787426386508737739019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85179716568515344983652025 63884787426386508737739019)
  ·
    refine ⟨95827181139579763106608529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63884787426386508737739019 95827181139579763106608529)
    ·
      refine ⟨71870385854684822329956397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95827181139579763106608529 71870385854684822329956397)
      ·
        refine ⟨26951394695506808373733649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71870385854684822329956397 26951394695506808373733649)
        ·
          refine ⟨20213546021630106280300237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26951394695506808373733649 20213546021630106280300237)
          ·
            refine ⟨7580079758111289855112589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20213546021630106280300237 7580079758111289855112589)
            ·
              refine ⟨2842529909291733695667221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7580079758111289855112589 2842529909291733695667221)
              ·
                refine ⟨133243589498050016984401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2842529909291733695667221 133243589498050016984401)
                ·
                  rfl

theorem cell22_3503128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 6].length) (baseStart_3503128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503128 prefixEnd_3503128 := by exact prefixLift 3503128
  have htrace : WordTrace (prefixWord ++ tailWord_3503128) baseStart_3503128 baseEnd_3503128 := by
    simpa [prefixWord, tailWord_3503128, baseEnd_3503128] using wordTrace_append hprefix tailTrace_3503128
  have hstable : (prefixWord ++ tailWord_3503128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503128).length < 2 ^ (prefixWord ++ tailWord_3503128).sum := by decide
  have hdescent : baseEnd_3503128 < baseStart_3503128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503160 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 3, 3]
def baseStart_3503160 : Nat := 118140960795 + 3503160 * 2 ^ 59
def prefixEnd_3503160 : Nat := 4983230072969 + 3 ^ 40 * 3503160 * 2
def baseEnd_3503160 : Nat := 1199203259736412736059511

theorem tailTrace_3503160 : CollatzResearch.WordTrace tailWord_3503160 prefixEnd_3503160 1199203259736412736059511 := by
  unfold tailWord_3503160
  simp only [CollatzResearch.WordTrace]
  refine ⟨63885370994328543470321467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85180494659104724627095289 63885370994328543470321467)
  ·
    refine ⟨95828056491492815205482201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63885370994328543470321467 95828056491492815205482201)
    ·
      refine ⟨71871042368619611404111651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95828056491492815205482201 71871042368619611404111651)
      ·
        refine ⟨107806563552929417106167477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71871042368619611404111651 107806563552929417106167477)
        ·
          refine ⟨10106865333087132853703201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107806563552929417106167477 10106865333087132853703201)
          ·
            refine ⟨7580148999815349640277401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10106865333087132853703201 7580148999815349640277401)
            ·
              refine ⟨5685111749861512230208051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7580148999815349640277401 5685111749861512230208051)
              ·
                refine ⟨8527667624792268345312077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5685111749861512230208051 8527667624792268345312077)
                ·
                  refine ⟨3197875359297100629492029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8527667624792268345312077 3197875359297100629492029)
                  ·
                    refine ⟨1199203259736412736059511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3197875359297100629492029 1199203259736412736059511)
                    ·
                      rfl

theorem cell22_3503160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_3503160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503160 prefixEnd_3503160 := by exact prefixLift 3503160
  have htrace : WordTrace (prefixWord ++ tailWord_3503160) baseStart_3503160 baseEnd_3503160 := by
    simpa [prefixWord, tailWord_3503160, baseEnd_3503160] using wordTrace_append hprefix tailTrace_3503160
  have hstable : (prefixWord ++ tailWord_3503160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503160).length < 2 ^ (prefixWord ++ tailWord_3503160).sum := by decide
  have hdescent : baseEnd_3503160 < baseStart_3503160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503171 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 2, 5]
def baseStart_3503171 : Nat := 118140960795 + 3503171 * 2 ^ 59
def prefixEnd_3503171 : Nat := 4983230072969 + 3 ^ 40 * 3503171 * 2
def baseEnd_3503171 : Nat := 1199207025261212374034477

theorem tailTrace_3503171 : CollatzResearch.WordTrace tailWord_3503171 prefixEnd_3503171 1199207025261212374034477 := by
  unfold tailWord_3503171
  simp only [CollatzResearch.WordTrace]
  refine ⟨127771143191617235819293367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85180762127744823879528911 127771143191617235819293367)
  ·
    refine ⟨191656714787425853728940051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127771143191617235819293367 191656714787425853728940051)
    ·
      refine ⟨287485072181138780593410077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191656714787425853728940051 287485072181138780593410077)
      ·
        refine ⟨107806902067927042722528779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287485072181138780593410077 107806902067927042722528779)
        ·
          refine ⟨161710353101890564083793169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107806902067927042722528779 161710353101890564083793169)
          ·
            refine ⟨121282764826417923062844877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161710353101890564083793169 121282764826417923062844877)
            ·
              refine ⟨45481036809906721148566829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121282764826417923062844877 45481036809906721148566829)
              ·
                refine ⟨17055388803715020430712561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45481036809906721148566829 17055388803715020430712561)
                ·
                  refine ⟨12791541602786265323034421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17055388803715020430712561 12791541602786265323034421)
                  ·
                    refine ⟨1199207025261212374034477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12791541602786265323034421 1199207025261212374034477)
                    ·
                      rfl

theorem cell22_3503171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_3503171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503171 prefixEnd_3503171 := by exact prefixLift 3503171
  have htrace : WordTrace (prefixWord ++ tailWord_3503171) baseStart_3503171 baseEnd_3503171 := by
    simpa [prefixWord, tailWord_3503171, baseEnd_3503171] using wordTrace_append hprefix tailTrace_3503171
  have hstable : (prefixWord ++ tailWord_3503171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503171).length < 2 ^ (prefixWord ++ tailWord_3503171).sum := by decide
  have hdescent : baseEnd_3503171 < baseStart_3503171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503201 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 8]
def baseStart_3503201 : Nat := 118140960795 + 3503201 * 2 ^ 59
def prefixEnd_3503201 : Nat := 4983230072969 + 3 ^ 40 * 3503201 * 2
def baseEnd_3503201 : Nat := 399739098291434098594795

theorem tailTrace_3503201 : CollatzResearch.WordTrace tailWord_3503201 prefixEnd_3503201 399739098291434098594795 := by
  unfold tailWord_3503201
  simp only [CollatzResearch.WordTrace]
  refine ⟨127772237381508550942885457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85181491587672367295256971 127772237381508550942885457)
  ·
    refine ⟨95829178036131413207164093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127772237381508550942885457 95829178036131413207164093)
    ·
      refine ⟨35935941763549279952686535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95829178036131413207164093 35935941763549279952686535)
      ·
        refine ⟨53903912645323919929029803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35935941763549279952686535 53903912645323919929029803)
        ·
          refine ⟨80855868967985879893544705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53903912645323919929029803 80855868967985879893544705)
          ·
            refine ⟨60641901725989409920158529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80855868967985879893544705 60641901725989409920158529)
            ·
              refine ⟨45481426294492057440118897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60641901725989409920158529 45481426294492057440118897)
              ·
                refine ⟨34111069720869043080089173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45481426294492057440118897 34111069720869043080089173)
                ·
                  refine ⟨399739098291434098594795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34111069720869043080089173 399739098291434098594795)
                  ·
                    rfl

theorem cell22_3503201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_3503201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503201 prefixEnd_3503201 := by exact prefixLift 3503201
  have htrace : WordTrace (prefixWord ++ tailWord_3503201) baseStart_3503201 baseEnd_3503201 := by
    simpa [prefixWord, tailWord_3503201, baseEnd_3503201] using wordTrace_append hprefix tailTrace_3503201
  have hstable : (prefixWord ++ tailWord_3503201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503201).length < 2 ^ (prefixWord ++ tailWord_3503201).sum := by decide
  have hdescent : baseEnd_3503201 < baseStart_3503201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503237 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_3503237 : Nat := 118140960795 + 3503237 * 2 ^ 59
def prefixEnd_3503237 : Nat := 4983230072969 + 3 ^ 40 * 3503237 * 2
def baseEnd_3503237 : Nat := 1199229618410010201884275

theorem tailTrace_3503237 : CollatzResearch.WordTrace tailWord_3503237 prefixEnd_3503237 1199229618410010201884275 := by
  unfold tailWord_3503237
  simp only [CollatzResearch.WordTrace]
  refine ⟨127773550409378129091195965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85182366939585419394130643 127773550409378129091195965)
  ·
    refine ⟨47915081403516798409198487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127773550409378129091195965 47915081403516798409198487)
    ·
      refine ⟨71872622105275197613797731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47915081403516798409198487 71872622105275197613797731)
      ·
        refine ⟨107808933157912796420696597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71872622105275197613797731 107808933157912796420696597)
        ·
          refine ⟨5053543741777162332220153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107808933157912796420696597 5053543741777162332220153)
          ·
            refine ⟨3790157806332871749165115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5053543741777162332220153 3790157806332871749165115)
            ·
              refine ⟨5685236709499307623747673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790157806332871749165115 5685236709499307623747673)
              ·
                refine ⟨4263927532124480717810755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5685236709499307623747673 4263927532124480717810755)
                ·
                  refine ⟨6395891298186721076716133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263927532124480717810755 6395891298186721076716133)
                  ·
                    refine ⟨1199229618410010201884275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6395891298186721076716133 1199229618410010201884275)
                    ·
                      rfl

theorem cell22_3503237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_3503237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503237 prefixEnd_3503237 := by exact prefixLift 3503237
  have htrace : WordTrace (prefixWord ++ tailWord_3503237) baseStart_3503237 baseEnd_3503237 := by
    simpa [prefixWord, tailWord_3503237, baseEnd_3503237] using wordTrace_append hprefix tailTrace_3503237
  have hstable : (prefixWord ++ tailWord_3503237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503237).length < 2 ^ (prefixWord ++ tailWord_3503237).sum := by decide
  have hdescent : baseEnd_3503237 < baseStart_3503237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503250 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3503250 : Nat := 118140960795 + 3503250 * 2 ^ 59
def prefixEnd_3503250 : Nat := 4983230072969 + 3 ^ 40 * 3503250 * 2
def baseEnd_3503250 : Nat := 1199234068575682501309235

theorem tailTrace_3503250 : CollatzResearch.WordTrace tailWord_3503250 prefixEnd_3503250 1199234068575682501309235 := by
  unfold tailWord_3503250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31943506139582758077854801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85182683038887354874279469 31943506139582758077854801)
  ·
    refine ⟨23957629604687068558391101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31943506139582758077854801 23957629604687068558391101)
    ·
      refine ⟨8984111101757650709396663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23957629604687068558391101 8984111101757650709396663)
      ·
        refine ⟨13476166652636476064094995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8984111101757650709396663 13476166652636476064094995)
        ·
          refine ⟨20214249978954714096142493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13476166652636476064094995 20214249978954714096142493)
          ·
            refine ⟨7580343742108017786053435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20214249978954714096142493 7580343742108017786053435)
            ·
              refine ⟨11370515613162026679080153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7580343742108017786053435 11370515613162026679080153)
              ·
                refine ⟨8527886709871520009310115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11370515613162026679080153 8527886709871520009310115)
                ·
                  refine ⟨12791830064807280013965173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8527886709871520009310115 12791830064807280013965173)
                  ·
                    refine ⟨1199234068575682501309235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12791830064807280013965173 1199234068575682501309235)
                    ·
                      rfl

theorem cell22_3503250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3503250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503250 prefixEnd_3503250 := by exact prefixLift 3503250
  have htrace : WordTrace (prefixWord ++ tailWord_3503250) baseStart_3503250 baseEnd_3503250 := by
    simpa [prefixWord, tailWord_3503250, baseEnd_3503250] using wordTrace_append hprefix tailTrace_3503250
  have hstable : (prefixWord ++ tailWord_3503250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503250).length < 2 ^ (prefixWord ++ tailWord_3503250).sum := by decide
  have hdescent : baseEnd_3503250 < baseStart_3503250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503263 : List Nat := [1, 1, 2, 6, 2, 10]
def baseStart_3503263 : Nat := 118140960795 + 3503263 * 2 ^ 59
def prefixEnd_3503263 : Nat := 4983230072969 + 3 ^ 40 * 3503263 * 2
def baseEnd_3503263 : Nat := 14805413811621664206595

theorem tailTrace_3503263 : CollatzResearch.WordTrace tailWord_3503263 prefixEnd_3503263 14805413811621664206595 := by
  unfold tailWord_3503263
  simp only [CollatzResearch.WordTrace]
  refine ⟨127774498707283935531642443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85182999138189290354428295 127774498707283935531642443)
  ·
    refine ⟨191661748060925903297463665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127774498707283935531642443 191661748060925903297463665)
    ·
      refine ⟨143746311045694427473097749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191661748060925903297463665 143746311045694427473097749)
      ·
        refine ⟨6738108330266926287801457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143746311045694427473097749 6738108330266926287801457)
        ·
          refine ⟨5053581247700194715851093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6738108330266926287801457 5053581247700194715851093)
          ·
            refine ⟨14805413811621664206595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5053581247700194715851093 14805413811621664206595)
            ·
              rfl

theorem cell22_3503263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 10].length) (baseStart_3503263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503263 prefixEnd_3503263 := by exact prefixLift 3503263
  have htrace : WordTrace (prefixWord ++ tailWord_3503263) baseStart_3503263 baseEnd_3503263 := by
    simpa [prefixWord, tailWord_3503263, baseEnd_3503263] using wordTrace_append hprefix tailTrace_3503263
  have hstable : (prefixWord ++ tailWord_3503263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503263).length < 2 ^ (prefixWord ++ tailWord_3503263).sum := by decide
  have hdescent : baseEnd_3503263 < baseStart_3503263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503297 : List Nat := [1, 2, 6, 1, 1, 2, 3, 6]
def baseStart_3503297 : Nat := 118140960795 + 3503297 * 2 ^ 59
def prefixEnd_3503297 : Nat := 4983230072969 + 3 ^ 40 * 3503297 * 2
def baseEnd_3503297 : Nat := 133250017515132227264899

theorem tailTrace_3503297 : CollatzResearch.WordTrace tailWord_3503297 prefixEnd_3503297 133250017515132227264899 := by
  unfold tailWord_3503297
  simp only [CollatzResearch.WordTrace]
  refine ⟨127775738789160759338380145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85183825859440506225586763 127775738789160759338380145)
  ·
    refine ⟨95831804091870569503785109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127775738789160759338380145 95831804091870569503785109)
    ·
      refine ⟨4492115816806432945489927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95831804091870569503785109 4492115816806432945489927)
      ·
        refine ⟨6738173725209649418234891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492115816806432945489927 6738173725209649418234891)
        ·
          refine ⟨10107260587814474127352337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6738173725209649418234891 10107260587814474127352337)
          ·
            refine ⟨7580445440860855595514253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10107260587814474127352337 7580445440860855595514253)
            ·
              refine ⟨2842667040322820848317845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7580445440860855595514253 2842667040322820848317845)
              ·
                refine ⟨133250017515132227264899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2842667040322820848317845 133250017515132227264899)
                ·
                  rfl

theorem cell22_3503297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 6].length) (baseStart_3503297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503297 prefixEnd_3503297 := by exact prefixLift 3503297
  have htrace : WordTrace (prefixWord ++ tailWord_3503297) baseStart_3503297 baseEnd_3503297 := by
    simpa [prefixWord, tailWord_3503297, baseEnd_3503297] using wordTrace_append hprefix tailTrace_3503297
  have hstable : (prefixWord ++ tailWord_3503297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503297).length < 2 ^ (prefixWord ++ tailWord_3503297).sum := by decide
  have hdescent : baseEnd_3503297 < baseStart_3503297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503318 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3503318 : Nat := 118140960795 + 3503318 * 2 ^ 59
def prefixEnd_3503318 : Nat := 4983230072969 + 3 ^ 40 * 3503318 * 2
def baseEnd_3503318 : Nat := 1199257346365352990609027

theorem tailTrace_3503318 : CollatzResearch.WordTrace tailWord_3503318 prefixEnd_3503318 1199257346365352990609027 := by
  unfold tailWord_3503318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7986031545130292495305913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85184336481389786616596405 7986031545130292495305913)
  ·
    refine ⟨5989523658847719371479435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7986031545130292495305913 5989523658847719371479435)
    ·
      refine ⟨8984285488271579057219153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5989523658847719371479435 8984285488271579057219153)
      ·
        refine ⟨6738214116203684292914365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8984285488271579057219153 6738214116203684292914365)
        ·
          refine ⟨2526830293576381609842887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6738214116203684292914365 2526830293576381609842887)
          ·
            refine ⟨3790245440364572414764331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526830293576381609842887 3790245440364572414764331)
            ·
              refine ⟨5685368160546858622146497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790245440364572414764331 5685368160546858622146497)
              ·
                refine ⟨4264026120410143966609873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5685368160546858622146497 4264026120410143966609873)
                ·
                  refine ⟨3198019590307607974957405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4264026120410143966609873 3198019590307607974957405)
                  ·
                    refine ⟨1199257346365352990609027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198019590307607974957405 1199257346365352990609027)
                    ·
                      rfl

theorem cell22_3503318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3503318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503318 prefixEnd_3503318 := by exact prefixLift 3503318
  have htrace : WordTrace (prefixWord ++ tailWord_3503318) baseStart_3503318 baseEnd_3503318 := by
    simpa [prefixWord, tailWord_3503318, baseEnd_3503318] using wordTrace_append hprefix tailTrace_3503318
  have hstable : (prefixWord ++ tailWord_3503318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503318).length < 2 ^ (prefixWord ++ tailWord_3503318).sum := by decide
  have hdescent : baseEnd_3503318 < baseStart_3503318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503348 : List Nat := [2, 6, 1, 2, 2, 1, 2, 6]
def baseStart_3503348 : Nat := 118140960795 + 3503348 * 2 ^ 59
def prefixEnd_3503348 : Nat := 4983230072969 + 3 ^ 40 * 3503348 * 2
def baseEnd_3503348 : Nat := 133251957330938101373215

theorem tailTrace_3503348 : CollatzResearch.WordTrace tailWord_3503348 prefixEnd_3503348 133251957330938101373215 := by
  unfold tailWord_3503348
  simp only [CollatzResearch.WordTrace]
  refine ⟨63888799455987997524243349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85185065941317330032324465 63888799455987997524243349)
  ·
    refine ⟨2994787474499437383948907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63888799455987997524243349 2994787474499437383948907)
    ·
      refine ⟨4492181211749156075923361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2994787474499437383948907 4492181211749156075923361)
      ·
        refine ⟨3369135908811867056942521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4492181211749156075923361 3369135908811867056942521)
        ·
          refine ⟨2526851931608900292706891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3369135908811867056942521 2526851931608900292706891)
          ·
            refine ⟨3790277897413350439060337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526851931608900292706891 3790277897413350439060337)
            ·
              refine ⟨2842708423060012829295253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3790277897413350439060337 2842708423060012829295253)
              ·
                refine ⟨133251957330938101373215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2842708423060012829295253 133251957330938101373215)
                ·
                  rfl

theorem cell22_3503348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 6].length) (baseStart_3503348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503348 prefixEnd_3503348 := by exact prefixLift 3503348
  have htrace : WordTrace (prefixWord ++ tailWord_3503348) baseStart_3503348 baseEnd_3503348 := by
    simpa [prefixWord, tailWord_3503348, baseEnd_3503348] using wordTrace_append hprefix tailTrace_3503348
  have hstable : (prefixWord ++ tailWord_3503348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503348).length < 2 ^ (prefixWord ++ tailWord_3503348).sum := by decide
  have hdescent : baseEnd_3503348 < baseStart_3503348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503353 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 6]
def baseStart_3503353 : Nat := 118140960795 + 3503353 * 2 ^ 59
def prefixEnd_3503353 : Nat := 4983230072969 + 3 ^ 40 * 3503353 * 2
def baseEnd_3503353 : Nat := 399756442526874855327973

theorem tailTrace_3503353 : CollatzResearch.WordTrace tailWord_3503353 prefixEnd_3503353 399756442526874855327973 := by
  unfold tailWord_3503353
  simp only [CollatzResearch.WordTrace]
  refine ⟨127777781276957880902418713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85185187517971920601612475 127777781276957880902418713)
  ·
    refine ⟨95833335957718410676814035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127777781276957880902418713 95833335957718410676814035)
    ·
      refine ⟨143750003936577616015221053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95833335957718410676814035 143750003936577616015221053)
      ·
        refine ⟨53906251476216606005707895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143750003936577616015221053 53906251476216606005707895)
        ·
          refine ⟨80859377214324909008561843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53906251476216606005707895 80859377214324909008561843)
          ·
            refine ⟨121289065821487363512842765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80859377214324909008561843 121289065821487363512842765)
            ·
              refine ⟨45483399683057761317316037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121289065821487363512842765 45483399683057761317316037)
              ·
                refine ⟨8528137440573330246996757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45483399683057761317316037 8528137440573330246996757)
                ·
                  refine ⟨399756442526874855327973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8528137440573330246996757 399756442526874855327973)
                  ·
                    rfl

theorem cell22_3503353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_3503353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503353 prefixEnd_3503353 := by exact prefixLift 3503353
  have htrace : WordTrace (prefixWord ++ tailWord_3503353) baseStart_3503353 baseEnd_3503353 := by
    simpa [prefixWord, tailWord_3503353, baseEnd_3503353] using wordTrace_append hprefix tailTrace_3503353
  have hstable : (prefixWord ++ tailWord_3503353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503353).length < 2 ^ (prefixWord ++ tailWord_3503353).sum := by decide
  have hdescent : baseEnd_3503353 < baseStart_3503353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503445 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3503445 : Nat := 118140960795 + 3503445 * 2 ^ 59
def prefixEnd_3503445 : Nat := 4983230072969 + 3 ^ 40 * 3503445 * 2
def baseEnd_3503445 : Nat := 1199300821060766992683637

theorem tailTrace_3503445 : CollatzResearch.WordTrace tailWord_3503445 prefixEnd_3503445 1199300821060766992683637 := by
  unfold tailWord_3503445
  simp only [CollatzResearch.WordTrace]
  refine ⟨127781136792624580614767789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85187424528416387076511859 127781136792624580614767789)
  ·
    refine ⟨47917926297234217730537921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127781136792624580614767789 47917926297234217730537921)
    ·
      refine ⟨35938444722925663297903441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47917926297234217730537921 35938444722925663297903441)
      ·
        refine ⟨26953833542194247473427581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35938444722925663297903441 26953833542194247473427581)
        ·
          refine ⟨10107687578322842802535343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26953833542194247473427581 10107687578322842802535343)
          ·
            refine ⟨15161531367484264203803015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10107687578322842802535343 15161531367484264203803015)
            ·
              refine ⟨22742297051226396305704523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15161531367484264203803015 22742297051226396305704523)
              ·
                refine ⟨34113445576839594458556785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22742297051226396305704523 34113445576839594458556785)
                ·
                  refine ⟨25585084182629695843917589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34113445576839594458556785 25585084182629695843917589)
                  ·
                    refine ⟨1199300821060766992683637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25585084182629695843917589 1199300821060766992683637)
                    ·
                      rfl

theorem cell22_3503445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3503445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503445 prefixEnd_3503445 := by exact prefixLift 3503445
  have htrace : WordTrace (prefixWord ++ tailWord_3503445) baseStart_3503445 baseEnd_3503445 := by
    simpa [prefixWord, tailWord_3503445, baseEnd_3503445] using wordTrace_append hprefix tailTrace_3503445
  have hstable : (prefixWord ++ tailWord_3503445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503445).length < 2 ^ (prefixWord ++ tailWord_3503445).sum := by decide
  have hdescent : baseEnd_3503445 < baseStart_3503445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503464 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 3, 3]
def baseStart_3503464 : Nat := 118140960795 + 3503464 * 2 ^ 59
def prefixEnd_3503464 : Nat := 4983230072969 + 3 ^ 40 * 3503464 * 2
def baseEnd_3503464 : Nat := 1199307325149057276458579

theorem tailTrace_3503464 : CollatzResearch.WordTrace tailWord_3503464 prefixEnd_3503464 1199307325149057276458579 := by
  unfold tailWord_3503464
  simp only [CollatzResearch.WordTrace]
  refine ⟨63890914889777873429854723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85187886519703831239806297 63890914889777873429854723)
  ·
    refine ⟨95836372334666810144782085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63890914889777873429854723 95836372334666810144782085)
    ·
      refine ⟨17969319812750026902146641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95836372334666810144782085 17969319812750026902146641)
      ·
        refine ⟨13476989859562520176609981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17969319812750026902146641 13476989859562520176609981)
        ·
          refine ⟨5053871197335945066228743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13476989859562520176609981 5053871197335945066228743)
          ·
            refine ⟨7580806796003917599343115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5053871197335945066228743 7580806796003917599343115)
            ·
              refine ⟨11371210194005876399014673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7580806796003917599343115 11371210194005876399014673)
              ·
                refine ⟨8528407645504407299261005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11371210194005876399014673 8528407645504407299261005)
                ·
                  refine ⟨3198152867064152737222877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8528407645504407299261005 3198152867064152737222877)
                  ·
                    refine ⟨1199307325149057276458579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198152867064152737222877 1199307325149057276458579)
                    ·
                      rfl

theorem cell22_3503464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_3503464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503464 prefixEnd_3503464 := by exact prefixLift 3503464
  have htrace : WordTrace (prefixWord ++ tailWord_3503464) baseStart_3503464 baseEnd_3503464 := by
    simpa [prefixWord, tailWord_3503464, baseEnd_3503464] using wordTrace_append hprefix tailTrace_3503464
  have hstable : (prefixWord ++ tailWord_3503464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503464).length < 2 ^ (prefixWord ++ tailWord_3503464).sum := by decide
  have hdescent : baseEnd_3503464 < baseStart_3503464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503522 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_3503522 : Nat := 118140960795 + 3503522 * 2 ^ 59
def prefixEnd_3503522 : Nat := 4983230072969 + 3 ^ 40 * 3503522 * 2
def baseEnd_3503522 : Nat := 399775726578121486169467

theorem tailTrace_3503522 : CollatzResearch.WordTrace tailWord_3503522 prefixEnd_3503522 399775726578121486169467 := by
  unfold tailWord_3503522
  simp only [CollatzResearch.WordTrace]
  refine ⟨31945986303336405691330205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85189296808897081843547213 31945986303336405691330205)
  ·
    refine ⟨11979744863751152134248827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31945986303336405691330205 11979744863751152134248827)
    ·
      refine ⟨17969617295626728201373241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11979744863751152134248827 17969617295626728201373241)
      ·
        refine ⟨13477212971720046151029931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17969617295626728201373241 13477212971720046151029931)
        ·
          refine ⟨20215819457580069226544897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13477212971720046151029931 20215819457580069226544897)
          ·
            refine ⟨15161864593185051919908673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20215819457580069226544897 15161864593185051919908673)
            ·
              refine ⟨11371398444888788939931505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15161864593185051919908673 11371398444888788939931505)
              ·
                refine ⟨8528548833666591704948629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11371398444888788939931505 8528548833666591704948629)
                ·
                  refine ⟨399775726578121486169467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8528548833666591704948629 399775726578121486169467)
                  ·
                    rfl

theorem cell22_3503522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_3503522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503522 prefixEnd_3503522 := by exact prefixLift 3503522
  have htrace : WordTrace (prefixWord ++ tailWord_3503522) baseStart_3503522 baseEnd_3503522 := by
    simpa [prefixWord, tailWord_3503522, baseEnd_3503522] using wordTrace_append hprefix tailTrace_3503522
  have hstable : (prefixWord ++ tailWord_3503522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503522).length < 2 ^ (prefixWord ++ tailWord_3503522).sum := by decide
  have hdescent : baseEnd_3503522 < baseStart_3503522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503535 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 6, 4]
def baseStart_3503535 : Nat := 118140960795 + 3503535 * 2 ^ 59
def prefixEnd_3503535 : Nat := 4983230072969 + 3 ^ 40 * 3503535 * 2
def baseEnd_3503535 : Nat := 1199331629900036757933361

theorem tailTrace_3503535 : CollatzResearch.WordTrace tailWord_3503535 prefixEnd_3503535 1199331629900036757933361 := by
  unfold tailWord_3503535
  simp only [CollatzResearch.WordTrace]
  refine ⟨127784419362298525985544059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85189612908199017323696039 127784419362298525985544059)
  ·
    refine ⟨191676629043447788978316089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127784419362298525985544059 191676629043447788978316089)
    ·
      refine ⟨143757471782585841733737067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191676629043447788978316089 143757471782585841733737067)
      ·
        refine ⟨215636207673878762600605601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143757471782585841733737067 215636207673878762600605601)
        ·
          refine ⟨161727155755409071950454201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215636207673878762600605601 161727155755409071950454201)
          ·
            refine ⟨121295366816556803962840651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161727155755409071950454201 121295366816556803962840651)
            ·
              refine ⟨181943050224835205944260977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121295366816556803962840651 181943050224835205944260977)
              ·
                refine ⟨136457287668626404458195733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181943050224835205944260977 136457287668626404458195733)
                ·
                  refine ⟨6396435359466862708977925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136457287668626404458195733 6396435359466862708977925)
                  ·
                    refine ⟨1199331629900036757933361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6396435359466862708977925 1199331629900036757933361)
                    ·
                      rfl

theorem cell22_3503535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_3503535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503535 prefixEnd_3503535 := by exact prefixLift 3503535
  have htrace : WordTrace (prefixWord ++ tailWord_3503535) baseStart_3503535 baseEnd_3503535 := by
    simpa [prefixWord, tailWord_3503535, baseEnd_3503535] using wordTrace_append hprefix tailTrace_3503535
  have hstable : (prefixWord ++ tailWord_3503535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503535).length < 2 ^ (prefixWord ++ tailWord_3503535).sum := by decide
  have hdescent : baseEnd_3503535 < baseStart_3503535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503537 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 6, 3]
def baseStart_3503537 : Nat := 118140960795 + 3503537 * 2 ^ 59
def prefixEnd_3503537 : Nat := 4983230072969 + 3 ^ 40 * 3503537 * 2
def baseEnd_3503537 : Nat := 1199332314540909419383355

theorem tailTrace_3503537 : CollatzResearch.WordTrace tailWord_3503537 prefixEnd_3503537 1199332314540909419383355 := by
  unfold tailWord_3503537
  simp only [CollatzResearch.WordTrace]
  refine ⟨127784492308291280327116865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85189661538860853551411243 127784492308291280327116865)
  ·
    refine ⟨95838369231218460245337649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127784492308291280327116865 95838369231218460245337649)
    ·
      refine ⟨71878776923413845184003237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95838369231218460245337649 71878776923413845184003237)
      ·
        refine ⟨13477270673140095972000607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71878776923413845184003237 13477270673140095972000607)
        ·
          refine ⟨20215906009710143958000911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13477270673140095972000607 20215906009710143958000911)
          ·
            refine ⟨30323859014565215937001367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20215906009710143958000911 30323859014565215937001367)
            ·
              refine ⟨45485788521847823905502051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30323859014565215937001367 45485788521847823905502051)
              ·
                refine ⟨68228682782771735858253077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45485788521847823905502051 68228682782771735858253077)
                ·
                  refine ⟨3198219505442425118355613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68228682782771735858253077 3198219505442425118355613)
                  ·
                    refine ⟨1199332314540909419383355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198219505442425118355613 1199332314540909419383355)
                    ·
                      rfl

theorem cell22_3503537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_3503537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503537 prefixEnd_3503537 := by exact prefixLift 3503537
  have htrace : WordTrace (prefixWord ++ tailWord_3503537) baseStart_3503537 baseEnd_3503537 := by
    simpa [prefixWord, tailWord_3503537, baseEnd_3503537] using wordTrace_append hprefix tailTrace_3503537
  have hstable : (prefixWord ++ tailWord_3503537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503537).length < 2 ^ (prefixWord ++ tailWord_3503537).sum := by decide
  have hdescent : baseEnd_3503537 < baseStart_3503537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503595 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 7]
def baseStart_3503595 : Nat := 118140960795 + 3503595 * 2 ^ 59
def prefixEnd_3503595 : Nat := 4983230072969 + 3 ^ 40 * 3503595 * 2
def baseEnd_3503595 : Nat := 399784056375405533811059

theorem tailTrace_3503595 : CollatzResearch.WordTrace tailWord_3503595 prefixEnd_3503595 399784056375405533811059 := by
  unfold tailWord_3503595
  simp only [CollatzResearch.WordTrace]
  refine ⟨127786607742081156232728239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85191071828054104155152159 127786607742081156232728239)
  ·
    refine ⟨191679911613121734349092359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127786607742081156232728239 191679911613121734349092359)
    ·
      refine ⟨287519867419682601523638539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191679911613121734349092359 287519867419682601523638539)
      ·
        refine ⟨431279801129523902285457809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287519867419682601523638539 431279801129523902285457809)
        ·
          refine ⟨323459850847142926714093357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431279801129523902285457809 323459850847142926714093357)
          ·
            refine ⟨121297444067678597517785009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323459850847142926714093357 121297444067678597517785009)
            ·
              refine ⟨90973083050758948138338757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121297444067678597517785009 90973083050758948138338757)
              ·
                refine ⟨17057453072017302775938517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90973083050758948138338757 17057453072017302775938517)
                ·
                  refine ⟨399784056375405533811059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17057453072017302775938517 399784056375405533811059)
                  ·
                    rfl

theorem cell22_3503595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 7].length) (baseStart_3503595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503595 prefixEnd_3503595 := by exact prefixLift 3503595
  have htrace : WordTrace (prefixWord ++ tailWord_3503595) baseStart_3503595 baseEnd_3503595 := by
    simpa [prefixWord, tailWord_3503595, baseEnd_3503595] using wordTrace_append hprefix tailTrace_3503595
  have hstable : (prefixWord ++ tailWord_3503595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503595).length < 2 ^ (prefixWord ++ tailWord_3503595).sum := by decide
  have hdescent : baseEnd_3503595 < baseStart_3503595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503612 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 5]
def baseStart_3503612 : Nat := 118140960795 + 3503612 * 2 ^ 59
def prefixEnd_3503612 : Nat := 4983230072969 + 3 ^ 40 * 3503612 * 2
def baseEnd_3503612 : Nat := 399785996191211407919375

theorem tailTrace_3503612 : CollatzResearch.WordTrace tailWord_3503612 prefixEnd_3503612 399785996191211407919375 := by
  unfold tailWord_3503612
  simp only [CollatzResearch.WordTrace]
  refine ⟨63893613891509784068048545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85191485188679712090731393 63893613891509784068048545)
  ·
    refine ⟨47920210418632338051036409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63893613891509784068048545 47920210418632338051036409)
    ·
      refine ⟨35940157813974253538277307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47920210418632338051036409 35940157813974253538277307)
      ·
        refine ⟨53910236720961380307415961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35940157813974253538277307 53910236720961380307415961)
        ·
          refine ⟨40432677540721035230561971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53910236720961380307415961 40432677540721035230561971)
          ·
            refine ⟨60649016311081552845842957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40432677540721035230561971 60649016311081552845842957)
            ·
              refine ⟨22743381116655582317191109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60649016311081552845842957 22743381116655582317191109)
              ·
                refine ⟨4264383959372921684473333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22743381116655582317191109 4264383959372921684473333)
                ·
                  refine ⟨399785996191211407919375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4264383959372921684473333 399785996191211407919375)
                  ·
                    rfl

theorem cell22_3503612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_3503612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503612 prefixEnd_3503612 := by exact prefixLift 3503612
  have htrace : WordTrace (prefixWord ++ tailWord_3503612) baseStart_3503612 baseEnd_3503612 := by
    simpa [prefixWord, tailWord_3503612, baseEnd_3503612] using wordTrace_append hprefix tailTrace_3503612
  have hstable : (prefixWord ++ tailWord_3503612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503612).length < 2 ^ (prefixWord ++ tailWord_3503612).sum := by decide
  have hdescent : baseEnd_3503612 < baseStart_3503612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503674 : List Nat := [3, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_3503674 : Nat := 118140960795 + 3503674 * 2 ^ 59
def prefixEnd_3503674 : Nat := 4983230072969 + 3 ^ 40 * 3503674 * 2
def baseEnd_3503674 : Nat := 399793070813562242902645

theorem tailTrace_3503674 : CollatzResearch.WordTrace tailWord_3503674 prefixEnd_3503674 399793070813562242902645 := by
  unfold tailWord_3503674
  simp only [CollatzResearch.WordTrace]
  refine ⟨31947372277198738181213519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85192992739196635149902717 31947372277198738181213519)
  ·
    refine ⟨47921058415798107271820279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31947372277198738181213519 47921058415798107271820279)
    ·
      refine ⟨71881587623697160907730419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47921058415798107271820279 71881587623697160907730419)
      ·
        refine ⟨107822381435545741361595629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71881587623697160907730419 107822381435545741361595629)
        ·
          refine ⟨40433393038329653010598361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107822381435545741361595629 40433393038329653010598361)
          ·
            refine ⟨30325044778747239757948771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40433393038329653010598361 30325044778747239757948771)
            ·
              refine ⟨45487567168120859636923157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30325044778747239757948771 45487567168120859636923157)
              ·
                refine ⟨2132229711005665295480773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45487567168120859636923157 2132229711005665295480773)
                ·
                  refine ⟨399793070813562242902645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132229711005665295480773 399793070813562242902645)
                  ·
                    rfl

theorem cell22_3503674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_3503674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503674 prefixEnd_3503674 := by exact prefixLift 3503674
  have htrace : WordTrace (prefixWord ++ tailWord_3503674) baseStart_3503674 baseEnd_3503674 := by
    simpa [prefixWord, tailWord_3503674, baseEnd_3503674] using wordTrace_append hprefix tailTrace_3503674
  have hstable : (prefixWord ++ tailWord_3503674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503674).length < 2 ^ (prefixWord ++ tailWord_3503674).sum := by decide
  have hdescent : baseEnd_3503674 < baseStart_3503674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503689 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 2, 3]
def baseStart_3503689 : Nat := 118140960795 + 3503689 * 2 ^ 59
def prefixEnd_3503689 : Nat := 4983230072969 + 3 ^ 40 * 3503689 * 2
def baseEnd_3503689 : Nat := 1199384347247231689582889

theorem tailTrace_3503689 : CollatzResearch.WordTrace tailWord_3503689 prefixEnd_3503689 1199384347247231689582889 := by
  unfold tailWord_3503689
  simp only [CollatzResearch.WordTrace]
  refine ⟨127790036203740610286650121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85193357469160406857766747 127790036203740610286650121)
  ·
    refine ⟨95842527152805457714987591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127790036203740610286650121 95842527152805457714987591)
    ·
      refine ⟨143763790729208186572481387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95842527152805457714987591 143763790729208186572481387)
      ·
        refine ⟨215645686093812279858722081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143763790729208186572481387 215645686093812279858722081)
        ·
          refine ⟨161734264570359209894041561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215645686093812279858722081 161734264570359209894041561)
          ·
            refine ⟨121300698427769407420531171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161734264570359209894041561 121300698427769407420531171)
            ·
              refine ⟨181951047641654111130796757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121300698427769407420531171 181951047641654111130796757)
              ·
                refine ⟨4264477679101268229628049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 181951047641654111130796757 4264477679101268229628049)
                ·
                  refine ⟨3198358259325951172221037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4264477679101268229628049 3198358259325951172221037)
                  ·
                    refine ⟨1199384347247231689582889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198358259325951172221037 1199384347247231689582889)
                    ·
                      rfl

theorem cell22_3503689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_3503689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503689 prefixEnd_3503689 := by exact prefixLift 3503689
  have htrace : WordTrace (prefixWord ++ tailWord_3503689) baseStart_3503689 baseEnd_3503689 := by
    simpa [prefixWord, tailWord_3503689, baseEnd_3503689] using wordTrace_append hprefix tailTrace_3503689
  have hstable : (prefixWord ++ tailWord_3503689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503689).length < 2 ^ (prefixWord ++ tailWord_3503689).sum := by decide
  have hdescent : baseEnd_3503689 < baseStart_3503689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503693 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3503693 : Nat := 118140960795 + 3503693 * 2 ^ 59
def prefixEnd_3503693 : Nat := 4983230072969 + 3 ^ 40 * 3503693 * 2
def baseEnd_3503693 : Nat := 1199385716528977012482877

theorem tailTrace_3503693 : CollatzResearch.WordTrace tailWord_3503693 prefixEnd_3503693 1199385716528977012482877 := by
  unfold tailWord_3503693
  simp only [CollatzResearch.WordTrace]
  refine ⟨127790182095726118969795733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85193454730484079313197155 127790182095726118969795733)
  ·
    refine ⟨5990164785737161826709175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127790182095726118969795733 5990164785737161826709175)
    ·
      refine ⟨8985247178605742740063763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5990164785737161826709175 8985247178605742740063763)
      ·
        refine ⟨13477870767908614110095645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8985247178605742740063763 13477870767908614110095645)
        ·
          refine ⟨5054201537965730291285867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13477870767908614110095645 5054201537965730291285867)
          ·
            refine ⟨7581302306948595436928801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054201537965730291285867 7581302306948595436928801)
            ·
              refine ⟨5685976730211446577696601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7581302306948595436928801 5685976730211446577696601)
              ·
                refine ⟨4264482547658584933272451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5685976730211446577696601 4264482547658584933272451)
                ·
                  refine ⟨6396723821487877399908677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264482547658584933272451 6396723821487877399908677)
                  ·
                    refine ⟨1199385716528977012482877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6396723821487877399908677 1199385716528977012482877)
                    ·
                      rfl

theorem cell22_3503693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3503693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503693 prefixEnd_3503693 := by exact prefixLift 3503693
  have htrace : WordTrace (prefixWord ++ tailWord_3503693) baseStart_3503693 baseEnd_3503693 := by
    simpa [prefixWord, tailWord_3503693, baseEnd_3503693] using wordTrace_append hprefix tailTrace_3503693
  have hstable : (prefixWord ++ tailWord_3503693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503693).length < 2 ^ (prefixWord ++ tailWord_3503693).sum := by decide
  have hdescent : baseEnd_3503693 < baseStart_3503693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503708 : List Nat := [2, 2, 4, 1, 2, 3, 1, 3, 4]
def baseStart_3503708 : Nat := 118140960795 + 3503708 * 2 ^ 59
def prefixEnd_3503708 : Nat := 4983230072969 + 3 ^ 40 * 3503708 * 2
def baseEnd_3503708 : Nat := 399796950445173991119277

theorem tailTrace_3503708 : CollatzResearch.WordTrace tailWord_3503708 prefixEnd_3503708 399796950445173991119277 := by
  unfold tailWord_3503708
  simp only [CollatzResearch.WordTrace]
  refine ⟨63895364595335888265795889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85193819460447851021061185 63895364595335888265795889)
  ·
    refine ⟨47921523446501916199346917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63895364595335888265795889 47921523446501916199346917)
    ·
      refine ⟨8985285646219109287377547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47921523446501916199346917 8985285646219109287377547)
      ·
        refine ⟨13477928469328663931066321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8985285646219109287377547 13477928469328663931066321)
        ·
          refine ⟨10108446351996497948299741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13477928469328663931066321 10108446351996497948299741)
          ·
            refine ⟨3790667381998686730612403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10108446351996497948299741 3790667381998686730612403)
            ·
              refine ⟨5686001072998030095918605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790667381998686730612403 5686001072998030095918605)
              ·
                refine ⟨2132250402374261285969477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5686001072998030095918605 2132250402374261285969477)
                ·
                  refine ⟨399796950445173991119277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132250402374261285969477 399796950445173991119277)
                  ·
                    rfl

theorem cell22_3503708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_3503708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503708 prefixEnd_3503708 := by exact prefixLift 3503708
  have htrace : WordTrace (prefixWord ++ tailWord_3503708) baseStart_3503708 baseEnd_3503708 := by
    simpa [prefixWord, tailWord_3503708, baseEnd_3503708] using wordTrace_append hprefix tailTrace_3503708
  have hstable : (prefixWord ++ tailWord_3503708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503708).length < 2 ^ (prefixWord ++ tailWord_3503708).sum := by decide
  have hdescent : baseEnd_3503708 < baseStart_3503708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503794 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_3503794 : Nat := 118140960795 + 3503794 * 2 ^ 59
def prefixEnd_3503794 : Nat := 4983230072969 + 3 ^ 40 * 3503794 * 2
def baseEnd_3503794 : Nat := 1199420290893046415707567

theorem tailTrace_3503794 : CollatzResearch.WordTrace tailWord_3503794 prefixEnd_3503794 1199420290893046415707567 := by
  unfold tailWord_3503794
  simp only [CollatzResearch.WordTrace]
  refine ⟨31948466467090053304805609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85195910578906808812814957 31948466467090053304805609)
  ·
    refine ⟨23961349850317539978604207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31948466467090053304805609 23961349850317539978604207)
    ·
      refine ⟨35942024775476309967906311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23961349850317539978604207 35942024775476309967906311)
      ·
        refine ⟨53913037163214464951859467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35942024775476309967906311 53913037163214464951859467)
        ·
          refine ⟨80869555744821697427789201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53913037163214464951859467 80869555744821697427789201)
          ·
            refine ⟨60652166808616273070841901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80869555744821697427789201 60652166808616273070841901)
            ·
              refine ⟨22744562553231102401565713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60652166808616273070841901 22744562553231102401565713)
              ·
                refine ⟨17058421914923326801174285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22744562553231102401565713 17058421914923326801174285)
                ·
                  refine ⟨6396908218096247550440357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17058421914923326801174285 6396908218096247550440357)
                  ·
                    refine ⟨1199420290893046415707567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6396908218096247550440357 1199420290893046415707567)
                    ·
                      rfl

theorem cell22_3503794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_3503794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503794 prefixEnd_3503794 := by exact prefixLift 3503794
  have htrace : WordTrace (prefixWord ++ tailWord_3503794) baseStart_3503794 baseEnd_3503794 := by
    simpa [prefixWord, tailWord_3503794, baseEnd_3503794] using wordTrace_append hprefix tailTrace_3503794
  have hstable : (prefixWord ++ tailWord_3503794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503794).length < 2 ^ (prefixWord ++ tailWord_3503794).sum := by decide
  have hdescent : baseEnd_3503794 < baseStart_3503794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503798 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_3503798 : Nat := 118140960795 + 3503798 * 2 ^ 59
def prefixEnd_3503798 : Nat := 4983230072969 + 3 ^ 40 * 3503798 * 2
def baseEnd_3503798 : Nat := 399807220058263912869185

theorem tailTrace_3503798 : CollatzResearch.WordTrace tailWord_3503798 prefixEnd_3503798 399807220058263912869185 := by
  unfold tailWord_3503798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987125735021607618898003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85196007840230481268245365 7987125735021607618898003)
  ·
    refine ⟨11980688602532411428347005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7987125735021607618898003 11980688602532411428347005)
    ·
      refine ⟨4492758225949654285630127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11980688602532411428347005 4492758225949654285630127)
      ·
        refine ⟨6739137338924481428445191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492758225949654285630127 6739137338924481428445191)
        ·
          refine ⟨10108706008386722142667787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6739137338924481428445191 10108706008386722142667787)
          ·
            refine ⟨15163059012580083214001681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10108706008386722142667787 15163059012580083214001681)
            ·
              refine ⟨11372294259435062410501261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15163059012580083214001681 11372294259435062410501261)
              ·
                refine ⟨4264610347288148403937973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11372294259435062410501261 4264610347288148403937973)
                ·
                  refine ⟨399807220058263912869185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4264610347288148403937973 399807220058263912869185)
                  ·
                    rfl

theorem cell22_3503798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_3503798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503798 prefixEnd_3503798 := by exact prefixLift 3503798
  have htrace : WordTrace (prefixWord ++ tailWord_3503798) baseStart_3503798 baseEnd_3503798 := by
    simpa [prefixWord, tailWord_3503798, baseEnd_3503798] using wordTrace_append hprefix tailTrace_3503798
  have hstable : (prefixWord ++ tailWord_3503798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503798).length < 2 ^ (prefixWord ++ tailWord_3503798).sum := by decide
  have hdescent : baseEnd_3503798 < baseStart_3503798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503828 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3503828 : Nat := 118140960795 + 3503828 * 2 ^ 59
def prefixEnd_3503828 : Nat := 4983230072969 + 3 ^ 40 * 3503828 * 2
def baseEnd_3503828 : Nat := 1199431929787881660357463

theorem tailTrace_3503828 : CollatzResearch.WordTrace tailWord_3503828 prefixEnd_3503828 1199431929787881660357463 := by
  unfold tailWord_3503828
  simp only [CollatzResearch.WordTrace]
  refine ⟨63897552975118518512980069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85196737300158024683973425 63897552975118518512980069)
  ·
    refine ⟨11980791182834722221183763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63897552975118518512980069 11980791182834722221183763)
    ·
      refine ⟨17971186774252083331775645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11980791182834722221183763 17971186774252083331775645)
      ·
        refine ⟨6739195040344531249415867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17971186774252083331775645 6739195040344531249415867)
        ·
          refine ⟨10108792560516796874123801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6739195040344531249415867 10108792560516796874123801)
          ·
            refine ⟨7581594420387597655592851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10108792560516796874123801 7581594420387597655592851)
            ·
              refine ⟨11372391630581396483389277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581594420387597655592851 11372391630581396483389277)
              ·
                refine ⟨4264646861468023681270979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11372391630581396483389277 4264646861468023681270979)
                ·
                  refine ⟨6396970292202035521906469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264646861468023681270979 6396970292202035521906469)
                  ·
                    refine ⟨1199431929787881660357463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6396970292202035521906469 1199431929787881660357463)
                    ·
                      rfl

theorem cell22_3503828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3503828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503828 prefixEnd_3503828 := by exact prefixLift 3503828
  have htrace : WordTrace (prefixWord ++ tailWord_3503828) baseStart_3503828 baseEnd_3503828 := by
    simpa [prefixWord, tailWord_3503828, baseEnd_3503828] using wordTrace_append hprefix tailTrace_3503828
  have hstable : (prefixWord ++ tailWord_3503828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503828).length < 2 ^ (prefixWord ++ tailWord_3503828).sum := by decide
  have hdescent : baseEnd_3503828 < baseStart_3503828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503839 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 4, 4]
def baseStart_3503839 : Nat := 118140960795 + 3503839 * 2 ^ 59
def prefixEnd_3503839 : Nat := 4983230072969 + 3 ^ 40 * 3503839 * 2
def baseEnd_3503839 : Nat := 1199435695312681298332429

theorem tailTrace_3503839 : CollatzResearch.WordTrace tailWord_3503839 prefixEnd_3503839 1199435695312681298332429 := by
  unfold tailWord_3503839
  simp only [CollatzResearch.WordTrace]
  refine ⟨127795507153197185904610571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85197004768798123936407047 127795507153197185904610571)
  ·
    refine ⟨191693260729795778856915857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127795507153197185904610571 191693260729795778856915857)
    ·
      refine ⟨143769945547346834142686893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191693260729795778856915857 143769945547346834142686893)
      ·
        refine ⟨53913729580255062803507585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143769945547346834142686893 53913729580255062803507585)
        ·
          refine ⟨40435297185191297102630689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53913729580255062803507585 40435297185191297102630689)
          ·
            refine ⟨30326472888893472826973017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40435297185191297102630689 30326472888893472826973017)
            ·
              refine ⟨22744854666670104620229763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30326472888893472826973017 22744854666670104620229763)
              ·
                refine ⟨34117282000005156930344645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22744854666670104620229763 34117282000005156930344645)
                ·
                  refine ⟨6396990375000966924439621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34117282000005156930344645 6396990375000966924439621)
                  ·
                    refine ⟨1199435695312681298332429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6396990375000966924439621 1199435695312681298332429)
                    ·
                      rfl

theorem cell22_3503839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_3503839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503839 prefixEnd_3503839 := by exact prefixLift 3503839
  have htrace : WordTrace (prefixWord ++ tailWord_3503839) baseStart_3503839 baseEnd_3503839 := by
    simpa [prefixWord, tailWord_3503839, baseEnd_3503839] using wordTrace_append hprefix tailTrace_3503839
  have hstable : (prefixWord ++ tailWord_3503839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503839).length < 2 ^ (prefixWord ++ tailWord_3503839).sum := by decide
  have hdescent : baseEnd_3503839 < baseStart_3503839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503854 : List Nat := [4, 1, 2, 1, 1, 2, 2, 9]
def baseStart_3503854 : Nat := 118140960795 + 3503854 * 2 ^ 59
def prefixEnd_3503854 : Nat := 4983230072969 + 3 ^ 40 * 3503854 * 2
def baseEnd_3503854 : Nat := 133271203346580695467487

theorem tailTrace_3503854 : CollatzResearch.WordTrace tailWord_3503854 prefixEnd_3503854 133271203346580695467487 := by
  unfold tailWord_3503854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15974506781017855433300827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85197369498761895644271077 15974506781017855433300827)
  ·
    refine ⟨23961760171526783149951241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15974506781017855433300827 23961760171526783149951241)
    ·
      refine ⟨17971320128645087362463431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23961760171526783149951241 17971320128645087362463431)
      ·
        refine ⟨26956980192967631043695147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17971320128645087362463431 26956980192967631043695147)
        ·
          refine ⟨40435470289451446565542721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26956980192967631043695147 40435470289451446565542721)
          ·
            refine ⟨30326602717088584924157041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40435470289451446565542721 30326602717088584924157041)
            ·
              refine ⟨22744952037816438693117781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30326602717088584924157041 22744952037816438693117781)
              ·
                refine ⟨133271203346580695467487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22744952037816438693117781 133271203346580695467487)
                ·
                  rfl

theorem cell22_3503854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_3503854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503854 prefixEnd_3503854 := by exact prefixLift 3503854
  have htrace : WordTrace (prefixWord ++ tailWord_3503854) baseStart_3503854 baseEnd_3503854 := by
    simpa [prefixWord, tailWord_3503854, baseEnd_3503854] using wordTrace_append hprefix tailTrace_3503854
  have hstable : (prefixWord ++ tailWord_3503854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503854).length < 2 ^ (prefixWord ++ tailWord_3503854).sum := by decide
  have hdescent : baseEnd_3503854 < baseStart_3503854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503886 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_3503886 : Nat := 118140960795 + 3503886 * 2 ^ 59
def prefixEnd_3503886 : Nat := 4983230072969 + 3 ^ 40 * 3503886 * 2
def baseEnd_3503886 : Nat := 1199451784373188842407285

theorem tailTrace_3503886 : CollatzResearch.WordTrace tailWord_3503886 prefixEnd_3503886 1199451784373188842407285 := by
  unfold tailWord_3503886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15974652673003364116446439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85198147589351275287714341 15974652673003364116446439)
  ·
    refine ⟨23961979009505046174669659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15974652673003364116446439 23961979009505046174669659)
    ·
      refine ⟨35942968514257569262004489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23961979009505046174669659 35942968514257569262004489)
      ·
        refine ⟨26957226385693176946503367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35942968514257569262004489 26957226385693176946503367)
        ·
          refine ⟨40435839578539765419755051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26957226385693176946503367 40435839578539765419755051)
          ·
            refine ⟨60653759367809648129632577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40435839578539765419755051 60653759367809648129632577)
            ·
              refine ⟨45490319525857236097224433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60653759367809648129632577 45490319525857236097224433)
              ·
                refine ⟨34117739644392927072918325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45490319525857236097224433 34117739644392927072918325)
                ·
                  refine ⟨3198538091661836913086093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34117739644392927072918325 3198538091661836913086093)
                  ·
                    refine ⟨1199451784373188842407285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198538091661836913086093 1199451784373188842407285)
                    ·
                      rfl

theorem cell22_3503886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_3503886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503886 prefixEnd_3503886 := by exact prefixLift 3503886
  have htrace : WordTrace (prefixWord ++ tailWord_3503886) baseStart_3503886 baseEnd_3503886 := by
    simpa [prefixWord, tailWord_3503886, baseEnd_3503886] using wordTrace_append hprefix tailTrace_3503886
  have hstable : (prefixWord ++ tailWord_3503886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503886).length < 2 ^ (prefixWord ++ tailWord_3503886).sum := by decide
  have hdescent : baseEnd_3503886 < baseStart_3503886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503916 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 5]
def baseStart_3503916 : Nat := 118140960795 + 3503916 * 2 ^ 59
def prefixEnd_3503916 : Nat := 4983230072969 + 3 ^ 40 * 3503916 * 2
def baseEnd_3503916 : Nat := 399820684662092921385731

theorem tailTrace_3503916 : CollatzResearch.WordTrace tailWord_3503916 prefixEnd_3503916 399820684662092921385731 := by
  unfold tailWord_3503916
  simp only [CollatzResearch.WordTrace]
  refine ⟨63899157786959114027581801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85198877049278818703442401 63899157786959114027581801)
  ·
    refine ⟨47924368340219335520686351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63899157786959114027581801 47924368340219335520686351)
    ·
      refine ⟨71886552510329003281029527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47924368340219335520686351 71886552510329003281029527)
      ·
        refine ⟨107829828765493504921544291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71886552510329003281029527 107829828765493504921544291)
        ·
          refine ⟨161744743148240257382316437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107829828765493504921544291 161744743148240257382316437)
          ·
            refine ⟨7581784835073762064796083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161744743148240257382316437 7581784835073762064796083)
            ·
              refine ⟨11372677252610643097194125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581784835073762064796083 11372677252610643097194125)
              ·
                refine ⟨4264753969728991161447797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11372677252610643097194125 4264753969728991161447797)
                ·
                  refine ⟨399820684662092921385731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4264753969728991161447797 399820684662092921385731)
                  ·
                    rfl

theorem cell22_3503916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_3503916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3503916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3503916 prefixEnd_3503916 := by exact prefixLift 3503916
  have htrace : WordTrace (prefixWord ++ tailWord_3503916) baseStart_3503916 baseEnd_3503916 := by
    simpa [prefixWord, tailWord_3503916, baseEnd_3503916] using wordTrace_append hprefix tailTrace_3503916
  have hstable : (prefixWord ++ tailWord_3503916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503916).length < 2 ^ (prefixWord ++ tailWord_3503916).sum := by decide
  have hdescent : baseEnd_3503916 < baseStart_3503916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504010 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_3504010 : Nat := 118140960795 + 3504010 * 2 ^ 59
def prefixEnd_3504010 : Nat := 4983230072969 + 3 ^ 40 * 3504010 * 2
def baseEnd_3504010 : Nat := 1199494232107293852306905

theorem tailTrace_3504010 : CollatzResearch.WordTrace tailWord_3504010 prefixEnd_3504010 1199494232107293852306905 := by
  unfold tailWord_3504010
  simp only [CollatzResearch.WordTrace]
  refine ⟨31950436008894420527271371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85201162690385121406056989 31950436008894420527271371)
  ·
    refine ⟨47925654013341630790907057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31950436008894420527271371 47925654013341630790907057)
    ·
      refine ⟨35944240510006223093180293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47925654013341630790907057 35944240510006223093180293)
      ·
        refine ⟨6739545095626166829971305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35944240510006223093180293 6739545095626166829971305)
        ·
          refine ⟨5054658821719625122478479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6739545095626166829971305 5054658821719625122478479)
          ·
            refine ⟨7581988232579437683717719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054658821719625122478479 7581988232579437683717719)
            ·
              refine ⟨11372982348869156525576579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581988232579437683717719 11372982348869156525576579)
              ·
                refine ⟨17059473523303734788364869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11372982348869156525576579 17059473523303734788364869)
                ·
                  refine ⟨3198651285619450272818413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17059473523303734788364869 3198651285619450272818413)
                  ·
                    refine ⟨1199494232107293852306905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198651285619450272818413 1199494232107293852306905)
                    ·
                      rfl

theorem cell22_3504010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_3504010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504010 prefixEnd_3504010 := by exact prefixLift 3504010
  have htrace : WordTrace (prefixWord ++ tailWord_3504010) baseStart_3504010 baseEnd_3504010 := by
    simpa [prefixWord, tailWord_3504010, baseEnd_3504010] using wordTrace_append hprefix tailTrace_3504010
  have hstable : (prefixWord ++ tailWord_3504010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504010).length < 2 ^ (prefixWord ++ tailWord_3504010).sum := by decide
  have hdescent : baseEnd_3504010 < baseStart_3504010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504040 : List Nat := [2, 1, 6, 2, 1, 1, 1, 8]
def baseStart_3504040 : Nat := 118140960795 + 3504040 * 2 ^ 59
def prefixEnd_3504040 : Nat := 4983230072969 + 3 ^ 40 * 3504040 * 2
def baseEnd_3504040 : Nat := 133278277968931530450757

theorem tailTrace_3504040 : CollatzResearch.WordTrace tailWord_3504040 prefixEnd_3504040 133278277968931530450757 := by
  unfold tailWord_3504040
  simp only [CollatzResearch.WordTrace]
  refine ⟨63901419112734498616338787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85201892150312664821785049 63901419112734498616338787)
  ·
    refine ⟨95852128669101747924508181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63901419112734498616338787 95852128669101747924508181)
    ·
      refine ⟨4493068531364144433961321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95852128669101747924508181 4493068531364144433961321)
      ·
        refine ⟨3369801398523108325470991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4493068531364144433961321 3369801398523108325470991)
        ·
          refine ⟨5054702097784662488206487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369801398523108325470991 5054702097784662488206487)
          ·
            refine ⟨7582053146676993732309731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054702097784662488206487 7582053146676993732309731)
            ·
              refine ⟨11373079720015490598464597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7582053146676993732309731 11373079720015490598464597)
              ·
                refine ⟨133278277968931530450757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11373079720015490598464597 133278277968931530450757)
                ·
                  rfl

theorem cell22_3504040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 8].length) (baseStart_3504040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504040 prefixEnd_3504040 := by exact prefixLift 3504040
  have htrace : WordTrace (prefixWord ++ tailWord_3504040) baseStart_3504040 baseEnd_3504040 := by
    simpa [prefixWord, tailWord_3504040, baseEnd_3504040] using wordTrace_append hprefix tailTrace_3504040
  have hstable : (prefixWord ++ tailWord_3504040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504040).length < 2 ^ (prefixWord ++ tailWord_3504040).sum := by decide
  have hdescent : baseEnd_3504040 < baseStart_3504040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504046 : List Nat := [4, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_3504046 : Nat := 118140960795 + 3504046 * 2 ^ 59
def prefixEnd_3504046 : Nat := 4983230072969 + 3 ^ 40 * 3504046 * 2
def baseEnd_3504046 : Nat := 399835518547667252802265

theorem tailTrace_3504046 : CollatzResearch.WordTrace tailWord_3504046 prefixEnd_3504046 399835518547667252802265 := by
  unfold tailWord_3504046
  simp only [CollatzResearch.WordTrace]
  refine ⟨15975382132930907532174499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85202038042298173504930661 15975382132930907532174499)
  ·
    refine ⟨23963073199396361298261749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15975382132930907532174499 23963073199396361298261749)
    ·
      refine ⟨2246538112443408871712039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23963073199396361298261749 2246538112443408871712039)
      ·
        refine ⟨3369807168665113307568059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246538112443408871712039 3369807168665113307568059)
        ·
          refine ⟨5054710752997669961352089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369807168665113307568059 5054710752997669961352089)
          ·
            refine ⟨3791033064748252471014067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5054710752997669961352089 3791033064748252471014067)
            ·
              refine ⟨5686549597122378706521101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791033064748252471014067 5686549597122378706521101)
              ·
                refine ⟨2132456098920892014945413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5686549597122378706521101 2132456098920892014945413)
                ·
                  refine ⟨399835518547667252802265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132456098920892014945413 399835518547667252802265)
                  ·
                    rfl

theorem cell22_3504046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_3504046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504046 prefixEnd_3504046 := by exact prefixLift 3504046
  have htrace : WordTrace (prefixWord ++ tailWord_3504046) baseStart_3504046 baseEnd_3504046 := by
    simpa [prefixWord, tailWord_3504046, baseEnd_3504046] using wordTrace_append hprefix tailTrace_3504046
  have hstable : (prefixWord ++ tailWord_3504046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504046).length < 2 ^ (prefixWord ++ tailWord_3504046).sum := by decide
  have hdescent : baseEnd_3504046 < baseStart_3504046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504085 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 5]
def baseStart_3504085 : Nat := 118140960795 + 3504085 * 2 ^ 59
def prefixEnd_3504085 : Nat := 4983230072969 + 3 ^ 40 * 3504085 * 2
def baseEnd_3504085 : Nat := 399839968713339552227225

theorem tailTrace_3504085 : CollatzResearch.WordTrace tailWord_3504085 prefixEnd_3504085 399839968713339552227225 := by
  unfold tailWord_3504085
  simp only [CollatzResearch.WordTrace]
  refine ⟨127804479510305969918065709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85202986340203979945377139 127804479510305969918065709)
  ·
    refine ⟨47926679816364738719274641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127804479510305969918065709 47926679816364738719274641)
    ·
      refine ⟨35945009862273554039455981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47926679816364738719274641 35945009862273554039455981)
      ·
        refine ⟨13479378698352582764795993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35945009862273554039455981 13479378698352582764795993)
        ·
          refine ⟨10109534023764437073596995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13479378698352582764795993 10109534023764437073596995)
          ·
            refine ⟨15164301035646655610395493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10109534023764437073596995 15164301035646655610395493)
            ·
              refine ⟨2843306444183747926949155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15164301035646655610395493 2843306444183747926949155)
              ·
                refine ⟨4264959666275621890423733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843306444183747926949155 4264959666275621890423733)
                ·
                  refine ⟨399839968713339552227225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4264959666275621890423733 399839968713339552227225)
                  ·
                    rfl

theorem cell22_3504085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_3504085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504085 prefixEnd_3504085 := by exact prefixLift 3504085
  have htrace : WordTrace (prefixWord ++ tailWord_3504085) baseStart_3504085 baseEnd_3504085 := by
    simpa [prefixWord, tailWord_3504085, baseEnd_3504085] using wordTrace_append hprefix tailTrace_3504085
  have hstable : (prefixWord ++ tailWord_3504085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504085).length < 2 ^ (prefixWord ++ tailWord_3504085).sum := by decide
  have hdescent : baseEnd_3504085 < baseStart_3504085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504096 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 6]
def baseStart_3504096 : Nat := 118140960795 + 3504096 * 2 ^ 59
def prefixEnd_3504096 : Nat := 4983230072969 + 3 ^ 40 * 3504096 * 2
def baseEnd_3504096 : Nat := 399841223888272764885547

theorem tailTrace_3504096 : CollatzResearch.WordTrace tailWord_3504096 prefixEnd_3504096 399841223888272764885547 := by
  unfold tailWord_3504096
  simp only [CollatzResearch.WordTrace]
  refine ⟨63902440356633059398358071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85203253808844079197810761 63902440356633059398358071)
  ·
    refine ⟨95853660534949589097537107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63902440356633059398358071 95853660534949589097537107)
    ·
      refine ⟨143780490802424383646305661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95853660534949589097537107 143780490802424383646305661)
      ·
        refine ⟨53917684050909143867364623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143780490802424383646305661 53917684050909143867364623)
        ·
          refine ⟨80876526076363715801046935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53917684050909143867364623 80876526076363715801046935)
          ·
            refine ⟨121314789114545573701570403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80876526076363715801046935 121314789114545573701570403)
            ·
              refine ⟨181972183671818360552355605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121314789114545573701570403 181972183671818360552355605)
              ·
                refine ⟨8529946109616485650891669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181972183671818360552355605 8529946109616485650891669)
                ·
                  refine ⟨399841223888272764885547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8529946109616485650891669 399841223888272764885547)
                  ·
                    rfl

theorem cell22_3504096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_3504096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504096 prefixEnd_3504096 := by exact prefixLift 3504096
  have htrace : WordTrace (prefixWord ++ tailWord_3504096) baseStart_3504096 baseEnd_3504096 := by
    simpa [prefixWord, tailWord_3504096, baseEnd_3504096] using wordTrace_append hprefix tailTrace_3504096
  have hstable : (prefixWord ++ tailWord_3504096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504096).length < 2 ^ (prefixWord ++ tailWord_3504096).sum := by decide
  have hdescent : baseEnd_3504096 < baseStart_3504096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504171 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 1, 8]
def baseStart_3504171 : Nat := 118140960795 + 3504171 * 2 ^ 59
def prefixEnd_3504171 : Nat := 4983230072969 + 3 ^ 40 * 3504171 * 2
def baseEnd_3504171 : Nat := 1199549345697543099031411

theorem tailTrace_3504171 : CollatzResearch.WordTrace tailWord_3504171 prefixEnd_3504171 1199549345697543099031411 := by
  unfold tailWord_3504171
  simp only [CollatzResearch.WordTrace]
  refine ⟨127807616187994406605696367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85205077458662937737130911 127807616187994406605696367)
  ·
    refine ⟨191711424281991609908544551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127807616187994406605696367 191711424281991609908544551)
    ·
      refine ⟨287567136422987414862816827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191711424281991609908544551 287567136422987414862816827)
      ·
        refine ⟨431350704634481122294225241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287567136422987414862816827 431350704634481122294225241)
        ·
          refine ⟨323513028475860841720668931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431350704634481122294225241 323513028475860841720668931)
          ·
            refine ⟨485269542713791262581003397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323513028475860841720668931 485269542713791262581003397)
            ·
              refine ⟨90988039258835861733938137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 485269542713791262581003397 90988039258835861733938137)
              ·
                refine ⟨68241029444126896300453603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90988039258835861733938137 68241029444126896300453603)
                ·
                  refine ⟨102361544166190344450680405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68241029444126896300453603 102361544166190344450680405)
                  ·
                    refine ⟨1199549345697543099031411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102361544166190344450680405 1199549345697543099031411)
                    ·
                      rfl

theorem cell22_3504171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_3504171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504171 prefixEnd_3504171 := by exact prefixLift 3504171
  have htrace : WordTrace (prefixWord ++ tailWord_3504171) baseStart_3504171 baseEnd_3504171 := by
    simpa [prefixWord, tailWord_3504171, baseEnd_3504171] using wordTrace_append hprefix tailTrace_3504171
  have hstable : (prefixWord ++ tailWord_3504171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504171).length < 2 ^ (prefixWord ++ tailWord_3504171).sum := by decide
  have hdescent : baseEnd_3504171 < baseStart_3504171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504224 : List Nat := [2, 1, 1, 3, 2, 5, 1, 3, 1, 3]
def baseStart_3504224 : Nat := 118140960795 + 3504224 * 2 ^ 59
def prefixEnd_3504224 : Nat := 4983230072969 + 3 ^ 40 * 3504224 * 2
def baseEnd_3504224 : Nat := 1199567488680668627456249

theorem tailTrace_3504224 : CollatzResearch.WordTrace tailWord_3504224 prefixEnd_3504224 1199567488680668627456249 := by
  unfold tailWord_3504224
  simp only [CollatzResearch.WordTrace]
  refine ⟨63904774628401198328687863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85206366171201597771583817 63904774628401198328687863)
  ·
    refine ⟨95857161942601797493031795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63904774628401198328687863 95857161942601797493031795)
    ·
      refine ⟨143785742913902696239547693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95857161942601797493031795 143785742913902696239547693)
      ·
        refine ⟨53919653592713511089830385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143785742913902696239547693 53919653592713511089830385)
        ·
          refine ⟨40439740194535133317372789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53919653592713511089830385 40439740194535133317372789)
          ·
            refine ⟨3791225643237668748503699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40439740194535133317372789 3791225643237668748503699)
            ·
              refine ⟨5686838464856503122755549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791225643237668748503699 5686838464856503122755549)
              ·
                refine ⟨2132564424321188671033331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5686838464856503122755549 2132564424321188671033331)
                ·
                  refine ⟨3198846636481783006549997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132564424321188671033331 3198846636481783006549997)
                  ·
                    refine ⟨1199567488680668627456249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198846636481783006549997 1199567488680668627456249)
                    ·
                      rfl

theorem cell22_3504224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 3].length) (baseStart_3504224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504224 prefixEnd_3504224 := by exact prefixLift 3504224
  have htrace : WordTrace (prefixWord ++ tailWord_3504224) baseStart_3504224 baseEnd_3504224 := by
    simpa [prefixWord, tailWord_3504224, baseEnd_3504224] using wordTrace_append hprefix tailTrace_3504224
  have hstable : (prefixWord ++ tailWord_3504224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504224).length < 2 ^ (prefixWord ++ tailWord_3504224).sum := by decide
  have hdescent : baseEnd_3504224 < baseStart_3504224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504325 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_3504325 : Nat := 118140960795 + 3504325 * 2 ^ 59
def prefixEnd_3504325 : Nat := 4983230072969 + 3 ^ 40 * 3504325 * 2
def baseEnd_3504325 : Nat := 1199602063044738030680939

theorem tailTrace_3504325 : CollatzResearch.WordTrace tailWord_3504325 prefixEnd_3504325 1199602063044738030680939 := by
  unfold tailWord_3504325
  simp only [CollatzResearch.WordTrace]
  refine ⟨127813233029436490906802429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85208822019624327271201619 127813233029436490906802429)
  ·
    refine ⟨47929962386038684090050911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127813233029436490906802429 47929962386038684090050911)
    ·
      refine ⟨71894943579058026135076367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47929962386038684090050911 71894943579058026135076367)
      ·
        refine ⟨107842415368587039202614551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71894943579058026135076367 107842415368587039202614551)
        ·
          refine ⟨161763623052880558803921827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107842415368587039202614551 161763623052880558803921827)
          ·
            refine ⟨242645434579320838205882741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161763623052880558803921827 242645434579320838205882741)
            ·
              refine ⟨22748009491811328581801507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242645434579320838205882741 22748009491811328581801507)
              ·
                refine ⟨34122014237716992872702261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22748009491811328581801507 34122014237716992872702261)
                ·
                  refine ⟨3198938834785968081815837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34122014237716992872702261 3198938834785968081815837)
                  ·
                    refine ⟨1199602063044738030680939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198938834785968081815837 1199602063044738030680939)
                    ·
                      rfl

theorem cell22_3504325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_3504325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504325 prefixEnd_3504325 := by exact prefixLift 3504325
  have htrace : WordTrace (prefixWord ++ tailWord_3504325) baseStart_3504325 baseEnd_3504325 := by
    simpa [prefixWord, tailWord_3504325, baseEnd_3504325] using wordTrace_append hprefix tailTrace_3504325
  have hstable : (prefixWord ++ tailWord_3504325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504325).length < 2 ^ (prefixWord ++ tailWord_3504325).sum := by decide
  have hdescent : baseEnd_3504325 < baseStart_3504325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504348 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3504348 : Nat := 118140960795 + 3504348 * 2 ^ 59
def prefixEnd_3504348 : Nat := 4983230072969 + 3 ^ 40 * 3504348 * 2
def baseEnd_3504348 : Nat := 1199609936414773637355869

theorem tailTrace_3504348 : CollatzResearch.WordTrace tailWord_3504348 prefixEnd_3504348 1199609936414773637355869 := by
  unfold tailWord_3504348
  simp only [CollatzResearch.WordTrace]
  refine ⟨63907035954176582917444849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85209381272235443889926465 63907035954176582917444849)
  ·
    refine ⟨47930276965632437188083637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63907035954176582917444849 47930276965632437188083637)
    ·
      refine ⟨4493463465528040986382841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47930276965632437188083637 4493463465528040986382841)
      ·
        refine ⟨3370097599146030739787131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4493463465528040986382841 3370097599146030739787131)
        ·
          refine ⟨5055146398719046109680697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370097599146030739787131 5055146398719046109680697)
          ·
            refine ⟨3791359799039284582260523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5055146398719046109680697 3791359799039284582260523)
            ·
              refine ⟨5687039698558926873390785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791359799039284582260523 5687039698558926873390785)
              ·
                refine ⟨4265279773919195155043089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5687039698558926873390785 4265279773919195155043089)
                ·
                  refine ⟨3198959830439396366282317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4265279773919195155043089 3198959830439396366282317)
                  ·
                    refine ⟨1199609936414773637355869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198959830439396366282317 1199609936414773637355869)
                    ·
                      rfl

theorem cell22_3504348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3504348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504348 prefixEnd_3504348 := by exact prefixLift 3504348
  have htrace : WordTrace (prefixWord ++ tailWord_3504348) baseStart_3504348 baseEnd_3504348 := by
    simpa [prefixWord, tailWord_3504348, baseEnd_3504348] using wordTrace_append hprefix tailTrace_3504348
  have hstable : (prefixWord ++ tailWord_3504348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504348).length < 2 ^ (prefixWord ++ tailWord_3504348).sum := by decide
  have hdescent : baseEnd_3504348 < baseStart_3504348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504359 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 3, 3]
def baseStart_3504359 : Nat := 118140960795 + 3504359 * 2 ^ 59
def prefixEnd_3504359 : Nat := 4983230072969 + 3 ^ 40 * 3504359 * 2
def baseEnd_3504359 : Nat := 1199613701939573275330835

theorem tailTrace_3504359 : CollatzResearch.WordTrace tailWord_3504359 prefixEnd_3504359 1199613701939573275330835 := by
  unfold tailWord_3504359
  simp only [CollatzResearch.WordTrace]
  refine ⟨127814473111313314713540131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85209648740875543142360087 127814473111313314713540131)
  ·
    refine ⟨191721709666969972070310197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127814473111313314713540131 191721709666969972070310197)
    ·
      refine ⟨17973910281278434881591581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191721709666969972070310197 17973910281278434881591581)
      ·
        refine ⟨6740216355479413080596843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17973910281278434881591581 6740216355479413080596843)
        ·
          refine ⟨10110324533219119620895265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740216355479413080596843 10110324533219119620895265)
          ·
            refine ⟨7582743399914339715671449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10110324533219119620895265 7582743399914339715671449)
            ·
              refine ⟨5687057549935754786753587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7582743399914339715671449 5687057549935754786753587)
              ·
                refine ⟨8530586324903632180130381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687057549935754786753587 8530586324903632180130381)
                ·
                  refine ⟨3198969871838862067548893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8530586324903632180130381 3198969871838862067548893)
                  ·
                    refine ⟨1199613701939573275330835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198969871838862067548893 1199613701939573275330835)
                    ·
                      rfl

theorem cell22_3504359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_3504359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504359 prefixEnd_3504359 := by exact prefixLift 3504359
  have htrace : WordTrace (prefixWord ++ tailWord_3504359) baseStart_3504359 baseEnd_3504359 := by
    simpa [prefixWord, tailWord_3504359, baseEnd_3504359] using wordTrace_append hprefix tailTrace_3504359
  have hstable : (prefixWord ++ tailWord_3504359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504359).length < 2 ^ (prefixWord ++ tailWord_3504359).sum := by decide
  have hdescent : baseEnd_3504359 < baseStart_3504359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504417 : List Nat := [1, 2, 3, 2, 1, 1, 2, 6, 4]
def baseStart_3504417 : Nat := 118140960795 + 3504417 * 2 ^ 59
def prefixEnd_3504417 : Nat := 4983230072969 + 3 ^ 40 * 3504417 * 2
def baseEnd_3504417 : Nat := 399877852174960152460219

theorem tailTrace_3504417 : CollatzResearch.WordTrace tailWord_3504417 prefixEnd_3504417 399877852174960152460219 := by
  unfold tailWord_3504417
  simp only [CollatzResearch.WordTrace]
  refine ⟨127816588545103190619151505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85211059030068793746101003 127816588545103190619151505)
  ·
    refine ⟨95862441408827392964363629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127816588545103190619151505 95862441408827392964363629)
    ·
      refine ⟨35948415528310272361636361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95862441408827392964363629 35948415528310272361636361)
      ·
        refine ⟨26961311646232704271227271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35948415528310272361636361 26961311646232704271227271)
        ·
          refine ⟨40441967469349056406840907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26961311646232704271227271 40441967469349056406840907)
          ·
            refine ⟨60662951204023584610261361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40441967469349056406840907 60662951204023584610261361)
            ·
              refine ⟨45497213403017688457696021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60662951204023584610261361 45497213403017688457696021)
              ·
                refine ⟨2132681878266454146454501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45497213403017688457696021 2132681878266454146454501)
                ·
                  refine ⟨399877852174960152460219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132681878266454146454501 399877852174960152460219)
                  ·
                    rfl

theorem cell22_3504417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 4].length) (baseStart_3504417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504417 prefixEnd_3504417 := by exact prefixLift 3504417
  have htrace : WordTrace (prefixWord ++ tailWord_3504417) baseStart_3504417 baseEnd_3504417 := by
    simpa [prefixWord, tailWord_3504417, baseEnd_3504417] using wordTrace_append hprefix tailTrace_3504417
  have hstable : (prefixWord ++ tailWord_3504417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504417).length < 2 ^ (prefixWord ++ tailWord_3504417).sum := by decide
  have hdescent : baseEnd_3504417 < baseStart_3504417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504436 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3504436 : Nat := 118140960795 + 3504436 * 2 ^ 59
def prefixEnd_3504436 : Nat := 4983230072969 + 3 ^ 40 * 3504436 * 2
def baseEnd_3504436 : Nat := 1199640060613170741155599

theorem tailTrace_3504436 : CollatzResearch.WordTrace tailWord_3504436 prefixEnd_3504436 1199640060613170741155599 := by
  unfold tailWord_3504436
  simp only [CollatzResearch.WordTrace]
  refine ⟨63908640766017178432046581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85211521021356237909395441 63908640766017178432046581)
  ·
    refine ⟨5991435071814110478004367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63908640766017178432046581 5991435071814110478004367)
    ·
      refine ⟨8987152607721165717006551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5991435071814110478004367 8987152607721165717006551)
      ·
        refine ⟨13480728911581748575509827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8987152607721165717006551 13480728911581748575509827)
        ·
          refine ⟨20221093367372622863264741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13480728911581748575509827 20221093367372622863264741)
          ·
            refine ⟨3791455006382366786862139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20221093367372622863264741 3791455006382366786862139)
            ·
              refine ⟨5687182509573550180293209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791455006382366786862139 5687182509573550180293209)
              ·
                refine ⟨4265386882180162635219907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5687182509573550180293209 4265386882180162635219907)
                ·
                  refine ⟨6398080323270243952829861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265386882180162635219907 6398080323270243952829861)
                  ·
                    refine ⟨1199640060613170741155599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6398080323270243952829861 1199640060613170741155599)
                    ·
                      rfl

theorem cell22_3504436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3504436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504436 prefixEnd_3504436 := by exact prefixLift 3504436
  have htrace : WordTrace (prefixWord ++ tailWord_3504436) baseStart_3504436 baseEnd_3504436 := by
    simpa [prefixWord, tailWord_3504436, baseEnd_3504436] using wordTrace_append hprefix tailTrace_3504436
  have hstable : (prefixWord ++ tailWord_3504436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504436).length < 2 ^ (prefixWord ++ tailWord_3504436).sum := by decide
  have hdescent : baseEnd_3504436 < baseStart_3504436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504447 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 2, 4]
def baseStart_3504447 : Nat := 118140960795 + 3504447 * 2 ^ 59
def prefixEnd_3504447 : Nat := 4983230072969 + 3 ^ 40 * 3504447 * 2
def baseEnd_3504447 : Nat := 1199643826137970379130565

theorem tailTrace_3504447 : CollatzResearch.WordTrace tailWord_3504447 prefixEnd_3504447 1199643826137970379130565 := by
  unfold tailWord_3504447
  simp only [CollatzResearch.WordTrace]
  refine ⟨127817682734994505742743595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85211788489996337161829063 127817682734994505742743595)
  ·
    refine ⟨191726524102491758614115393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127817682734994505742743595 191726524102491758614115393)
    ·
      refine ⟨143794893076868818960586545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191726524102491758614115393 143794893076868818960586545)
      ·
        refine ⟨107846169807651614220439909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143794893076868818960586545 107846169807651614220439909)
        ·
          refine ⟨20221156838934677666332483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107846169807651614220439909 20221156838934677666332483)
          ·
            refine ⟨30331735258402016499498725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20221156838934677666332483 30331735258402016499498725)
            ·
              refine ⟨5687200360950378093656011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30331735258402016499498725 5687200360950378093656011)
              ·
                refine ⟨8530800541425567140484017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687200360950378093656011 8530800541425567140484017)
                ·
                  refine ⟨6398100406069175355363013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8530800541425567140484017 6398100406069175355363013)
                  ·
                    refine ⟨1199643826137970379130565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6398100406069175355363013 1199643826137970379130565)
                    ·
                      rfl

theorem cell22_3504447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_3504447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504447 prefixEnd_3504447 := by exact prefixLift 3504447
  have htrace : WordTrace (prefixWord ++ tailWord_3504447) baseStart_3504447 baseEnd_3504447 := by
    simpa [prefixWord, tailWord_3504447, baseEnd_3504447] using wordTrace_append hprefix tailTrace_3504447
  have hstable : (prefixWord ++ tailWord_3504447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504447).length < 2 ^ (prefixWord ++ tailWord_3504447).sum := by decide
  have hdescent : baseEnd_3504447 < baseStart_3504447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504449 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3504449 : Nat := 118140960795 + 3504449 * 2 ^ 59
def prefixEnd_3504449 : Nat := 4983230072969 + 3 ^ 40 * 3504449 * 2
def baseEnd_3504449 : Nat := 1199644510778843040580559

theorem tailTrace_3504449 : CollatzResearch.WordTrace tailWord_3504449 prefixEnd_3504449 1199644510778843040580559 := by
  unfold tailWord_3504449
  simp only [CollatzResearch.WordTrace]
  refine ⟨127817755680987260084316401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85211837120658173389544267 127817755680987260084316401)
  ·
    refine ⟨95863316760740445063237301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127817755680987260084316401 95863316760740445063237301)
    ·
      refine ⟨8987185946319416724678497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95863316760740445063237301 8987185946319416724678497)
      ·
        refine ⟨6740389459739562543508873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8987185946319416724678497 6740389459739562543508873)
        ·
          refine ⟨5055292094804671907631655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6740389459739562543508873 5055292094804671907631655)
          ·
            refine ⟨7582938142207007861447483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055292094804671907631655 7582938142207007861447483)
            ·
              refine ⟨11374407213310511792171225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7582938142207007861447483 11374407213310511792171225)
              ·
                refine ⟨8530805409982883844128419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11374407213310511792171225 8530805409982883844128419)
                ·
                  refine ⟨12796208114974325766192629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8530805409982883844128419 12796208114974325766192629)
                  ·
                    refine ⟨1199644510778843040580559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12796208114974325766192629 1199644510778843040580559)
                    ·
                      rfl

theorem cell22_3504449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3504449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504449 prefixEnd_3504449 := by exact prefixLift 3504449
  have htrace : WordTrace (prefixWord ++ tailWord_3504449) baseStart_3504449 baseEnd_3504449 := by
    simpa [prefixWord, tailWord_3504449, baseEnd_3504449] using wordTrace_append hprefix tailTrace_3504449
  have hstable : (prefixWord ++ tailWord_3504449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504449).length < 2 ^ (prefixWord ++ tailWord_3504449).sum := by decide
  have hdescent : baseEnd_3504449 < baseStart_3504449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504505 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_3504505 : Nat := 118140960795 + 3504505 * 2 ^ 59
def prefixEnd_3504505 : Nat := 4983230072969 + 3 ^ 40 * 3504505 * 2
def baseEnd_3504505 : Nat := 1199663680723277561180387

theorem tailTrace_3504505 : CollatzResearch.WordTrace tailWord_3504505 prefixEnd_3504505 1199663680723277561180387 := by
  unfold tailWord_3504505
  simp only [CollatzResearch.WordTrace]
  refine ⟨127819798168784381648354969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85213198779189587765569979 127819798168784381648354969)
  ·
    refine ⟨95864848626588286236266227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127819798168784381648354969 95864848626588286236266227)
    ·
      refine ⟨143797272939882429354399341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95864848626588286236266227 143797272939882429354399341)
      ·
        refine ⟨53923977352455911007899753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143797272939882429354399341 53923977352455911007899753)
        ·
          refine ⟨40442983014341933255924815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53923977352455911007899753 40442983014341933255924815)
          ·
            refine ⟨60664474521512899883887223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40442983014341933255924815 60664474521512899883887223)
            ·
              refine ⟨90996711782269349825830835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60664474521512899883887223 90996711782269349825830835)
              ·
                refine ⟨136495067673404024738746253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90996711782269349825830835 136495067673404024738746253)
                ·
                  refine ⟨51185650377526509277029845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136495067673404024738746253 51185650377526509277029845)
                  ·
                    refine ⟨1199663680723277561180387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51185650377526509277029845 1199663680723277561180387)
                    ·
                      rfl

theorem cell22_3504505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_3504505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504505 prefixEnd_3504505 := by exact prefixLift 3504505
  have htrace : WordTrace (prefixWord ++ tailWord_3504505) baseStart_3504505 baseEnd_3504505 := by
    simpa [prefixWord, tailWord_3504505, baseEnd_3504505] using wordTrace_append hprefix tailTrace_3504505
  have hstable : (prefixWord ++ tailWord_3504505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504505).length < 2 ^ (prefixWord ++ tailWord_3504505).sum := by decide
  have hdescent : baseEnd_3504505 < baseStart_3504505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504524 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 5]
def baseStart_3504524 : Nat := 118140960795 + 3504524 * 2 ^ 59
def prefixEnd_3504524 : Nat := 4983230072969 + 3 ^ 40 * 3504524 * 2
def baseEnd_3504524 : Nat := 399890061603855948318443

theorem tailTrace_3504524 : CollatzResearch.WordTrace tailWord_3504524 prefixEnd_3504524 399890061603855948318443 := by
  unfold tailWord_3504524
  simp only [CollatzResearch.WordTrace]
  refine ⟨63910245577857773946648313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85213660770477031928864417 63910245577857773946648313)
  ·
    refine ⟨47932684183393330459986235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63910245577857773946648313 47932684183393330459986235)
    ·
      refine ⟨71899026275089995689979353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47932684183393330459986235 71899026275089995689979353)
      ·
        refine ⟨53924269706317496767484515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71899026275089995689979353 53924269706317496767484515)
        ·
          refine ⟨80886404559476245151226773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53924269706317496767484515 80886404559476245151226773)
          ·
            refine ⟨3791550213725448991463755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80886404559476245151226773 3791550213725448991463755)
            ·
              refine ⟨5687325320588173487195633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791550213725448991463755 5687325320588173487195633)
              ·
                refine ⟨4265493990441130115396725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5687325320588173487195633 4265493990441130115396725)
                ·
                  refine ⟨399890061603855948318443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265493990441130115396725 399890061603855948318443)
                  ·
                    rfl

theorem cell22_3504524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_3504524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504524 prefixEnd_3504524 := by exact prefixLift 3504524
  have htrace : WordTrace (prefixWord ++ tailWord_3504524) baseStart_3504524 baseEnd_3504524 := by
    simpa [prefixWord, tailWord_3504524, baseEnd_3504524] using wordTrace_append hprefix tailTrace_3504524
  have hstable : (prefixWord ++ tailWord_3504524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504524).length < 2 ^ (prefixWord ++ tailWord_3504524).sum := by decide
  have hdescent : baseEnd_3504524 < baseStart_3504524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504541 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 5]
def baseStart_3504541 : Nat := 118140960795 + 3504541 * 2 ^ 59
def prefixEnd_3504541 : Nat := 4983230072969 + 3 ^ 40 * 3504541 * 2
def baseEnd_3504541 : Nat := 399892001419661822426759

theorem tailTrace_3504541 : CollatzResearch.WordTrace tailWord_3504541 prefixEnd_3504541 399892001419661822426759 := by
  unfold tailWord_3504541
  simp only [CollatzResearch.WordTrace]
  refine ⟨127821111196653959796665477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85214074131102639864443651 127821111196653959796665477)
  ·
    refine ⟨23966458349372617461874777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127821111196653959796665477 23966458349372617461874777)
    ·
      refine ⟨17974843762029463096406083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23966458349372617461874777 17974843762029463096406083)
      ·
        refine ⟨26962265643044194644609125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17974843762029463096406083 26962265643044194644609125)
        ·
          refine ⟨5055424808070786495864211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26962265643044194644609125 5055424808070786495864211)
          ·
            refine ⟨7583137212106179743796317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055424808070786495864211 7583137212106179743796317)
            ·
              refine ⟨2843676454539817403923619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7583137212106179743796317 2843676454539817403923619)
              ·
                refine ⟨4265514681809726105885429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843676454539817403923619 4265514681809726105885429)
                ·
                  refine ⟨399892001419661822426759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265514681809726105885429 399892001419661822426759)
                  ·
                    rfl

theorem cell22_3504541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_3504541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504541 prefixEnd_3504541 := by exact prefixLift 3504541
  have htrace : WordTrace (prefixWord ++ tailWord_3504541) baseStart_3504541 baseEnd_3504541 := by
    simpa [prefixWord, tailWord_3504541, baseEnd_3504541] using wordTrace_append hprefix tailTrace_3504541
  have hstable : (prefixWord ++ tailWord_3504541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504541).length < 2 ^ (prefixWord ++ tailWord_3504541).sum := by decide
  have hdescent : baseEnd_3504541 < baseStart_3504541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504584 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 4, 3]
def baseStart_3504584 : Nat := 118140960795 + 3504584 * 2 ^ 59
def prefixEnd_3504584 : Nat := 4983230072969 + 3 ^ 40 * 3504584 * 2
def baseEnd_3504584 : Nat := 1199690724037747688455145

theorem tailTrace_3504584 : CollatzResearch.WordTrace tailWord_3504584 prefixEnd_3504584 1199690724037747688455145 := by
  unfold tailWord_3504584
  simp only [CollatzResearch.WordTrace]
  refine ⟨63911339767749089070240403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85215119690332118760320537 63911339767749089070240403)
  ·
    refine ⟨95867009651623633605360605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63911339767749089070240403 95867009651623633605360605)
    ·
      refine ⟨35950128619358862602010227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95867009651623633605360605 35950128619358862602010227)
      ·
        refine ⟨53925192929038293903015341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35950128619358862602010227 53925192929038293903015341)
        ·
          refine ⟨20221947348389360213630753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53925192929038293903015341 20221947348389360213630753)
          ·
            refine ⟨15166460511292020160223065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20221947348389360213630753 15166460511292020160223065)
            ·
              refine ⟨11374845383469015120167299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15166460511292020160223065 11374845383469015120167299)
              ·
                refine ⟨17062268075203522680250949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11374845383469015120167299 17062268075203522680250949)
                ·
                  refine ⟨3199175264100660502547053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17062268075203522680250949 3199175264100660502547053)
                  ·
                    refine ⟨1199690724037747688455145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3199175264100660502547053 1199690724037747688455145)
                    ·
                      rfl

theorem cell22_3504584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_3504584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504584 prefixEnd_3504584 := by exact prefixLift 3504584
  have htrace : WordTrace (prefixWord ++ tailWord_3504584) baseStart_3504584 baseEnd_3504584 := by
    simpa [prefixWord, tailWord_3504584, baseEnd_3504584] using wordTrace_append hprefix tailTrace_3504584
  have hstable : (prefixWord ++ tailWord_3504584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504584).length < 2 ^ (prefixWord ++ tailWord_3504584).sum := by decide
  have hdescent : baseEnd_3504584 < baseStart_3504584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504586 : List Nat := [3, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_3504586 : Nat := 118140960795 + 3504586 * 2 ^ 59
def prefixEnd_3504586 : Nat := 4983230072969 + 3 ^ 40 * 3504586 * 2
def baseEnd_3504586 : Nat := 399897136226206783301713

theorem tailTrace_3504586 : CollatzResearch.WordTrace tailWord_3504586 prefixEnd_3504586 399897136226206783301713 := by
  unfold tailWord_3504586
  simp only [CollatzResearch.WordTrace]
  refine ⟨31955688120372733120513403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85215168320993954988035741 31955688120372733120513403)
  ·
    refine ⟨47933532180559099680770105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31955688120372733120513403 47933532180559099680770105)
    ·
      refine ⟨35950149135419324760577579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47933532180559099680770105 35950149135419324760577579)
      ·
        refine ⟨53925223703128987140866369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35950149135419324760577579 53925223703128987140866369)
        ·
          refine ⟨40443917777346740355649777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53925223703128987140866369 40443917777346740355649777)
          ·
            refine ⟨30332938333010055266737333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40443917777346740355649777 30332938333010055266737333)
            ·
              refine ⟨2843712968719692681256625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30332938333010055266737333 2843712968719692681256625)
              ·
                refine ⟨2132784726539769510942469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843712968719692681256625 2132784726539769510942469)
                ·
                  refine ⟨399897136226206783301713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132784726539769510942469 399897136226206783301713)
                  ·
                    rfl

theorem cell22_3504586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_3504586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504586 prefixEnd_3504586 := by exact prefixLift 3504586
  have htrace : WordTrace (prefixWord ++ tailWord_3504586) baseStart_3504586 baseEnd_3504586 := by
    simpa [prefixWord, tailWord_3504586, baseEnd_3504586] using wordTrace_append hprefix tailTrace_3504586
  have hstable : (prefixWord ++ tailWord_3504586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504586).length < 2 ^ (prefixWord ++ tailWord_3504586).sum := by decide
  have hdescent : baseEnd_3504586 < baseStart_3504586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504597 : List Nat := [1, 3, 2, 3, 1, 2, 1, 9]
def baseStart_3504597 : Nat := 118140960795 + 3504597 * 2 ^ 59
def prefixEnd_3504597 : Nat := 4983230072969 + 3 ^ 40 * 3504597 * 2
def baseEnd_3504597 : Nat := 133299463800379998653345

theorem tailTrace_3504597 : CollatzResearch.WordTrace tailWord_3504597 prefixEnd_3504597 133299463800379998653345 := by
  unfold tailWord_3504597
  simp only [CollatzResearch.WordTrace]
  refine ⟨127823153684451081360704045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85215435789634054240469363 127823153684451081360704045)
  ·
    refine ⟨47933682631669155510264017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127823153684451081360704045 47933682631669155510264017)
    ·
      refine ⟨35950261973751866632698013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47933682631669155510264017 35950261973751866632698013)
      ·
        refine ⟨13481348240156949987261755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35950261973751866632698013 13481348240156949987261755)
        ·
          refine ⟨20222022360235424980892633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13481348240156949987261755 20222022360235424980892633)
          ·
            refine ⟨15166516770176568735669475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20222022360235424980892633 15166516770176568735669475)
            ·
              refine ⟨22749775155264853103504213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15166516770176568735669475 22749775155264853103504213)
              ·
                refine ⟨133299463800379998653345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22749775155264853103504213 133299463800379998653345)
                ·
                  rfl

theorem cell22_3504597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 9].length) (baseStart_3504597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504597 prefixEnd_3504597 := by exact prefixLift 3504597
  have htrace : WordTrace (prefixWord ++ tailWord_3504597) baseStart_3504597 baseEnd_3504597 := by
    simpa [prefixWord, tailWord_3504597, baseEnd_3504597] using wordTrace_append hprefix tailTrace_3504597
  have hstable : (prefixWord ++ tailWord_3504597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504597).length < 2 ^ (prefixWord ++ tailWord_3504597).sum := by decide
  have hdescent : baseEnd_3504597 < baseStart_3504597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504644 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_3504644 : Nat := 118140960795 + 3504644 * 2 ^ 59
def prefixEnd_3504644 : Nat := 4983230072969 + 3 ^ 40 * 3504644 * 2
def baseEnd_3504644 : Nat := 1199711263263927531954961

theorem tailTrace_3504644 : CollatzResearch.WordTrace tailWord_3504644 prefixEnd_3504644 1199711263263927531954961 := by
  unfold tailWord_3504644
  simp only [CollatzResearch.WordTrace]
  refine ⟨63912433957640404193832493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85216578610187205591776657 63912433957640404193832493)
  ·
    refine ⟨23967162734115151572687185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63912433957640404193832493 23967162734115151572687185)
    ·
      refine ⟨17975372050586363679515389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23967162734115151572687185 17975372050586363679515389)
      ·
        refine ⟨6740764518969886379818271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17975372050586363679515389 6740764518969886379818271)
        ·
          refine ⟨10111146778454829569727407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740764518969886379818271 10111146778454829569727407)
          ·
            refine ⟨15166720167682244354591111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10111146778454829569727407 15166720167682244354591111)
            ·
              refine ⟨22750080251523366531886667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15166720167682244354591111 22750080251523366531886667)
              ·
                refine ⟨34125120377285049797830001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22750080251523366531886667 34125120377285049797830001)
                ·
                  refine ⟨25593840282963787348372501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34125120377285049797830001 25593840282963787348372501)
                  ·
                    refine ⟨1199711263263927531954961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25593840282963787348372501 1199711263263927531954961)
                    ·
                      rfl

theorem cell22_3504644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_3504644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504644 prefixEnd_3504644 := by exact prefixLift 3504644
  have htrace : WordTrace (prefixWord ++ tailWord_3504644) baseStart_3504644 baseEnd_3504644 := by
    simpa [prefixWord, tailWord_3504644, baseEnd_3504644] using wordTrace_append hprefix tailTrace_3504644
  have hstable : (prefixWord ++ tailWord_3504644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504644).length < 2 ^ (prefixWord ++ tailWord_3504644).sum := by decide
  have hdescent : baseEnd_3504644 < baseStart_3504644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504663 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 3, 3]
def baseStart_3504663 : Nat := 118140960795 + 3504663 * 2 ^ 59
def prefixEnd_3504663 : Nat := 4983230072969 + 3 ^ 40 * 3504663 * 2
def baseEnd_3504663 : Nat := 1199717767352217815729903

theorem tailTrace_3504663 : CollatzResearch.WordTrace tailWord_3504663 prefixEnd_3504663 1199717767352217815729903 := by
  unfold tailWord_3504663
  simp only [CollatzResearch.WordTrace]
  refine ⟨127825560902211974632606643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85217040601474649755071095 127825560902211974632606643)
  ·
    refine ⟨191738341353317961948909965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127825560902211974632606643 191738341353317961948909965)
    ·
      refine ⟨71901878007494235730841237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191738341353317961948909965 71901878007494235730841237)
      ·
        refine ⟨3370400531601292299883183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71901878007494235730841237 3370400531601292299883183)
        ·
          refine ⟨5055600797401938449824775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370400531601292299883183 5055600797401938449824775)
          ·
            refine ⟨7583401196102907674737163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055600797401938449824775 7583401196102907674737163)
            ·
              refine ⟨11375101794154361512105745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583401196102907674737163 11375101794154361512105745)
              ·
                refine ⟨8531326345615771134079309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11375101794154361512105745 8531326345615771134079309)
                ·
                  refine ⟨3199247379605914175279741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8531326345615771134079309 3199247379605914175279741)
                  ·
                    refine ⟨1199717767352217815729903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3199247379605914175279741 1199717767352217815729903)
                    ·
                      rfl

theorem cell22_3504663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_3504663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504663 prefixEnd_3504663 := by exact prefixLift 3504663
  have htrace : WordTrace (prefixWord ++ tailWord_3504663) baseStart_3504663 baseEnd_3504663 := by
    simpa [prefixWord, tailWord_3504663, baseEnd_3504663] using wordTrace_append hprefix tailTrace_3504663
  have hstable : (prefixWord ++ tailWord_3504663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504663).length < 2 ^ (prefixWord ++ tailWord_3504663).sum := by decide
  have hdescent : baseEnd_3504663 < baseStart_3504663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504680 : List Nat := [2, 1, 5, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3504680 : Nat := 118140960795 + 3504680 * 2 ^ 59
def prefixEnd_3504680 : Nat := 4983230072969 + 3 ^ 40 * 3504680 * 2
def baseEnd_3504680 : Nat := 1199723586799635438054851

theorem tailTrace_3504680 : CollatzResearch.WordTrace tailWord_3504680 prefixEnd_3504680 1199723586799635438054851 := by
  unfold tailWord_3504680
  simp only [CollatzResearch.WordTrace]
  refine ⟨63913090471575193267987747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85217453962100257690650329 63913090471575193267987747)
  ·
    refine ⟨95869635707362789901981621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63913090471575193267987747 95869635707362789901981621)
    ·
      refine ⟨8987778347565261553310777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95869635707362789901981621 8987778347565261553310777)
      ·
        refine ⟨6740833760673946164983083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8987778347565261553310777 6740833760673946164983083)
        ·
          refine ⟨10111250641010919247474625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740833760673946164983083 10111250641010919247474625)
          ·
            refine ⟨7583437980758189435605969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10111250641010919247474625 7583437980758189435605969)
            ·
              refine ⟨5687578485568642076704477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7583437980758189435605969 5687578485568642076704477)
              ·
                refine ⟨2132841932088240778764179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5687578485568642076704477 2132841932088240778764179)
                ·
                  refine ⟨3199262898132361168146269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132841932088240778764179 3199262898132361168146269)
                  ·
                    refine ⟨1199723586799635438054851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3199262898132361168146269 1199723586799635438054851)
                    ·
                      rfl

theorem cell22_3504680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3504680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504680 prefixEnd_3504680 := by exact prefixLift 3504680
  have htrace : WordTrace (prefixWord ++ tailWord_3504680) baseStart_3504680 baseEnd_3504680 := by
    simpa [prefixWord, tailWord_3504680, baseEnd_3504680] using wordTrace_append hprefix tailTrace_3504680
  have hstable : (prefixWord ++ tailWord_3504680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504680).length < 2 ^ (prefixWord ++ tailWord_3504680).sum := by decide
  have hdescent : baseEnd_3504680 < baseStart_3504680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504710 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3504710 : Nat := 118140960795 + 3504710 * 2 ^ 59
def prefixEnd_3504710 : Nat := 4983230072969 + 3 ^ 40 * 3504710 * 2
def baseEnd_3504710 : Nat := 399911285470908453268253

theorem tailTrace_3504710 : CollatzResearch.WordTrace tailWord_3504710 prefixEnd_3504710 399911285470908453268253 := by
  unfold tailWord_3504710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994602347907553176861487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85218183422027801106378389 3994602347907553176861487)
  ·
    refine ⟨5991903521861329765292231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3994602347907553176861487 5991903521861329765292231)
    ·
      refine ⟨8987855282791994647938347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5991903521861329765292231 8987855282791994647938347)
      ·
        refine ⟨13481782924187991971907521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8987855282791994647938347 13481782924187991971907521)
        ·
          refine ⟨10111337193140993978930641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13481782924187991971907521 10111337193140993978930641)
          ·
            refine ⟨7583502894855745484197981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10111337193140993978930641 7583502894855745484197981)
            ·
              refine ⟨2843813585570904556574243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7583502894855745484197981 2843813585570904556574243)
              ·
                refine ⟨4265720378356356834861365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843813585570904556574243 4265720378356356834861365)
                ·
                  refine ⟨399911285470908453268253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265720378356356834861365 399911285470908453268253)
                  ·
                    rfl

theorem cell22_3504710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3504710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504710 prefixEnd_3504710 := by exact prefixLift 3504710
  have htrace : WordTrace (prefixWord ++ tailWord_3504710) baseStart_3504710 baseEnd_3504710 := by
    simpa [prefixWord, tailWord_3504710, baseEnd_3504710] using wordTrace_append hprefix tailTrace_3504710
  have hstable : (prefixWord ++ tailWord_3504710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504710).length < 2 ^ (prefixWord ++ tailWord_3504710).sum := by decide
  have hdescent : baseEnd_3504710 < baseStart_3504710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504719 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 1, 5]
def baseStart_3504719 : Nat := 118140960795 + 3504719 * 2 ^ 59
def prefixEnd_3504719 : Nat := 4983230072969 + 3 ^ 40 * 3504719 * 2
def baseEnd_3504719 : Nat := 1199736937296652336329731

theorem tailTrace_3504719 : CollatzResearch.WordTrace tailWord_3504719 prefixEnd_3504719 1199736937296652336329731 := by
  unfold tailWord_3504719
  simp only [CollatzResearch.WordTrace]
  refine ⟨127827603390009096196645211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85218402260006064131096807 127827603390009096196645211)
  ·
    refine ⟨191741405085013644294967817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127827603390009096196645211 191741405085013644294967817)
    ·
      refine ⟨143806053813760233221225863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191741405085013644294967817 143806053813760233221225863)
      ·
        refine ⟨215709080720640349831838795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143806053813760233221225863 215709080720640349831838795)
        ·
          refine ⟨323563621080960524747758193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215709080720640349831838795 323563621080960524747758193)
          ·
            refine ⟨242672715810720393560818645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323563621080960524747758193 242672715810720393560818645)
            ·
              refine ⟨5687641776813759224081687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 242672715810720393560818645 5687641776813759224081687)
              ·
                refine ⟨8531462665220638836122531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687641776813759224081687 8531462665220638836122531)
                ·
                  refine ⟨12797193997830958254183797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8531462665220638836122531 12797193997830958254183797)
                  ·
                    refine ⟨1199736937296652336329731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12797193997830958254183797 1199736937296652336329731)
                    ·
                      rfl

theorem cell22_3504719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_3504719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504719 prefixEnd_3504719 := by exact prefixLift 3504719
  have htrace : WordTrace (prefixWord ++ tailWord_3504719) baseStart_3504719 baseEnd_3504719 := by
    simpa [prefixWord, tailWord_3504719, baseEnd_3504719] using wordTrace_append hprefix tailTrace_3504719
  have hstable : (prefixWord ++ tailWord_3504719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504719).length < 2 ^ (prefixWord ++ tailWord_3504719).sum := by decide
  have hdescent : baseEnd_3504719 < baseStart_3504719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504749 : List Nat := [1, 5, 1, 1, 3, 1, 10]
def baseStart_3504749 : Nat := 118140960795 + 3504749 * 2 ^ 59
def prefixEnd_3504749 : Nat := 4983230072969 + 3 ^ 40 * 3504749 * 2
def baseEnd_3504749 : Nat := 44435081737397861410357

theorem tailTrace_3504749 : CollatzResearch.WordTrace tailWord_3504749 prefixEnd_3504749 44435081737397861410357 := by
  unfold tailWord_3504749
  simp only [CollatzResearch.WordTrace]
  refine ⟨127828697579900411320237301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85219131719933607546824867 127828697579900411320237301)
  ·
    refine ⟨11983940398115663561272247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127828697579900411320237301 11983940398115663561272247)
    ·
      refine ⟨17975910597173495341908371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11983940398115663561272247 17975910597173495341908371)
      ·
        refine ⟨26963865895760243012862557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17975910597173495341908371 26963865895760243012862557)
        ·
          refine ⟨10111449710910091129823459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26963865895760243012862557 10111449710910091129823459)
          ·
            refine ⟨15167174566365136694735189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10111449710910091129823459 15167174566365136694735189)
            ·
              refine ⟨44435081737397861410357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15167174566365136694735189 44435081737397861410357)
              ·
                rfl

theorem cell22_3504749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 10].length) (baseStart_3504749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504749 prefixEnd_3504749 := by exact prefixLift 3504749
  have htrace : WordTrace (prefixWord ++ tailWord_3504749) baseStart_3504749 baseEnd_3504749 := by
    simpa [prefixWord, tailWord_3504749, baseEnd_3504749] using wordTrace_append hprefix tailTrace_3504749
  have hstable : (prefixWord ++ tailWord_3504749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504749).length < 2 ^ (prefixWord ++ tailWord_3504749).sum := by decide
  have hdescent : baseEnd_3504749 < baseStart_3504749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504815 : List Nat := [1, 1, 2, 1, 2, 5, 4, 2, 1, 3]
def baseStart_3504815 : Nat := 118140960795 + 3504815 * 2 ^ 59
def prefixEnd_3504815 : Nat := 4983230072969 + 3 ^ 40 * 3504815 * 2
def baseEnd_3504815 : Nat := 1199769800058540085929437

theorem tailTrace_3504815 : CollatzResearch.WordTrace tailWord_3504815 prefixEnd_3504815 1199769800058540085929437 := by
  unfold tailWord_3504815
  simp only [CollatzResearch.WordTrace]
  refine ⟨127831104797661304592139899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85220736531774203061426599 127831104797661304592139899)
  ·
    refine ⟨191746657196491956888209849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127831104797661304592139899 191746657196491956888209849)
    ·
      refine ⟨143809992897368967666157387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191746657196491956888209849 143809992897368967666157387)
      ·
        refine ⟨215714989346053451499236081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143809992897368967666157387 215714989346053451499236081)
        ·
          refine ⟨161786242009540088624427061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215714989346053451499236081 161786242009540088624427061)
          ·
            refine ⟨15167460188394383308540037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161786242009540088624427061 15167460188394383308540037)
            ·
              refine ⟨2843898785323946870351257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15167460188394383308540037 2843898785323946870351257)
              ·
                refine ⟨2132924088992960152763443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843898785323946870351257 2132924088992960152763443)
                ·
                  refine ⟨3199386133489440229145165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132924088992960152763443 3199386133489440229145165)
                  ·
                    refine ⟨1199769800058540085929437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3199386133489440229145165 1199769800058540085929437)
                    ·
                      rfl

theorem cell22_3504815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 3].length) (baseStart_3504815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504815 prefixEnd_3504815 := by exact prefixLift 3504815
  have htrace : WordTrace (prefixWord ++ tailWord_3504815) baseStart_3504815 baseEnd_3504815 := by
    simpa [prefixWord, tailWord_3504815, baseEnd_3504815] using wordTrace_append hprefix tailTrace_3504815
  have hstable : (prefixWord ++ tailWord_3504815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504815).length < 2 ^ (prefixWord ++ tailWord_3504815).sum := by decide
  have hdescent : baseEnd_3504815 < baseStart_3504815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504886 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3504886 : Nat := 118140960795 + 3504886 * 2 ^ 59
def prefixEnd_3504886 : Nat := 4983230072969 + 3 ^ 40 * 3504886 * 2
def baseEnd_3504886 : Nat := 1199794104809519567404219

theorem tailTrace_3504886 : CollatzResearch.WordTrace tailWord_3504886 prefixEnd_3504886 1199794104809519567404219 := by
  unfold tailWord_3504886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7989605898775255232373407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85222462920269389145316341 7989605898775255232373407)
  ·
    refine ⟨11984408848162882848560111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7989605898775255232373407 11984408848162882848560111)
    ·
      refine ⟨17976613272244324272840167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11984408848162882848560111 17976613272244324272840167)
      ·
        refine ⟨26964919908366486409260251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17976613272244324272840167 26964919908366486409260251)
        ·
          refine ⟨40447379862549729613890377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26964919908366486409260251 40447379862549729613890377)
          ·
            refine ⟨30335534896912297210417783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40447379862549729613890377 30335534896912297210417783)
            ·
              refine ⟨45503302345368445815626675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30335534896912297210417783 45503302345368445815626675)
              ·
                refine ⟨68254953518052668723440013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45503302345368445815626675 68254953518052668723440013)
                ·
                  refine ⟨25595607569269750771290005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68254953518052668723440013 25595607569269750771290005)
                  ·
                    refine ⟨1199794104809519567404219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25595607569269750771290005 1199794104809519567404219)
                    ·
                      rfl

theorem cell22_3504886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3504886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504886 prefixEnd_3504886 := by exact prefixLift 3504886
  have htrace : WordTrace (prefixWord ++ tailWord_3504886) baseStart_3504886 baseEnd_3504886 := by
    simpa [prefixWord, tailWord_3504886, baseEnd_3504886] using wordTrace_append hprefix tailTrace_3504886
  have hstable : (prefixWord ++ tailWord_3504886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504886).length < 2 ^ (prefixWord ++ tailWord_3504886).sum := by decide
  have hdescent : baseEnd_3504886 < baseStart_3504886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504899 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 1, 9]
def baseStart_3504899 : Nat := 118140960795 + 3504899 * 2 ^ 59
def prefixEnd_3504899 : Nat := 4983230072969 + 3 ^ 40 * 3504899 * 2
def baseEnd_3504899 : Nat := 1199798554975191866829179

theorem tailTrace_3504899 : CollatzResearch.WordTrace tailWord_3504899 prefixEnd_3504899 1199798554975191866829179 := by
  unfold tailWord_3504899
  simp only [CollatzResearch.WordTrace]
  refine ⟨127834168529356986938197751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85222779019571324625465167 127834168529356986938197751)
  ·
    refine ⟨191751252794035480407296627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127834168529356986938197751 191751252794035480407296627)
    ·
      refine ⟨287626879191053220610944941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191751252794035480407296627 287626879191053220610944941)
      ·
        refine ⟨107860079696644957729104353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287626879191053220610944941 107860079696644957729104353)
        ·
          refine ⟨80895059772483718296828265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107860079696644957729104353 80895059772483718296828265)
          ·
            refine ⟨60671294829362788722621199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80895059772483718296828265 60671294829362788722621199)
            ·
              refine ⟨91006942244044183083931799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60671294829362788722621199 91006942244044183083931799)
              ·
                refine ⟨136510413366066274625897699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91006942244044183083931799 136510413366066274625897699)
                ·
                  refine ⟨204765620049099411938846549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136510413366066274625897699 204765620049099411938846549)
                  ·
                    refine ⟨1199798554975191866829179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 204765620049099411938846549 1199798554975191866829179)
                    ·
                      rfl

theorem cell22_3504899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_3504899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504899 prefixEnd_3504899 := by exact prefixLift 3504899
  have htrace : WordTrace (prefixWord ++ tailWord_3504899) baseStart_3504899 baseEnd_3504899 := by
    simpa [prefixWord, tailWord_3504899, baseEnd_3504899] using wordTrace_append hprefix tailTrace_3504899
  have hstable : (prefixWord ++ tailWord_3504899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504899).length < 2 ^ (prefixWord ++ tailWord_3504899).sum := by decide
  have hdescent : baseEnd_3504899 < baseStart_3504899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504980 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 5]
def baseStart_3504980 : Nat := 118140960795 + 3504980 * 2 ^ 59
def prefixEnd_3504980 : Nat := 4983230072969 + 3 ^ 40 * 3504980 * 2
def baseEnd_3504980 : Nat := 399942094310178218517977

theorem tailTrace_3504980 : CollatzResearch.WordTrace tailWord_3504980 prefixEnd_3504980 399942094310178218517977 := by
  unfold tailWord_3504980
  simp only [CollatzResearch.WordTrace]
  refine ⟨63918561421031768885948197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85224748561375691847930929 63918561421031768885948197)
  ·
    refine ⟨11984730266443456666115287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63918561421031768885948197 11984730266443456666115287)
    ·
      refine ⟨17977095399665184999172931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11984730266443456666115287 17977095399665184999172931)
      ·
        refine ⟨26965643099497777498759397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17977095399665184999172931 26965643099497777498759397)
        ·
          refine ⟨5056058081155833281017387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26965643099497777498759397 5056058081155833281017387)
          ·
            refine ⟨7584087121733749921526081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056058081155833281017387 7584087121733749921526081)
            ·
              refine ⟨5688065341300312441144561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7584087121733749921526081 5688065341300312441144561)
              ·
                refine ⟨4266049005975234330858421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5688065341300312441144561 4266049005975234330858421)
                ·
                  refine ⟨399942094310178218517977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4266049005975234330858421 399942094310178218517977)
                  ·
                    rfl

theorem cell22_3504980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_3504980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504980 prefixEnd_3504980 := by exact prefixLift 3504980
  have htrace : WordTrace (prefixWord ++ tailWord_3504980) baseStart_3504980 baseEnd_3504980 := by
    simpa [prefixWord, tailWord_3504980, baseEnd_3504980] using wordTrace_append hprefix tailTrace_3504980
  have hstable : (prefixWord ++ tailWord_3504980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504980).length < 2 ^ (prefixWord ++ tailWord_3504980).sum := by decide
  have hdescent : baseEnd_3504980 < baseStart_3504980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504991 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 6]
def baseStart_3504991 : Nat := 118140960795 + 3504991 * 2 ^ 59
def prefixEnd_3504991 : Nat := 4983230072969 + 3 ^ 40 * 3504991 * 2
def baseEnd_3504991 : Nat := 399943349485111431176299

theorem tailTrace_3504991 : CollatzResearch.WordTrace tailWord_3504991 prefixEnd_3504991 399943349485111431176299 := by
  unfold tailWord_3504991
  simp only [CollatzResearch.WordTrace]
  refine ⟨127837524045023686650546827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85225016030015791100364551 127837524045023686650546827)
  ·
    refine ⟨191756286067535529975820241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127837524045023686650546827 191756286067535529975820241)
    ·
      refine ⟨143817214550651647481865181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191756286067535529975820241 143817214550651647481865181)
      ·
        refine ⟨53931455456494367805699443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143817214550651647481865181 53931455456494367805699443)
        ·
          refine ⟨80897183184741551708549165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53931455456494367805699443 80897183184741551708549165)
          ·
            refine ⟨30336443694278081890705937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80897183184741551708549165 30336443694278081890705937)
            ·
              refine ⟨22752332770708561418029453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30336443694278081890705937 22752332770708561418029453)
              ·
                refine ⟨8532124789015710531761045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22752332770708561418029453 8532124789015710531761045)
                ·
                  refine ⟨399943349485111431176299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8532124789015710531761045 399943349485111431176299)
                  ·
                    rfl

theorem cell22_3504991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 6].length) (baseStart_3504991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3504991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3504991 prefixEnd_3504991 := by exact prefixLift 3504991
  have htrace : WordTrace (prefixWord ++ tailWord_3504991) baseStart_3504991 baseEnd_3504991 := by
    simpa [prefixWord, tailWord_3504991, baseEnd_3504991] using wordTrace_append hprefix tailTrace_3504991
  have hstable : (prefixWord ++ tailWord_3504991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504991).length < 2 ^ (prefixWord ++ tailWord_3504991).sum := by decide
  have hdescent : baseEnd_3504991 < baseStart_3504991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505098 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_3505098 : Nat := 118140960795 + 3505098 * 2 ^ 59
def prefixEnd_3505098 : Nat := 4983230072969 + 3 ^ 40 * 3505098 * 2
def baseEnd_3505098 : Nat := 399955558914007227034523

theorem tailTrace_3505098 : CollatzResearch.WordTrace tailWord_3505098 prefixEnd_3505098 399955558914007227034523 := by
  unfold tailWord_3505098
  simp only [CollatzResearch.WordTrace]
  refine ⟨31960356663909010981172987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85227617770424029283127965 31960356663909010981172987)
  ·
    refine ⟨47940534995863516471759481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31960356663909010981172987 47940534995863516471759481)
    ·
      refine ⟨35955401246897637353819611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47940534995863516471759481 35955401246897637353819611)
      ·
        refine ⟨53933101870346456030729417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35955401246897637353819611 53933101870346456030729417)
        ·
          refine ⟨40449826402759842023047063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53933101870346456030729417 40449826402759842023047063)
          ·
            refine ⟨60674739604139763034570595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40449826402759842023047063 60674739604139763034570595)
            ·
              refine ⟨91012109406209644551855893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60674739604139763034570595 91012109406209644551855893)
              ·
                refine ⟨4266192628416077088368245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91012109406209644551855893 4266192628416077088368245)
                ·
                  refine ⟨399955558914007227034523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4266192628416077088368245 399955558914007227034523)
                  ·
                    rfl

theorem cell22_3505098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_3505098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505098 prefixEnd_3505098 := by exact prefixLift 3505098
  have htrace : WordTrace (prefixWord ++ tailWord_3505098) baseStart_3505098 baseEnd_3505098 := by
    simpa [prefixWord, tailWord_3505098, baseEnd_3505098] using wordTrace_append hprefix tailTrace_3505098
  have hstable : (prefixWord ++ tailWord_3505098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505098).length < 2 ^ (prefixWord ++ tailWord_3505098).sum := by decide
  have hdescent : baseEnd_3505098 < baseStart_3505098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505102 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_3505102 : Nat := 118140960795 + 3505102 * 2 ^ 59
def prefixEnd_3505102 : Nat := 4983230072969 + 3 ^ 40 * 3505102 * 2
def baseEnd_3505102 : Nat := 1199868046023767004003557

theorem tailTrace_3505102 : CollatzResearch.WordTrace tailWord_3505102 prefixEnd_3505102 1199868046023767004003557 := by
  unfold tailWord_3505102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15980196568452694075979695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85227715031747701738558373 15980196568452694075979695)
  ·
    refine ⟨23970294852679041113969543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15980196568452694075979695 23970294852679041113969543)
    ·
      refine ⟨35955442279018561670954315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23970294852679041113969543 35955442279018561670954315)
      ·
        refine ⟨53933163418527842506431473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35955442279018561670954315 53933163418527842506431473)
        ·
          refine ⟨40449872563895881879823605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53933163418527842506431473 40449872563895881879823605)
          ·
            refine ⟨3792175552865238926233463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40449872563895881879823605 3792175552865238926233463)
            ·
              refine ⟨5688263329297858389350195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792175552865238926233463 5688263329297858389350195)
              ·
                refine ⟨8532394993946787584025293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688263329297858389350195 8532394993946787584025293)
                ·
                  refine ⟨3199648122730045344009485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8532394993946787584025293 3199648122730045344009485)
                  ·
                    refine ⟨1199868046023767004003557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3199648122730045344009485 1199868046023767004003557)
                    ·
                      rfl

theorem cell22_3505102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_3505102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505102 prefixEnd_3505102 := by exact prefixLift 3505102
  have htrace : WordTrace (prefixWord ++ tailWord_3505102) baseStart_3505102 baseEnd_3505102 := by
    simpa [prefixWord, tailWord_3505102, baseEnd_3505102] using wordTrace_append hprefix tailTrace_3505102
  have hstable : (prefixWord ++ tailWord_3505102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505102).length < 2 ^ (prefixWord ++ tailWord_3505102).sum := by decide
  have hdescent : baseEnd_3505102 < baseStart_3505102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505175 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 1, 5]
def baseStart_3505175 : Nat := 118140960795 + 3505175 * 2 ^ 59
def prefixEnd_3505175 : Nat := 4983230072969 + 3 ^ 40 * 3505175 * 2
def baseEnd_3505175 : Nat := 1199893035415619146928333

theorem tailTrace_3505175 : CollatzResearch.WordTrace tailWord_3505175 prefixEnd_3505175 1199893035415619146928333 := by
  unfold tailWord_3505175
  simp only [CollatzResearch.WordTrace]
  refine ⟨127844235076357086075244979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85229490050904724050163319 127844235076357086075244979)
  ·
    refine ⟨191766352614535629112867469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127844235076357086075244979 191766352614535629112867469)
    ·
      refine ⟨71912382230450860917325301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191766352614535629112867469 71912382230450860917325301)
      ·
        refine ⟨6741785834104768210999247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71912382230450860917325301 6741785834104768210999247)
        ·
          refine ⟨10112678751157152316498871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741785834104768210999247 10112678751157152316498871)
          ·
            refine ⟨15169018126735728474748307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10112678751157152316498871 15169018126735728474748307)
            ·
              refine ⟨22753527190103592712122461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15169018126735728474748307 22753527190103592712122461)
              ·
                refine ⟨8532572696288847267045923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22753527190103592712122461 8532572696288847267045923)
                ·
                  refine ⟨12798859044433270900568885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8532572696288847267045923 12798859044433270900568885)
                  ·
                    refine ⟨1199893035415619146928333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12798859044433270900568885 1199893035415619146928333)
                    ·
                      rfl

theorem cell22_3505175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_3505175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505175 prefixEnd_3505175 := by exact prefixLift 3505175
  have htrace : WordTrace (prefixWord ++ tailWord_3505175) baseStart_3505175 baseEnd_3505175 := by
    simpa [prefixWord, tailWord_3505175, baseEnd_3505175] using wordTrace_append hprefix tailTrace_3505175
  have hstable : (prefixWord ++ tailWord_3505175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505175).length < 2 ^ (prefixWord ++ tailWord_3505175).sum := by decide
  have hdescent : baseEnd_3505175 < baseStart_3505175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505194 : List Nat := [3, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_3505194 : Nat := 118140960795 + 3505194 * 2 ^ 59
def prefixEnd_3505194 : Nat := 4983230072969 + 3 ^ 40 * 3505194 * 2
def baseEnd_3505194 : Nat := 399966513167969810234425

theorem tailTrace_3505194 : CollatzResearch.WordTrace tailWord_3505194 prefixEnd_3505194 399966513167969810234425 := by
  unfold tailWord_3505194
  simp only [CollatzResearch.WordTrace]
  refine ⟨31961232015822063080046659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85229952042192168213457757 31961232015822063080046659)
  ·
    refine ⟨47941848023733094620069989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31961232015822063080046659 47941848023733094620069989)
    ·
      refine ⟨8989096504449955241263123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47941848023733094620069989 8989096504449955241263123)
      ·
        refine ⟨13483644756674932861894685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8989096504449955241263123 13483644756674932861894685)
        ·
          refine ⟨5056366783753099823210507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13483644756674932861894685 5056366783753099823210507)
          ·
            refine ⟨7584550175629649734815761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056366783753099823210507 7584550175629649734815761)
            ·
              refine ⟨5688412631722237301111821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7584550175629649734815761 5688412631722237301111821)
              ·
                refine ⟨2133154736895838987916933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5688412631722237301111821 2133154736895838987916933)
                ·
                  refine ⟨399966513167969810234425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2133154736895838987916933 399966513167969810234425)
                  ·
                    rfl

theorem cell22_3505194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_3505194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505194 prefixEnd_3505194 := by exact prefixLift 3505194
  have htrace : WordTrace (prefixWord ++ tailWord_3505194) baseStart_3505194 baseEnd_3505194 := by
    simpa [prefixWord, tailWord_3505194, baseEnd_3505194] using wordTrace_append hprefix tailTrace_3505194
  have hstable : (prefixWord ++ tailWord_3505194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505194).length < 2 ^ (prefixWord ++ tailWord_3505194).sum := by decide
  have hdescent : baseEnd_3505194 < baseStart_3505194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505209 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 2, 3]
def baseStart_3505209 : Nat := 118140960795 + 3505209 * 2 ^ 59
def prefixEnd_3505209 : Nat := 4983230072969 + 3 ^ 40 * 3505209 * 2
def baseEnd_3505209 : Nat := 1199904674310454391578229

theorem tailTrace_3505209 : CollatzResearch.WordTrace tailWord_3505209 prefixEnd_3505209 1199904674310454391578229 := by
  unfold tailWord_3505209
  simp only [CollatzResearch.WordTrace]
  refine ⟨127845475158233909881982681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85230316772155939921321787 127845475158233909881982681)
  ·
    refine ⟨95884106368675432411487011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127845475158233909881982681 95884106368675432411487011)
    ·
      refine ⟨143826159553013148617230517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95884106368675432411487011 143826159553013148617230517)
      ·
        refine ⟨13483702458094982682865361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143826159553013148617230517 13483702458094982682865361)
        ·
          refine ⟨10112776843571237012149021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13483702458094982682865361 10112776843571237012149021)
          ·
            refine ⟨3792291316339213879555883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10112776843571237012149021 3792291316339213879555883)
            ·
              refine ⟨5688436974508820819333825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792291316339213879555883 5688436974508820819333825)
              ·
                refine ⟨4266327730881615614500369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5688436974508820819333825 4266327730881615614500369)
                ·
                  refine ⟨3199745798161211710875277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4266327730881615614500369 3199745798161211710875277)
                  ·
                    refine ⟨1199904674310454391578229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3199745798161211710875277 1199904674310454391578229)
                    ·
                      rfl

theorem cell22_3505209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_3505209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505209 prefixEnd_3505209 := by exact prefixLift 3505209
  have htrace : WordTrace (prefixWord ++ tailWord_3505209) baseStart_3505209 baseEnd_3505209 := by
    simpa [prefixWord, tailWord_3505209, baseEnd_3505209] using wordTrace_append hprefix tailTrace_3505209
  have hstable : (prefixWord ++ tailWord_3505209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505209).length < 2 ^ (prefixWord ++ tailWord_3505209).sum := by decide
  have hdescent : baseEnd_3505209 < baseStart_3505209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505284 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 5]
def baseStart_3505284 : Nat := 118140960795 + 3505284 * 2 ^ 59
def prefixEnd_3505284 : Nat := 4983230072969 + 3 ^ 40 * 3505284 * 2
def baseEnd_3505284 : Nat := 399976782781059731984333

theorem tailTrace_3505284 : CollatzResearch.WordTrace tailWord_3505284 prefixEnd_3505284 399976782781059731984333 := by
  unfold tailWord_3505284
  simp only [CollatzResearch.WordTrace]
  refine ⟨63924105316481098845481453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85232140421974798460641937 63924105316481098845481453)
  ·
    refine ⟨23971539493680412067055545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63924105316481098845481453 23971539493680412067055545)
    ·
      refine ⟨17978654620260309050291659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23971539493680412067055545 17978654620260309050291659)
      ·
        refine ⟨26967981930390463575437489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17978654620260309050291659 26967981930390463575437489)
        ·
          refine ⟨20225986447792847681578117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26967981930390463575437489 20225986447792847681578117)
          ·
            refine ⟨3792372458961158940295897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20225986447792847681578117 3792372458961158940295897)
            ·
              refine ⟨2844279344220869205221923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792372458961158940295897 2844279344220869205221923)
              ·
                refine ⟨4266419016331303807832885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844279344220869205221923 4266419016331303807832885)
                ·
                  refine ⟨399976782781059731984333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4266419016331303807832885 399976782781059731984333)
                  ·
                    rfl

theorem cell22_3505284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_3505284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505284 prefixEnd_3505284 := by exact prefixLift 3505284
  have htrace : WordTrace (prefixWord ++ tailWord_3505284) baseStart_3505284 baseEnd_3505284 := by
    simpa [prefixWord, tailWord_3505284, baseEnd_3505284] using wordTrace_append hprefix tailTrace_3505284
  have hstable : (prefixWord ++ tailWord_3505284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505284).length < 2 ^ (prefixWord ++ tailWord_3505284).sum := by decide
  have hdescent : baseEnd_3505284 < baseStart_3505284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505312 : List Nat := [2, 1, 1, 4, 2, 1, 2, 5, 4]
def baseStart_3505312 : Nat := 118140960795 + 3505312 * 2 ^ 59
def prefixEnd_3505312 : Nat := 4983230072969 + 3 ^ 40 * 3505312 * 2
def baseEnd_3505312 : Nat := 399979977771798818750971

theorem tailTrace_3505312 : CollatzResearch.WordTrace tailWord_3505312 prefixEnd_3505312 399979977771798818750971 := by
  unfold tailWord_3505312
  simp only [CollatzResearch.WordTrace]
  refine ⟨63924615938430379236491095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85232821251240505648654793 63924615938430379236491095)
  ·
    refine ⟨95886923907645568854736643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63924615938430379236491095 95886923907645568854736643)
    ·
      refine ⟨143830385861468353282104965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95886923907645568854736643 143830385861468353282104965)
      ·
        refine ⟨26968197349025316240394681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143830385861468353282104965 26968197349025316240394681)
        ·
          refine ⟨20226148011768987180296011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26968197349025316240394681 20226148011768987180296011)
          ·
            refine ⟨30339222017653480770444017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20226148011768987180296011 30339222017653480770444017)
            ·
              refine ⟨22754416513240110577833013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30339222017653480770444017 22754416513240110577833013)
              ·
                refine ⟨2133226548116260366671845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22754416513240110577833013 2133226548116260366671845)
                ·
                  refine ⟨399979977771798818750971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2133226548116260366671845 399979977771798818750971)
                  ·
                    rfl

theorem cell22_3505312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 4].length) (baseStart_3505312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505312 prefixEnd_3505312 := by exact prefixLift 3505312
  have htrace : WordTrace (prefixWord ++ tailWord_3505312) baseStart_3505312 baseEnd_3505312 := by
    simpa [prefixWord, tailWord_3505312, baseEnd_3505312] using wordTrace_append hprefix tailTrace_3505312
  have hstable : (prefixWord ++ tailWord_3505312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505312).length < 2 ^ (prefixWord ++ tailWord_3505312).sum := by decide
  have hdescent : baseEnd_3505312 < baseStart_3505312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505327 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 2, 3]
def baseStart_3505327 : Nat := 118140960795 + 3505327 * 2 ^ 59
def prefixEnd_3505327 : Nat := 4983230072969 + 3 ^ 40 * 3505327 * 2
def baseEnd_3505327 : Nat := 1199945068121941417127867

theorem tailTrace_3505327 : CollatzResearch.WordTrace tailWord_3505327 prefixEnd_3505327 1199945068121941417127867 := by
  unfold tailWord_3505327
  simp only [CollatzResearch.WordTrace]
  refine ⟨127849778971806416034778235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85233185981204277356518823 127849778971806416034778235)
  ·
    refine ⟨191774668457709624052167353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127849778971806416034778235 191774668457709624052167353)
    ·
      refine ⟨143831001343282218039125515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191774668457709624052167353 143831001343282218039125515)
      ·
        refine ⟨215746502014923327058688273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143831001343282218039125515 215746502014923327058688273)
        ·
          refine ⟨161809876511192495294016205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215746502014923327058688273 161809876511192495294016205)
          ·
            refine ⟨60678703691697185735256077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161809876511192495294016205 60678703691697185735256077)
            ·
              refine ⟨22754513884386444650721029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60678703691697185735256077 22754513884386444650721029)
              ·
                refine ⟨4266471353322458372010193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22754513884386444650721029 4266471353322458372010193)
                ·
                  refine ⟨3199853514991843779007645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4266471353322458372010193 3199853514991843779007645)
                  ·
                    refine ⟨1199945068121941417127867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3199853514991843779007645 1199945068121941417127867)
                    ·
                      rfl

theorem cell22_3505327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_3505327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505327 prefixEnd_3505327 := by exact prefixLift 3505327
  have htrace : WordTrace (prefixWord ++ tailWord_3505327) baseStart_3505327 baseEnd_3505327 := by
    simpa [prefixWord, tailWord_3505327, baseEnd_3505327] using wordTrace_append hprefix tailTrace_3505327
  have hstable : (prefixWord ++ tailWord_3505327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505327).length < 2 ^ (prefixWord ++ tailWord_3505327).sum := by decide
  have hdescent : baseEnd_3505327 < baseStart_3505327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505329 : List Nat := [1, 2, 2, 5, 1, 2, 1, 4, 4]
def baseStart_3505329 : Nat := 118140960795 + 3505329 * 2 ^ 59
def prefixEnd_3505329 : Nat := 4983230072969 + 3 ^ 40 * 3505329 * 2
def baseEnd_3505329 : Nat := 399981917587604692859287

theorem tailTrace_3505329 : CollatzResearch.WordTrace tailWord_3505329 prefixEnd_3505329 399981917587604692859287 := by
  unfold tailWord_3505329
  simp only [CollatzResearch.WordTrace]
  refine ⟨127849851917799170376351041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85233234611866113584234027 127849851917799170376351041)
  ·
    refine ⟨95887388938349377782263281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127849851917799170376351041 95887388938349377782263281)
    ·
      refine ⟨71915541703762033336697461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95887388938349377782263281 71915541703762033336697461)
      ·
        refine ⟨6742082034727690625315387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71915541703762033336697461 6742082034727690625315387)
        ·
          refine ⟨10113123052091535937973081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6742082034727690625315387 10113123052091535937973081)
          ·
            refine ⟨7584842289068651953479811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10113123052091535937973081 7584842289068651953479811)
            ·
              refine ⟨11377263433602977930219717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584842289068651953479811 11377263433602977930219717)
              ·
                refine ⟨2133236893800558361916197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11377263433602977930219717 2133236893800558361916197)
                ·
                  refine ⟨399981917587604692859287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2133236893800558361916197 399981917587604692859287)
                  ·
                    rfl

theorem cell22_3505329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 4].length) (baseStart_3505329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505329 prefixEnd_3505329 := by exact prefixLift 3505329
  have htrace : WordTrace (prefixWord ++ tailWord_3505329) baseStart_3505329 baseEnd_3505329 := by
    simpa [prefixWord, tailWord_3505329, baseEnd_3505329] using wordTrace_append hprefix tailTrace_3505329
  have hstable : (prefixWord ++ tailWord_3505329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505329).length < 2 ^ (prefixWord ++ tailWord_3505329).sum := by decide
  have hdescent : baseEnd_3505329 < baseStart_3505329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505346 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3505346 : Nat := 118140960795 + 3505346 * 2 ^ 59
def prefixEnd_3505346 : Nat := 4983230072969 + 3 ^ 40 * 3505346 * 2
def baseEnd_3505346 : Nat := 399983857403410566967603

theorem tailTrace_3505346 : CollatzResearch.WordTrace tailWord_3505346 prefixEnd_3505346 399983857403410566967603 := by
  unfold tailWord_3505346
  simp only [CollatzResearch.WordTrace]
  refine ⟨31962617989684395569929973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85233647972491721519813261 31962617989684395569929973)
  ·
    refine ⟨2996495436532912084680935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31962617989684395569929973 2996495436532912084680935)
    ·
      refine ⟨4494743154799368127021403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2996495436532912084680935 4494743154799368127021403)
      ·
        refine ⟨6742114732199052190532105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494743154799368127021403 6742114732199052190532105)
        ·
          refine ⟨5056586049149289142899079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6742114732199052190532105 5056586049149289142899079)
          ·
            refine ⟨7584879073723933714348619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056586049149289142899079 7584879073723933714348619)
            ·
              refine ⟨11377318610585900571522929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584879073723933714348619 11377318610585900571522929)
              ·
                refine ⟨8532988957939425428642197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11377318610585900571522929 8532988957939425428642197)
                ·
                  refine ⟨399983857403410566967603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8532988957939425428642197 399983857403410566967603)
                  ·
                    rfl

theorem cell22_3505346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3505346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505346 prefixEnd_3505346 := by exact prefixLift 3505346
  have htrace : WordTrace (prefixWord ++ tailWord_3505346) baseStart_3505346 baseEnd_3505346 := by
    simpa [prefixWord, tailWord_3505346, baseEnd_3505346] using wordTrace_append hprefix tailTrace_3505346
  have hstable : (prefixWord ++ tailWord_3505346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505346).length < 2 ^ (prefixWord ++ tailWord_3505346).sum := by decide
  have hdescent : baseEnd_3505346 < baseStart_3505346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505389 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_3505389 : Nat := 118140960795 + 3505389 * 2 ^ 59
def prefixEnd_3505389 : Nat := 4983230072969 + 3 ^ 40 * 3505389 * 2
def baseEnd_3505389 : Nat := 1199966291988993922077677

theorem tailTrace_3505389 : CollatzResearch.WordTrace tailWord_3505389 prefixEnd_3505389 1199966291988993922077677 := by
  unfold tailWord_3505389
  simp only [CollatzResearch.WordTrace]
  refine ⟨127852040297581800623535221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85234693531721200415690147 127852040297581800623535221)
  ·
    refine ⟨11986128777898293808456427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127852040297581800623535221 11986128777898293808456427)
    ·
      refine ⟨17979193166847440712684641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11986128777898293808456427 17979193166847440712684641)
      ·
        refine ⟨13484394875135580534513481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17979193166847440712684641 13484394875135580534513481)
        ·
          refine ⟨10113296156351685400885111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13484394875135580534513481 10113296156351685400885111)
          ·
            refine ⟨15169944234527528101327667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10113296156351685400885111 15169944234527528101327667)
            ·
              refine ⟨22754916351791292151991501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15169944234527528101327667 22754916351791292151991501)
              ·
                refine ⟨8533093631921734556996813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22754916351791292151991501 8533093631921734556996813)
                ·
                  refine ⟨3199910111970650458873805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8533093631921734556996813 3199910111970650458873805)
                  ·
                    refine ⟨1199966291988993922077677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3199910111970650458873805 1199966291988993922077677)
                    ·
                      rfl

theorem cell22_3505389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_3505389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505389 prefixEnd_3505389 := by exact prefixLift 3505389
  have htrace : WordTrace (prefixWord ++ tailWord_3505389) baseStart_3505389 baseEnd_3505389 := by
    simpa [prefixWord, tailWord_3505389, baseEnd_3505389] using wordTrace_append hprefix tailTrace_3505389
  have hstable : (prefixWord ++ tailWord_3505389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505389).length < 2 ^ (prefixWord ++ tailWord_3505389).sum := by decide
  have hdescent : baseEnd_3505389 < baseStart_3505389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505453 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 5]
def baseStart_3505453 : Nat := 118140960795 + 3505453 * 2 ^ 59
def prefixEnd_3505453 : Nat := 4983230072969 + 3 ^ 40 * 3505453 * 2
def baseEnd_3505453 : Nat := 399996066832306362825827

theorem tailTrace_3505453 : CollatzResearch.WordTrace tailWord_3505453 prefixEnd_3505453 399996066832306362825827 := by
  unfold tailWord_3505453
  simp only [CollatzResearch.WordTrace]
  refine ⟨127854374569349939553865013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85236249712899959702576675 127854374569349939553865013)
  ·
    refine ⟨11986347615876556833174845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127854374569349939553865013 11986347615876556833174845)
    ·
      refine ⟨4494880355953708812440567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11986347615876556833174845 4494880355953708812440567)
      ·
        refine ⟨6742320533930563218660851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494880355953708812440567 6742320533930563218660851)
        ·
          refine ⟨10113480800895844827991277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6742320533930563218660851 10113480800895844827991277)
          ·
            refine ⟨3792555300335941810496729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10113480800895844827991277 3792555300335941810496729)
            ·
              refine ⟨2844416475251956357872547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792555300335941810496729 2844416475251956357872547)
              ·
                refine ⟨4266624712877934536808821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844416475251956357872547 4266624712877934536808821)
                ·
                  refine ⟨399996066832306362825827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4266624712877934536808821 399996066832306362825827)
                  ·
                    rfl

theorem cell22_3505453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_3505453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505453 prefixEnd_3505453 := by exact prefixLift 3505453
  have htrace : WordTrace (prefixWord ++ tailWord_3505453) baseStart_3505453 baseEnd_3505453 := by
    simpa [prefixWord, tailWord_3505453, baseEnd_3505453] using wordTrace_append hprefix tailTrace_3505453
  have hstable : (prefixWord ++ tailWord_3505453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505453).length < 2 ^ (prefixWord ++ tailWord_3505453).sum := by decide
  have hdescent : baseEnd_3505453 < baseStart_3505453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505522 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_3505522 : Nat := 118140960795 + 3505522 * 2 ^ 59
def prefixEnd_3505522 : Nat := 4983230072969 + 3 ^ 40 * 3505522 * 2
def baseEnd_3505522 : Nat := 1200011820607025908502269

theorem tailTrace_3505522 : CollatzResearch.WordTrace tailWord_3505522 prefixEnd_3505522 1200011820607025908502269 := by
  unfold tailWord_3505522
  simp only [CollatzResearch.WordTrace]
  refine ⟨31964222801524991084531705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85237927470733309558751213 31964222801524991084531705)
  ·
    refine ⟨23973167101143743313398779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31964222801524991084531705 23973167101143743313398779)
    ·
      refine ⟨35959750651715614970098169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23973167101143743313398779 35959750651715614970098169)
      ·
        refine ⟨26969812988786711227573627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35959750651715614970098169 26969812988786711227573627)
        ·
          refine ⟨40454719483180066841360441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26969812988786711227573627 40454719483180066841360441)
          ·
            refine ⟨30341039612385050131020331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40454719483180066841360441 30341039612385050131020331)
            ·
              refine ⟨45511559418577575196530497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30341039612385050131020331 45511559418577575196530497)
              ·
                refine ⟨34133669563933181397397873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45511559418577575196530497 34133669563933181397397873)
                ·
                  refine ⟨25600252172949886048048405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34133669563933181397397873 25600252172949886048048405)
                  ·
                    refine ⟨1200011820607025908502269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25600252172949886048048405 1200011820607025908502269)
                    ·
                      rfl

theorem cell22_3505522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_3505522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505522 prefixEnd_3505522 := by exact prefixLift 3505522
  have htrace : WordTrace (prefixWord ++ tailWord_3505522) baseStart_3505522 baseEnd_3505522 := by
    simpa [prefixWord, tailWord_3505522, baseEnd_3505522] using wordTrace_append hprefix tailTrace_3505522
  have hstable : (prefixWord ++ tailWord_3505522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505522).length < 2 ^ (prefixWord ++ tailWord_3505522).sum := by decide
  have hdescent : baseEnd_3505522 < baseStart_3505522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505541 : List Nat := [1, 3, 1, 1, 3, 1, 3, 5, 1, 3]
def baseStart_3505541 : Nat := 118140960795 + 3505541 * 2 ^ 59
def prefixEnd_3505541 : Nat := 4983230072969 + 3 ^ 40 * 3505541 * 2
def baseEnd_3505541 : Nat := 1200018324695316192277211

theorem tailTrace_3505541 : CollatzResearch.WordTrace tailWord_3505541 prefixEnd_3505541 1200018324695316192277211 := by
  unfold tailWord_3505541
  simp only [CollatzResearch.WordTrace]
  refine ⟨127857584193031130583068477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85238389462020753722045651 127857584193031130583068477)
  ·
    refine ⟨47946594072386673968650679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127857584193031130583068477 47946594072386673968650679)
    ·
      refine ⟨71919891108580010952976019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47946594072386673968650679 71919891108580010952976019)
      ·
        refine ⟨107879836662870016429464029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71919891108580010952976019 107879836662870016429464029)
        ·
          refine ⟨40454938748576256161049011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107879836662870016429464029 40454938748576256161049011)
          ·
            refine ⟨60682408122864384241573517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40454938748576256161049011 60682408122864384241573517)
            ·
              refine ⟨22755903046074144090590069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60682408122864384241573517 22755903046074144090590069)
              ·
                refine ⟨2133365910569451008492819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22755903046074144090590069 2133365910569451008492819)
                ·
                  refine ⟨3200048865854176512739229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133365910569451008492819 3200048865854176512739229)
                  ·
                    refine ⟨1200018324695316192277211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3200048865854176512739229 1200018324695316192277211)
                    ·
                      rfl

theorem cell22_3505541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_3505541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505541 prefixEnd_3505541 := by exact prefixLift 3505541
  have htrace : WordTrace (prefixWord ++ tailWord_3505541) baseStart_3505541 baseEnd_3505541 := by
    simpa [prefixWord, tailWord_3505541, baseEnd_3505541] using wordTrace_append hprefix tailTrace_3505541
  have hstable : (prefixWord ++ tailWord_3505541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505541).length < 2 ^ (prefixWord ++ tailWord_3505541).sum := by decide
  have hdescent : baseEnd_3505541 < baseStart_3505541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505631 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 2, 3]
def baseStart_3505631 : Nat := 118140960795 + 3505631 * 2 ^ 59
def prefixEnd_3505631 : Nat := 4983230072969 + 3 ^ 40 * 3505631 * 2
def baseEnd_3505631 : Nat := 1200049133534585957526935

theorem tailTrace_3505631 : CollatzResearch.WordTrace tailWord_3505631 prefixEnd_3505631 1200049133534585957526935 := by
  unfold tailWord_3505631
  simp only [CollatzResearch.WordTrace]
  refine ⟨127860866762705075953844747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85240577841803383969229831 127860866762705075953844747)
  ·
    refine ⟨191791300144057613930767121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127860866762705075953844747 191791300144057613930767121)
    ·
      refine ⟨143843475108043210448075341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191791300144057613930767121 143843475108043210448075341)
      ·
        refine ⟨53941303165516203918028253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143843475108043210448075341 53941303165516203918028253)
        ·
          refine ⟨20227988687068576469260595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53941303165516203918028253 20227988687068576469260595)
          ·
            refine ⟨30341983030602864703890893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20227988687068576469260595 30341983030602864703890893)
            ·
              refine ⟨11378243636476074263959085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30341983030602864703890893 11378243636476074263959085)
              ·
                refine ⟨4266841363678527848984657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11378243636476074263959085 4266841363678527848984657)
                ·
                  refine ⟨3200131022758895886738493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4266841363678527848984657 3200131022758895886738493)
                  ·
                    refine ⟨1200049133534585957526935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3200131022758895886738493 1200049133534585957526935)
                    ·
                      rfl

theorem cell22_3505631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_3505631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505631 prefixEnd_3505631 := by exact prefixLift 3505631
  have htrace : WordTrace (prefixWord ++ tailWord_3505631) baseStart_3505631 baseEnd_3505631 := by
    simpa [prefixWord, tailWord_3505631, baseEnd_3505631] using wordTrace_append hprefix tailTrace_3505631
  have hstable : (prefixWord ++ tailWord_3505631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505631).length < 2 ^ (prefixWord ++ tailWord_3505631).sum := by decide
  have hdescent : baseEnd_3505631 < baseStart_3505631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505646 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3505646 : Nat := 118140960795 + 3505646 * 2 ^ 59
def prefixEnd_3505646 : Nat := 4983230072969 + 3 ^ 40 * 3505646 * 2
def baseEnd_3505646 : Nat := 1200054268341130918401889

theorem tailTrace_3505646 : CollatzResearch.WordTrace tailWord_3505646 prefixEnd_3505646 1200054268341130918401889 := by
  unfold tailWord_3505646
  simp only [CollatzResearch.WordTrace]
  refine ⟨15982676732206341689455099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85240942571767155677093861 15982676732206341689455099)
  ·
    refine ⟨23974015098309512534182649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15982676732206341689455099 23974015098309512534182649)
    ·
      refine ⟨17980511323732134400636987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23974015098309512534182649 17980511323732134400636987)
      ·
        refine ⟨26970766985598201600955481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17980511323732134400636987 26970766985598201600955481)
        ·
          refine ⟨20228075239198651200716611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26970766985598201600955481 20228075239198651200716611)
          ·
            refine ⟨30342112858797976801074917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20228075239198651200716611 30342112858797976801074917)
            ·
              refine ⟨5689146161024620650201547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30342112858797976801074917 5689146161024620650201547)
              ·
                refine ⟨8533719241536930975302321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689146161024620650201547 8533719241536930975302321)
                ·
                  refine ⟨6400289431152698231476741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8533719241536930975302321 6400289431152698231476741)
                  ·
                    refine ⟨1200054268341130918401889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6400289431152698231476741 1200054268341130918401889)
                    ·
                      rfl

theorem cell22_3505646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3505646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505646 prefixEnd_3505646 := by exact prefixLift 3505646
  have htrace : WordTrace (prefixWord ++ tailWord_3505646) baseStart_3505646 baseEnd_3505646 := by
    simpa [prefixWord, tailWord_3505646, baseEnd_3505646] using wordTrace_append hprefix tailTrace_3505646
  have hstable : (prefixWord ++ tailWord_3505646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505646).length < 2 ^ (prefixWord ++ tailWord_3505646).sum := by decide
  have hdescent : baseEnd_3505646 < baseStart_3505646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
