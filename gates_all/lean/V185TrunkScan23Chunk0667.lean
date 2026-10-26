import V185TrunkScan23Chunk0666

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3943545 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 3]
def baseStart_3943545 : Nat := 118140960795 + 3943545 * 2 ^ 59
def prefixEnd_3943545 : Nat := 4983230072969 + 3 ^ 40 * 3943545 * 2
def baseEnd_3943545 : Nat := 2024934067634878595751473

theorem tailTrace_3943545 : CollatzResearch.WordTrace tailWord_3943545 prefixEnd_3943545 2024934067634878595751473 := by
  unfold tailWord_3943545
  simp only [CollatzResearch.WordTrace]
  refine ⟨143832902498217443710728089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95888601665478295807152059 143832902498217443710728089)
  ·
    refine ⟨107874676873663082783046067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143832902498217443710728089 107874676873663082783046067)
    ·
      refine ⟨161812015310494624174569101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107874676873663082783046067 161812015310494624174569101)
      ·
        refine ⟨60679505741435484065463413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161812015310494624174569101 60679505741435484065463413)
        ·
          refine ⟨5688703663259576631137195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60679505741435484065463413 5688703663259576631137195)
          ·
            refine ⟨8533055494889364946705793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688703663259576631137195 8533055494889364946705793)
            ·
              refine ⟨6399791621167023710029345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8533055494889364946705793 6399791621167023710029345)
              ·
                refine ⟨4799843715875267782522009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6399791621167023710029345 4799843715875267782522009)
                ·
                  refine ⟨3599882786906450836891507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4799843715875267782522009 3599882786906450836891507)
                  ·
                    refine ⟨5399824180359676255337261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3599882786906450836891507 5399824180359676255337261)
                    ·
                      refine ⟨2024934067634878595751473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5399824180359676255337261 2024934067634878595751473)
                      ·
                        rfl

theorem cell23_3943545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_3943545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943545 prefixEnd_3943545 := by exact prefixLift 3943545
  have htrace : WordTrace (prefixWord ++ tailWord_3943545) baseStart_3943545 baseEnd_3943545 := by
    simpa [prefixWord, tailWord_3943545, baseEnd_3943545] using wordTrace_append hprefix tailTrace_3943545
  have hstable : (prefixWord ++ tailWord_3943545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943545).length < 2 ^ (prefixWord ++ tailWord_3943545).sum := by decide
  have hdescent : baseEnd_3943545 < baseStart_3943545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943602 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_3943602 : Nat := 118140960795 + 3943602 * 2 ^ 59
def prefixEnd_3943602 : Nat := 4983230072969 + 3 ^ 40 * 3943602 * 2
def baseEnd_3943602 : Nat := 2024963336032184872738711

theorem tailTrace_3943602 : CollatzResearch.WordTrace tailWord_3943602 prefixEnd_3943602 2024963336032184872738711 := by
  unfold tailWord_3943602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35958745364752735611388265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95889987639340628297035373 35958745364752735611388265)
  ·
    refine ⟨26969059023564551708541199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35958745364752735611388265 26969059023564551708541199)
    ·
      refine ⟨40453588535346827562811799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26969059023564551708541199 40453588535346827562811799)
      ·
        refine ⟨60680382803020241344217699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40453588535346827562811799 60680382803020241344217699)
        ·
          refine ⟨91020574204530362016326549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60680382803020241344217699 91020574204530362016326549)
          ·
            refine ⟨4266589415837360719515307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91020574204530362016326549 4266589415837360719515307)
            ·
              refine ⟨6399884123756041079272961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266589415837360719515307 6399884123756041079272961)
              ·
                refine ⟨4799913092817030809454721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6399884123756041079272961 4799913092817030809454721)
                ·
                  refine ⟨3599934819612773107091041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4799913092817030809454721 3599934819612773107091041)
                  ·
                    refine ⟨2699951114709579830318281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599934819612773107091041 2699951114709579830318281)
                    ·
                      refine ⟨2024963336032184872738711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699951114709579830318281 2024963336032184872738711)
                      ·
                        rfl

theorem cell23_3943602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_3943602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943602 prefixEnd_3943602 := by exact prefixLift 3943602
  have htrace : WordTrace (prefixWord ++ tailWord_3943602) baseStart_3943602 baseEnd_3943602 := by
    simpa [prefixWord, tailWord_3943602, baseEnd_3943602] using wordTrace_append hprefix tailTrace_3943602
  have hstable : (prefixWord ++ tailWord_3943602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943602).length < 2 ^ (prefixWord ++ tailWord_3943602).sum := by decide
  have hdescent : baseEnd_3943602 < baseStart_3943602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943611 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 2, 5, 2]
def baseStart_3943611 : Nat := 118140960795 + 3943611 * 2 ^ 59
def prefixEnd_3943611 : Nat := 4983230072969 + 3 ^ 40 * 3943611 * 2
def baseEnd_3943611 : Nat := 2024967957358075337526169

theorem tailTrace_3943611 : CollatzResearch.WordTrace tailWord_3943611 prefixEnd_3943611 2024967957358075337526169 := by
  unfold tailWord_3943611
  simp only [CollatzResearch.WordTrace]
  refine ⟨143835309715978336982630687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95890206477318891321753791 143835309715978336982630687)
  ·
    refine ⟨215752964573967505473946031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143835309715978336982630687 215752964573967505473946031)
    ·
      refine ⟨323629446860951258210919047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215752964573967505473946031 323629446860951258210919047)
      ·
        refine ⟨485444170291426887316378571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323629446860951258210919047 485444170291426887316378571)
        ·
          refine ⟨728166255437140330974567857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485444170291426887316378571 728166255437140330974567857)
          ·
            refine ⟨546124691577855248230925893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728166255437140330974567857 546124691577855248230925893)
            ·
              refine ⟨102398379670847859043298605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 546124691577855248230925893 102398379670847859043298605)
              ·
                refine ⟨38399392376567947141236977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102398379670847859043298605 38399392376567947141236977)
                ·
                  refine ⟨28799544282425960355927733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38399392376567947141236977 28799544282425960355927733)
                  ·
                    refine ⟨2699957276477433783368225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28799544282425960355927733 2699957276477433783368225)
                    ·
                      refine ⟨2024967957358075337526169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699957276477433783368225 2024967957358075337526169)
                      ·
                        rfl

theorem cell23_3943611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 5, 2].length) (baseStart_3943611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943611 prefixEnd_3943611 := by exact prefixLift 3943611
  have htrace : WordTrace (prefixWord ++ tailWord_3943611) baseStart_3943611 baseEnd_3943611 := by
    simpa [prefixWord, tailWord_3943611, baseEnd_3943611] using wordTrace_append hprefix tailTrace_3943611
  have hstable : (prefixWord ++ tailWord_3943611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943611).length < 2 ^ (prefixWord ++ tailWord_3943611).sum := by decide
  have hdescent : baseEnd_3943611 < baseStart_3943611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943641 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_3943641 : Nat := 118140960795 + 3943641 * 2 ^ 59
def prefixEnd_3943641 : Nat := 4983230072969 + 3 ^ 40 * 3943641 * 2
def baseEnd_3943641 : Nat := 2024983361777710220151031

theorem tailTrace_3943641 : CollatzResearch.WordTrace tailWord_3943641 prefixEnd_3943641 2024983361777710220151031 := by
  unfold tailWord_3943641
  simp only [CollatzResearch.WordTrace]
  refine ⟨143836403905869652106222777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95890935937246434737481851 143836403905869652106222777)
  ·
    refine ⟨107877302929402239079667083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143836403905869652106222777 107877302929402239079667083)
    ·
      refine ⟨161815954394103358619500625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107877302929402239079667083 161815954394103358619500625)
      ·
        refine ⟨121361965795577518964625469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161815954394103358619500625 121361965795577518964625469)
        ·
          refine ⟨45510737173341569611734551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121361965795577518964625469 45510737173341569611734551)
          ·
            refine ⟨68266105760012354417601827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45510737173341569611734551 68266105760012354417601827)
            ·
              refine ⟨102399158640018531626402741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68266105760012354417601827 102399158640018531626402741)
              ·
                refine ⟨9599921122501737339975257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102399158640018531626402741 9599921122501737339975257)
                ·
                  refine ⟨7199940841876303004981443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9599921122501737339975257 7199940841876303004981443)
                  ·
                    refine ⟨10799911262814454507472165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199940841876303004981443 10799911262814454507472165)
                    ·
                      refine ⟨2024983361777710220151031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10799911262814454507472165 2024983361777710220151031)
                      ·
                        rfl

theorem cell23_3943641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_3943641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943641 prefixEnd_3943641 := by exact prefixLift 3943641
  have htrace : WordTrace (prefixWord ++ tailWord_3943641) baseStart_3943641 baseEnd_3943641 := by
    simpa [prefixWord, tailWord_3943641, baseEnd_3943641] using wordTrace_append hprefix tailTrace_3943641
  have hstable : (prefixWord ++ tailWord_3943641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943641).length < 2 ^ (prefixWord ++ tailWord_3943641).sum := by decide
  have hdescent : baseEnd_3943641 < baseStart_3943641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943658 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_3943658 : Nat := 118140960795 + 3943658 * 2 ^ 59
def prefixEnd_3943658 : Nat := 4983230072969 + 3 ^ 40 * 3943658 * 2
def baseEnd_3943658 : Nat := 2024992090948836653638453

theorem tailTrace_3943658 : CollatzResearch.WordTrace tailWord_3943658 prefixEnd_3943658 2024992090948836653638453 := by
  unfold tailWord_3943658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35959255986702016002397907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95891349297872042673061085 35959255986702016002397907)
  ·
    refine ⟨53938883980053024003596861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35959255986702016002397907 53938883980053024003596861)
    ·
      refine ⟨20227081492519884001348823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53938883980053024003596861 20227081492519884001348823)
      ·
        refine ⟨30340622238779826002023235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20227081492519884001348823 30340622238779826002023235)
        ·
          refine ⟨45510933358169739003034853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30340622238779826002023235 45510933358169739003034853)
          ·
            refine ⟨8533300004656826063069035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45510933358169739003034853 8533300004656826063069035)
            ·
              refine ⟨12799950006985239094603553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8533300004656826063069035 12799950006985239094603553)
              ·
                refine ⟨9599962505238929320952665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12799950006985239094603553 9599962505238929320952665)
                ·
                  refine ⟨7199971878929196990714499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9599962505238929320952665 7199971878929196990714499)
                  ·
                    refine ⟨10799957818393795486071749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199971878929196990714499 10799957818393795486071749)
                    ·
                      refine ⟨2024992090948836653638453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10799957818393795486071749 2024992090948836653638453)
                      ·
                        rfl

theorem cell23_3943658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_3943658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943658 prefixEnd_3943658 := by exact prefixLift 3943658
  have htrace : WordTrace (prefixWord ++ tailWord_3943658) baseStart_3943658 baseEnd_3943658 := by
    simpa [prefixWord, tailWord_3943658, baseEnd_3943658] using wordTrace_append hprefix tailTrace_3943658
  have hstable : (prefixWord ++ tailWord_3943658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943658).length < 2 ^ (prefixWord ++ tailWord_3943658).sum := by decide
  have hdescent : baseEnd_3943658 < baseStart_3943658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943758 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_3943758 : Nat := 118140960795 + 3943758 * 2 ^ 59
def prefixEnd_3943758 : Nat := 4983230072969 + 3 ^ 40 * 3943758 * 2
def baseEnd_3943758 : Nat := 675014479671428754129331

theorem tailTrace_3943758 : CollatzResearch.WordTrace tailWord_3943758 prefixEnd_3943758 675014479671428754129331 := by
  unfold tailWord_3943758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980083905805722636028991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95893780830963854058821285 17980083905805722636028991)
  ·
    refine ⟨26970125858708583954043487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17980083905805722636028991 26970125858708583954043487)
    ·
      refine ⟨40455188788062875931065231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26970125858708583954043487 40455188788062875931065231)
      ·
        refine ⟨60682783182094313896597847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40455188788062875931065231 60682783182094313896597847)
        ·
          refine ⟨91024174773141470844896771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60682783182094313896597847 91024174773141470844896771)
          ·
            refine ⟨136536262159712206267345157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91024174773141470844896771 136536262159712206267345157)
            ·
              refine ⟨25600549154946038675127217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136536262159712206267345157 25600549154946038675127217)
              ·
                refine ⟨19200411866209529006345413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25600549154946038675127217 19200411866209529006345413)
                ·
                  refine ⟨3600077224914286688689765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19200411866209529006345413 3600077224914286688689765)
                  ·
                    refine ⟨675014479671428754129331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3600077224914286688689765 675014479671428754129331)
                    ·
                      rfl

theorem cell23_3943758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_3943758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943758 prefixEnd_3943758 := by exact prefixLift 3943758
  have htrace : WordTrace (prefixWord ++ tailWord_3943758) baseStart_3943758 baseEnd_3943758 := by
    simpa [prefixWord, tailWord_3943758, baseEnd_3943758] using wordTrace_append hprefix tailTrace_3943758
  have hstable : (prefixWord ++ tailWord_3943758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943758).length < 2 ^ (prefixWord ++ tailWord_3943758).sum := by decide
  have hdescent : baseEnd_3943758 < baseStart_3943758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943765 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3943765 : Nat := 118140960795 + 3943765 * 2 ^ 59
def prefixEnd_3943765 : Nat := 4983230072969 + 3 ^ 40 * 3943765 * 2
def baseEnd_3943765 : Nat := 2025047033378867735000461

theorem tailTrace_3943765 : CollatzResearch.WordTrace tailWord_3943765 prefixEnd_3943765 2025047033378867735000461 := by
  unfold tailWord_3943765
  simp only [CollatzResearch.WordTrace]
  refine ⟨143840926557420421283736749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95893951038280280855824499 143840926557420421283736749)
  ·
    refine ⟨53940347459032657981401281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143840926557420421283736749 53940347459032657981401281)
    ·
      refine ⟨40455260594274493486050961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53940347459032657981401281 40455260594274493486050961)
      ·
        refine ⟨30341445445705870114538221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40455260594274493486050961 30341445445705870114538221)
        ·
          refine ⟨11378042042139701292951833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30341445445705870114538221 11378042042139701292951833)
          ·
            refine ⟨8533531531604775969713875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11378042042139701292951833 8533531531604775969713875)
            ·
              refine ⟨12800297297407163954570813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8533531531604775969713875 12800297297407163954570813)
              ·
                refine ⟨4800111486527686482964055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12800297297407163954570813 4800111486527686482964055)
                ·
                  refine ⟨7200167229791529724446083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800111486527686482964055 7200167229791529724446083)
                  ·
                    refine ⟨10800250844687294586669125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7200167229791529724446083 10800250844687294586669125)
                    ·
                      refine ⟨2025047033378867735000461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10800250844687294586669125 2025047033378867735000461)
                      ·
                        rfl

theorem cell23_3943765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3943765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943765 prefixEnd_3943765 := by exact prefixLift 3943765
  have htrace : WordTrace (prefixWord ++ tailWord_3943765) baseStart_3943765 baseEnd_3943765 := by
    simpa [prefixWord, tailWord_3943765, baseEnd_3943765] using wordTrace_append hprefix tailTrace_3943765
  have hstable : (prefixWord ++ tailWord_3943765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943765).length < 2 ^ (prefixWord ++ tailWord_3943765).sum := by decide
  have hdescent : baseEnd_3943765 < baseStart_3943765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943766 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3943766 : Nat := 118140960795 + 3943766 * 2 ^ 59
def prefixEnd_3943766 : Nat := 4983230072969 + 3 ^ 40 * 3943766 * 2
def baseEnd_3943766 : Nat := 225005282984391359009773

theorem tailTrace_3943766 : CollatzResearch.WordTrace tailWord_3943766 prefixEnd_3943766 225005282984391359009773 := by
  unfold tailWord_3943766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990060189401049903407697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95893975353611198969682101 8990060189401049903407697)
  ·
    refine ⟨6742545142050787427555773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8990060189401049903407697 6742545142050787427555773)
    ·
      refine ⟨2528454428269045285333415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6742545142050787427555773 2528454428269045285333415)
      ·
        refine ⟨3792681642403567928000123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528454428269045285333415 3792681642403567928000123)
        ·
          refine ⟨5689022463605351892000185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792681642403567928000123 5689022463605351892000185)
          ·
            refine ⟨4266766847704013919000139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5689022463605351892000185 4266766847704013919000139)
            ·
              refine ⟨6400150271556020878500209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266766847704013919000139 6400150271556020878500209)
              ·
                refine ⟨4800112703667015658875157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6400150271556020878500209 4800112703667015658875157)
                ·
                  refine ⟨225005282984391359009773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4800112703667015658875157 225005282984391359009773)
                  ·
                    rfl

theorem cell23_3943766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3943766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943766 prefixEnd_3943766 := by exact prefixLift 3943766
  have htrace : WordTrace (prefixWord ++ tailWord_3943766) baseStart_3943766 baseEnd_3943766 := by
    simpa [prefixWord, tailWord_3943766, baseEnd_3943766] using wordTrace_append hprefix tailTrace_3943766
  have hstable : (prefixWord ++ tailWord_3943766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943766).length < 2 ^ (prefixWord ++ tailWord_3943766).sum := by decide
  have hdescent : baseEnd_3943766 < baseStart_3943766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943778 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3943778 : Nat := 118140960795 + 3943778 * 2 ^ 59
def prefixEnd_3943778 : Nat := 4983230072969 + 3 ^ 40 * 3943778 * 2
def baseEnd_3943778 : Nat := 2025053708627376184137901

theorem tailTrace_3943778 : CollatzResearch.WordTrace tailWord_3943778 prefixEnd_3943778 2025053708627376184137901 := by
  unfold tailWord_3943778
  simp only [CollatzResearch.WordTrace]
  refine ⟨35960350176593331125989997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95894267137582216335973325 35960350176593331125989997)
  ·
    refine ⟨13485131316222499172246249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35960350176593331125989997 13485131316222499172246249)
    ·
      refine ⟨10113848487166874379184687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13485131316222499172246249 10113848487166874379184687)
      ·
        refine ⟨15170772730750311568777031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10113848487166874379184687 15170772730750311568777031)
        ·
          refine ⟨22756159096125467353165547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15170772730750311568777031 22756159096125467353165547)
          ·
            refine ⟨34134238644188201029748321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22756159096125467353165547 34134238644188201029748321)
            ·
              refine ⟨25600678983141150772311241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34134238644188201029748321 25600678983141150772311241)
              ·
                refine ⟨19200509237355863079233431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25600678983141150772311241 19200509237355863079233431)
                ·
                  refine ⟨28800763856033794618850147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19200509237355863079233431 28800763856033794618850147)
                  ·
                    refine ⟨43201145784050691928275221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28800763856033794618850147 43201145784050691928275221)
                    ·
                      refine ⟨2025053708627376184137901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43201145784050691928275221 2025053708627376184137901)
                      ·
                        rfl

theorem cell23_3943778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3943778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943778 prefixEnd_3943778 := by exact prefixLift 3943778
  have htrace : WordTrace (prefixWord ++ tailWord_3943778) baseStart_3943778 baseEnd_3943778 := by
    simpa [prefixWord, tailWord_3943778, baseEnd_3943778] using wordTrace_append hprefix tailTrace_3943778
  have hstable : (prefixWord ++ tailWord_3943778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943778).length < 2 ^ (prefixWord ++ tailWord_3943778).sum := by decide
  have hdescent : baseEnd_3943778 < baseStart_3943778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943801 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 2, 7]
def baseStart_3943801 : Nat := 118140960795 + 3943801 * 2 ^ 59
def prefixEnd_3943801 : Nat := 4983230072969 + 3 ^ 40 * 3943801 * 2
def baseEnd_3943801 : Nat := 675021839560809864716765

theorem tailTrace_3943801 : CollatzResearch.WordTrace tailWord_3943801 prefixEnd_3943801 675021839560809864716765 := by
  unfold tailWord_3943801
  simp only [CollatzResearch.WordTrace]
  refine ⟨143842239585289999432047257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95894826390193332954698171 143842239585289999432047257)
  ·
    refine ⟨107881679688967499574035443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143842239585289999432047257 107881679688967499574035443)
    ·
      refine ⟨161822519533451249361053165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107881679688967499574035443 161822519533451249361053165)
      ·
        refine ⟨60683444825044218510394937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161822519533451249361053165 60683444825044218510394937)
        ·
          refine ⟨45512583618783163882796203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60683444825044218510394937 45512583618783163882796203)
          ·
            refine ⟨68268875428174745824194305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45512583618783163882796203 68268875428174745824194305)
            ·
              refine ⟨51201656571131059368145729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68268875428174745824194305 51201656571131059368145729)
              ·
                refine ⟨38401242428348294526109297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51201656571131059368145729 38401242428348294526109297)
                ·
                  refine ⟨28800931821261220894581973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38401242428348294526109297 28800931821261220894581973)
                  ·
                    refine ⟨675021839560809864716765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28800931821261220894581973 675021839560809864716765)
                    ·
                      rfl

theorem cell23_3943801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_3943801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943801 prefixEnd_3943801 := by exact prefixLift 3943801
  have htrace : WordTrace (prefixWord ++ tailWord_3943801) baseStart_3943801 baseEnd_3943801 := by
    simpa [prefixWord, tailWord_3943801, baseEnd_3943801] using wordTrace_append hprefix tailTrace_3943801
  have hstable : (prefixWord ++ tailWord_3943801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943801).length < 2 ^ (prefixWord ++ tailWord_3943801).sum := by decide
  have hdescent : baseEnd_3943801 < baseStart_3943801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943808 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 2, 7, 2]
def baseStart_3943808 : Nat := 118140960795 + 3943808 * 2 ^ 59
def prefixEnd_3943808 : Nat := 4983230072969 + 3 ^ 40 * 3943808 * 2
def baseEnd_3943808 : Nat := 2025069113047011066762763

theorem tailTrace_3943808 : CollatzResearch.WordTrace tailWord_3943808 prefixEnd_3943808 2025069113047011066762763 := by
  unfold tailWord_3943808
  simp only [CollatzResearch.WordTrace]
  refine ⟨71921247448132319813776039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95894996597509759751701385 71921247448132319813776039)
  ·
    refine ⟨107881871172198479720664059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71921247448132319813776039 107881871172198479720664059)
    ·
      refine ⟨161822806758297719580996089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107881871172198479720664059 161822806758297719580996089)
      ·
        refine ⟨121367105068723289685747067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161822806758297719580996089 121367105068723289685747067)
        ·
          refine ⟨182050657603084934528620601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121367105068723289685747067 182050657603084934528620601)
          ·
            refine ⟨136537993202313700896465451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182050657603084934528620601 136537993202313700896465451)
            ·
              refine ⟨204806989803470551344698177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136537993202313700896465451 204806989803470551344698177)
              ·
                refine ⟨153605242352602913508523633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204806989803470551344698177 153605242352602913508523633)
                ·
                  refine ⟨115203931764452185131392725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153605242352602913508523633 115203931764452185131392725)
                  ·
                    refine ⟨2700092150729348089017017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 115203931764452185131392725 2700092150729348089017017)
                    ·
                      refine ⟨2025069113047011066762763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700092150729348089017017 2025069113047011066762763)
                      ·
                        rfl

theorem cell23_3943808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_3943808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943808 prefixEnd_3943808 := by exact prefixLift 3943808
  have htrace : WordTrace (prefixWord ++ tailWord_3943808) baseStart_3943808 baseEnd_3943808 := by
    simpa [prefixWord, tailWord_3943808, baseEnd_3943808] using wordTrace_append hprefix tailTrace_3943808
  have hstable : (prefixWord ++ tailWord_3943808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943808).length < 2 ^ (prefixWord ++ tailWord_3943808).sum := by decide
  have hdescent : baseEnd_3943808 < baseStart_3943808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943815 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_3943815 : Nat := 118140960795 + 3943815 * 2 ^ 59
def prefixEnd_3943815 : Nat := 4983230072969 + 3 ^ 40 * 3943815 * 2
def baseEnd_3943815 : Nat := 2025072707411592539375231

theorem tailTrace_3943815 : CollatzResearch.WordTrace tailWord_3943815 prefixEnd_3943815 2025072707411592539375231 := by
  unfold tailWord_3943815
  simp only [CollatzResearch.WordTrace]
  refine ⟨143842750207239279823056899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95895166804826186548704599 143842750207239279823056899)
  ·
    refine ⟨215764125310858919734585349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143842750207239279823056899 215764125310858919734585349)
    ·
      refine ⟨40455773495786047450234753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215764125310858919734585349 40455773495786047450234753)
      ·
        refine ⟨30341830121839535587676065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40455773495786047450234753 30341830121839535587676065)
        ·
          refine ⟨22756372591379651690757049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30341830121839535587676065 22756372591379651690757049)
          ·
            refine ⟨17067279443534738768067787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22756372591379651690757049 17067279443534738768067787)
            ·
              refine ⟨25600919165302108152101681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17067279443534738768067787 25600919165302108152101681)
              ·
                refine ⟨19200689373976581114076261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25600919165302108152101681 19200689373976581114076261)
                ·
                  refine ⟨3600129257620608958889299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19200689373976581114076261 3600129257620608958889299)
                  ·
                    refine ⟨5400193886430913438333949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3600129257620608958889299 5400193886430913438333949)
                    ·
                      refine ⟨2025072707411592539375231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5400193886430913438333949 2025072707411592539375231)
                      ·
                        rfl

theorem cell23_3943815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_3943815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943815 prefixEnd_3943815 := by exact prefixLift 3943815
  have htrace : WordTrace (prefixWord ++ tailWord_3943815) baseStart_3943815 baseEnd_3943815 := by
    simpa [prefixWord, tailWord_3943815, baseEnd_3943815] using wordTrace_append hprefix tailTrace_3943815
  have hstable : (prefixWord ++ tailWord_3943815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943815).length < 2 ^ (prefixWord ++ tailWord_3943815).sum := by decide
  have hdescent : baseEnd_3943815 < baseStart_3943815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943816 : List Nat := [2, 1, 3, 3, 1, 4, 1, 3, 1, 2, 2]
def baseStart_3943816 : Nat := 118140960795 + 3943816 * 2 ^ 59
def prefixEnd_3943816 : Nat := 4983230072969 + 3 ^ 40 * 3943816 * 2
def baseEnd_3943816 : Nat := 2025073220892247035462727

theorem tailTrace_3943816 : CollatzResearch.WordTrace tailWord_3943816 prefixEnd_3943816 2025073220892247035462727 := by
  unfold tailWord_3943816
  simp only [CollatzResearch.WordTrace]
  refine ⟨71921393340117828496921651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95895191120157104662562201 71921393340117828496921651)
  ·
    refine ⟨107882090010176742745382477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71921393340117828496921651 107882090010176742745382477)
    ·
      refine ⟨40455783753816278529518429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107882090010176742745382477 40455783753816278529518429)
      ·
        refine ⟨15170918907681104448569411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40455783753816278529518429 15170918907681104448569411)
        ·
          refine ⟨22756378361521656672854117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15170918907681104448569411 22756378361521656672854117)
          ·
            refine ⟨4266820942785310626160147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22756378361521656672854117 4266820942785310626160147)
            ·
              refine ⟨6400231414177965939240221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266820942785310626160147 6400231414177965939240221)
              ·
                refine ⟨2400086780316737227215083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6400231414177965939240221 2400086780316737227215083)
                ·
                  refine ⟨3600130170475105840822625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400086780316737227215083 3600130170475105840822625)
                  ·
                    refine ⟨2700097627856329380616969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3600130170475105840822625 2700097627856329380616969)
                    ·
                      refine ⟨2025073220892247035462727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700097627856329380616969 2025073220892247035462727)
                      ·
                        rfl

theorem cell23_3943816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_3943816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943816 prefixEnd_3943816 := by exact prefixLift 3943816
  have htrace : WordTrace (prefixWord ++ tailWord_3943816) baseStart_3943816 baseEnd_3943816 := by
    simpa [prefixWord, tailWord_3943816, baseEnd_3943816] using wordTrace_append hprefix tailTrace_3943816
  have hstable : (prefixWord ++ tailWord_3943816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943816).length < 2 ^ (prefixWord ++ tailWord_3943816).sum := by decide
  have hdescent : baseEnd_3943816 < baseStart_3943816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943858 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_3943858 : Nat := 118140960795 + 3943858 * 2 ^ 59
def prefixEnd_3943858 : Nat := 4983230072969 + 3 ^ 40 * 3943858 * 2
def baseEnd_3943858 : Nat := 2025094787079735871137533

theorem tailTrace_3943858 : CollatzResearch.WordTrace tailWord_3943858 prefixEnd_3943858 2025094787079735871137533 := by
  unfold tailWord_3943858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35961079636520874541718057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95896212364055665444581485 35961079636520874541718057)
  ·
    refine ⟨26970809727390655906288543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35961079636520874541718057 26970809727390655906288543)
    ·
      refine ⟨40456214591085983859432815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26970809727390655906288543 40456214591085983859432815)
      ·
        refine ⟨60684321886628975789149223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40456214591085983859432815 60684321886628975789149223)
        ·
          refine ⟨91026482829943463683723835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60684321886628975789149223 91026482829943463683723835)
          ·
            refine ⟨136539724244915195525585753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91026482829943463683723835 136539724244915195525585753)
            ·
              refine ⟨102404793183686396644189315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136539724244915195525585753 102404793183686396644189315)
              ·
                refine ⟨153607189775529594966283973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102404793183686396644189315 153607189775529594966283973)
                ·
                  refine ⟨28801348082911799056178245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153607189775529594966283973 28801348082911799056178245)
                  ·
                    refine ⟨5400252765545962323033421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28801348082911799056178245 5400252765545962323033421)
                    ·
                      refine ⟨2025094787079735871137533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5400252765545962323033421 2025094787079735871137533)
                      ·
                        rfl

theorem cell23_3943858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_3943858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943858 prefixEnd_3943858 := by exact prefixLift 3943858
  have htrace : WordTrace (prefixWord ++ tailWord_3943858) baseStart_3943858 baseEnd_3943858 := by
    simpa [prefixWord, tailWord_3943858, baseEnd_3943858] using wordTrace_append hprefix tailTrace_3943858
  have hstable : (prefixWord ++ tailWord_3943858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943858).length < 2 ^ (prefixWord ++ tailWord_3943858).sum := by decide
  have hdescent : baseEnd_3943858 < baseStart_3943858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943876 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_3943876 : Nat := 118140960795 + 3943876 * 2 ^ 59
def prefixEnd_3943876 : Nat := 4983230072969 + 3 ^ 40 * 3943876 * 2
def baseEnd_3943876 : Nat := 2025104029731516800712451

theorem tailTrace_3943876 : CollatzResearch.WordTrace tailWord_3943876 prefixEnd_3943876 2025104029731516800712451 := by
  unfold tailWord_3943876
  simp only [CollatzResearch.WordTrace]
  refine ⟨71922487530009143620513741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95896650040012191494018321 71922487530009143620513741)
  ·
    refine ⟨26970932823753428857692653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71922487530009143620513741 26970932823753428857692653)
    ·
      refine ⟨10114099808907535821634745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26970932823753428857692653 10114099808907535821634745)
      ·
        refine ⟨7585574856680651866226059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10114099808907535821634745 7585574856680651866226059)
        ·
          refine ⟨11378362285020977799339089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7585574856680651866226059 11378362285020977799339089)
          ·
            refine ⟨8533771713765733349504317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11378362285020977799339089 8533771713765733349504317)
            ·
              refine ⟨3200164392662150006064119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8533771713765733349504317 3200164392662150006064119)
              ·
                refine ⟨4800246588993225009096179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200164392662150006064119 4800246588993225009096179)
                ·
                  refine ⟨7200369883489837513644269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800246588993225009096179 7200369883489837513644269)
                  ·
                    refine ⟨2700138706308689067616601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7200369883489837513644269 2700138706308689067616601)
                    ·
                      refine ⟨2025104029731516800712451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700138706308689067616601 2025104029731516800712451)
                      ·
                        rfl

theorem cell23_3943876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_3943876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943876 prefixEnd_3943876 := by exact prefixLift 3943876
  have htrace : WordTrace (prefixWord ++ tailWord_3943876) baseStart_3943876 baseEnd_3943876 := by
    simpa [prefixWord, tailWord_3943876, baseEnd_3943876] using wordTrace_append hprefix tailTrace_3943876
  have hstable : (prefixWord ++ tailWord_3943876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943876).length < 2 ^ (prefixWord ++ tailWord_3943876).sum := by decide
  have hdescent : baseEnd_3943876 < baseStart_3943876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943888 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 3]
def baseStart_3943888 : Nat := 118140960795 + 3943888 * 2 ^ 59
def prefixEnd_3943888 : Nat := 4983230072969 + 3 ^ 40 * 3943888 * 2
def baseEnd_3943888 : Nat := 2025110191499370753762395

theorem tailTrace_3943888 : CollatzResearch.WordTrace tailWord_3943888 prefixEnd_3943888 2025110191499370753762395 := by
  unfold tailWord_3943888
  simp only [CollatzResearch.WordTrace]
  refine ⟨71922706367987406645232159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95896941823983208860309545 71922706367987406645232159)
  ·
    refine ⟨107884059551981109967848239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71922706367987406645232159 107884059551981109967848239)
    ·
      refine ⟨161826089327971664951772359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107884059551981109967848239 161826089327971664951772359)
      ·
        refine ⟨242739133991957497427658539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161826089327971664951772359 242739133991957497427658539)
        ·
          refine ⟨364108700987936246141487809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242739133991957497427658539 364108700987936246141487809)
          ·
            refine ⟨273081525740952184606115857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364108700987936246141487809 273081525740952184606115857)
            ·
              refine ⟨204811144305714138454586893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273081525740952184606115857 204811144305714138454586893)
              ·
                refine ⟨76804179114642801920470085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204811144305714138454586893 76804179114642801920470085)
                ·
                  refine ⟨14400783583995525360088141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76804179114642801920470085 14400783583995525360088141)
                  ·
                    refine ⟨5400293843998322010033053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14400783583995525360088141 5400293843998322010033053)
                    ·
                      refine ⟨2025110191499370753762395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5400293843998322010033053 2025110191499370753762395)
                      ·
                        rfl

theorem cell23_3943888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_3943888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943888 prefixEnd_3943888 := by exact prefixLift 3943888
  have htrace : WordTrace (prefixWord ++ tailWord_3943888) baseStart_3943888 baseEnd_3943888 := by
    simpa [prefixWord, tailWord_3943888, baseEnd_3943888] using wordTrace_append hprefix tailTrace_3943888
  have hstable : (prefixWord ++ tailWord_3943888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943888).length < 2 ^ (prefixWord ++ tailWord_3943888).sum := by decide
  have hdescent : baseEnd_3943888 < baseStart_3943888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943905 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_3943905 : Nat := 118140960795 + 3943905 * 2 ^ 59
def prefixEnd_3943905 : Nat := 4983230072969 + 3 ^ 40 * 3943905 * 2
def baseEnd_3943905 : Nat := 2025118920670497187249817

theorem tailTrace_3943905 : CollatzResearch.WordTrace tailWord_3943905 prefixEnd_3943905 2025118920670497187249817 := by
  unfold tailWord_3943905
  simp only [CollatzResearch.WordTrace]
  refine ⟨143846032776913225193833169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95897355184608816795888779 143846032776913225193833169)
  ·
    refine ⟨107884524582684918895374877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143846032776913225193833169 107884524582684918895374877)
    ·
      refine ⟨40456696718506844585765579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107884524582684918895374877 40456696718506844585765579)
      ·
        refine ⟨60685045077760266878648369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40456696718506844585765579 60685045077760266878648369)
        ·
          refine ⟨45513783808320200158986277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60685045077760266878648369 45513783808320200158986277)
          ·
            refine ⟨8533834464060037529809927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45513783808320200158986277 8533834464060037529809927)
            ·
              refine ⟨12800751696090056294714891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8533834464060037529809927 12800751696090056294714891)
              ·
                refine ⟨19201127544135084442072337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12800751696090056294714891 19201127544135084442072337)
                ·
                  refine ⟨14400845658101313331554253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19201127544135084442072337 14400845658101313331554253)
                  ·
                    refine ⟨5400317121787992499332845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14400845658101313331554253 5400317121787992499332845)
                    ·
                      refine ⟨2025118920670497187249817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5400317121787992499332845 2025118920670497187249817)
                      ·
                        rfl

theorem cell23_3943905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_3943905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943905 prefixEnd_3943905 := by exact prefixLift 3943905
  have htrace : WordTrace (prefixWord ++ tailWord_3943905) baseStart_3943905 baseEnd_3943905 := by
    simpa [prefixWord, tailWord_3943905, baseEnd_3943905] using wordTrace_append hprefix tailTrace_3943905
  have hstable : (prefixWord ++ tailWord_3943905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943905).length < 2 ^ (prefixWord ++ tailWord_3943905).sum := by decide
  have hdescent : baseEnd_3943905 < baseStart_3943905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943908 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_3943908 : Nat := 118140960795 + 3943908 * 2 ^ 59
def prefixEnd_3943908 : Nat := 4983230072969 + 3 ^ 40 * 3943908 * 2
def baseEnd_3943908 : Nat := 675040153704153558504101

theorem tailTrace_3943908 : CollatzResearch.WordTrace tailWord_3943908 prefixEnd_3943908 675040153704153558504101 := by
  unfold tailWord_3943908
  simp only [CollatzResearch.WordTrace]
  refine ⟨71923071097951178353096189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95897428130601571137461585 71923071097951178353096189)
  ·
    refine ⟨26971151661731691882411071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71923071097951178353096189 26971151661731691882411071)
    ·
      refine ⟨40456727492597537823616607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26971151661731691882411071 40456727492597537823616607)
      ·
        refine ⟨60685091238896306735424911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40456727492597537823616607 60685091238896306735424911)
        ·
          refine ⟨91027636858344460103137367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60685091238896306735424911 91027636858344460103137367)
          ·
            refine ⟨136541455287516690154706051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91027636858344460103137367 136541455287516690154706051)
            ·
              refine ⟨204812182931275035232059077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136541455287516690154706051 204812182931275035232059077)
              ·
                refine ⟨38402284299614069106011077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204812182931275035232059077 38402284299614069106011077)
                ·
                  refine ⟨7200428306177637957377077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38402284299614069106011077 7200428306177637957377077)
                  ·
                    refine ⟨675040153704153558504101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7200428306177637957377077 675040153704153558504101)
                    ·
                      rfl

theorem cell23_3943908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_3943908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943908 prefixEnd_3943908 := by exact prefixLift 3943908
  have htrace : WordTrace (prefixWord ++ tailWord_3943908) baseStart_3943908 baseEnd_3943908 := by
    simpa [prefixWord, tailWord_3943908, baseEnd_3943908] using wordTrace_append hprefix tailTrace_3943908
  have hstable : (prefixWord ++ tailWord_3943908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943908).length < 2 ^ (prefixWord ++ tailWord_3943908).sum := by decide
  have hdescent : baseEnd_3943908 < baseStart_3943908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943945 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 4, 4, 2]
def baseStart_3943945 : Nat := 118140960795 + 3943945 * 2 ^ 59
def prefixEnd_3943945 : Nat := 4983230072969 + 3 ^ 40 * 3943945 * 2
def baseEnd_3943945 : Nat := 2025139459896677030749633

theorem tailTrace_3943945 : CollatzResearch.WordTrace tailWord_3943945 prefixEnd_3943945 2025139459896677030749633 := by
  unfold tailWord_3943945
  simp only [CollatzResearch.WordTrace]
  refine ⟨143847491696768312025289289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95898327797845541350192859 143847491696768312025289289)
  ·
    refine ⟨107885618772576234018966967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143847491696768312025289289 107885618772576234018966967)
    ·
      refine ⟨161828428158864351028450451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107885618772576234018966967 161828428158864351028450451)
      ·
        refine ⟨242742642238296526542675677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161828428158864351028450451 242742642238296526542675677)
        ·
          refine ⟨91028490839361197453503379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242742642238296526542675677 91028490839361197453503379)
          ·
            refine ⟨136542736259041796180255069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91028490839361197453503379 136542736259041796180255069)
            ·
              refine ⟨51203526097140673567595651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136542736259041796180255069 51203526097140673567595651)
              ·
                refine ⟨76805289145711010351393477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51203526097140673567595651 76805289145711010351393477)
                ·
                  refine ⟨14400991714820814440886277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76805289145711010351393477 14400991714820814440886277)
                  ·
                    refine ⟨2700185946528902707666177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14400991714820814440886277 2700185946528902707666177)
                    ·
                      refine ⟨2025139459896677030749633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700185946528902707666177 2025139459896677030749633)
                      ·
                        rfl

theorem cell23_3943945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 4, 2].length) (baseStart_3943945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943945 prefixEnd_3943945 := by exact prefixLift 3943945
  have htrace : WordTrace (prefixWord ++ tailWord_3943945) baseStart_3943945 baseEnd_3943945 := by
    simpa [prefixWord, tailWord_3943945, baseEnd_3943945] using wordTrace_append hprefix tailTrace_3943945
  have hstable : (prefixWord ++ tailWord_3943945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943945).length < 2 ^ (prefixWord ++ tailWord_3943945).sum := by decide
  have hdescent : baseEnd_3943945 < baseStart_3943945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943955 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 3, 4]
def baseStart_3943955 : Nat := 118140960795 + 3943955 * 2 ^ 59
def prefixEnd_3943955 : Nat := 4983230072969 + 3 ^ 40 * 3943955 * 2
def baseEnd_3943955 : Nat := 675048198234407330541529

theorem tailTrace_3943955 : CollatzResearch.WordTrace tailWord_3943955 prefixEnd_3943955 675048198234407330541529 := by
  unfold tailWord_3943955
  simp only [CollatzResearch.WordTrace]
  refine ⟨143847856426732083733153319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95898570951154722488768879 143847856426732083733153319)
  ·
    refine ⟨215771784640098125599729979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143847856426732083733153319 215771784640098125599729979)
    ·
      refine ⟨323657676960147188399594969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215771784640098125599729979 323657676960147188399594969)
      ·
        refine ⟨242743257720110391299696227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323657676960147188399594969 242743257720110391299696227)
        ·
          refine ⟨364114886580165586949544341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242743257720110391299696227 364114886580165586949544341)
          ·
            refine ⟨17067885308445261888259891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 364114886580165586949544341 17067885308445261888259891)
            ·
              refine ⟨25601827962667892832389837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17067885308445261888259891 25601827962667892832389837)
              ·
                refine ⟨9600685486000459812146189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25601827962667892832389837 9600685486000459812146189)
                ·
                  refine ⟨3600257057250172429554821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9600685486000459812146189 3600257057250172429554821)
                  ·
                    refine ⟨675048198234407330541529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3600257057250172429554821 675048198234407330541529)
                    ·
                      rfl

theorem cell23_3943955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 4].length) (baseStart_3943955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943955 prefixEnd_3943955 := by exact prefixLift 3943955
  have htrace : WordTrace (prefixWord ++ tailWord_3943955) baseStart_3943955 baseEnd_3943955 := by
    simpa [prefixWord, tailWord_3943955, baseEnd_3943955] using wordTrace_append hprefix tailTrace_3943955
  have hstable : (prefixWord ++ tailWord_3943955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943955).length < 2 ^ (prefixWord ++ tailWord_3943955).sum := by decide
  have hdescent : baseEnd_3943955 < baseStart_3943955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943965 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_3943965 : Nat := 118140960795 + 3943965 * 2 ^ 59
def prefixEnd_3943965 : Nat := 4983230072969 + 3 ^ 40 * 3943965 * 2
def baseEnd_3943965 : Nat := 2025149729509766952499541

theorem tailTrace_3943965 : CollatzResearch.WordTrace tailWord_3943965 prefixEnd_3943965 2025149729509766952499541 := by
  unfold tailWord_3943965
  simp only [CollatzResearch.WordTrace]
  refine ⟨143848221156695855441017349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95898814104463903627344899 143848221156695855441017349)
  ·
    refine ⟨26971541466880472895190753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143848221156695855441017349 26971541466880472895190753)
    ·
      refine ⟨20228656100160354671393065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26971541466880472895190753 20228656100160354671393065)
      ·
        refine ⟨15171492075120266003544799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20228656100160354671393065 15171492075120266003544799)
        ·
          refine ⟨22757238112680399005317199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15171492075120266003544799 22757238112680399005317199)
          ·
            refine ⟨34135857169020598507975799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22757238112680399005317199 34135857169020598507975799)
            ·
              refine ⟨51203785753530897761963699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34135857169020598507975799 51203785753530897761963699)
              ·
                refine ⟨76805678630296346642945549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51203785753530897761963699 76805678630296346642945549)
                ·
                  refine ⟨28802129486361129991104581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76805678630296346642945549 28802129486361129991104581)
                  ·
                    refine ⟨5400399278692711873332109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28802129486361129991104581 5400399278692711873332109)
                    ·
                      refine ⟨2025149729509766952499541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5400399278692711873332109 2025149729509766952499541)
                      ·
                        rfl

theorem cell23_3943965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_3943965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943965 prefixEnd_3943965 := by exact prefixLift 3943965
  have htrace : WordTrace (prefixWord ++ tailWord_3943965) baseStart_3943965 baseEnd_3943965 := by
    simpa [prefixWord, tailWord_3943965, baseEnd_3943965] using wordTrace_append hprefix tailTrace_3943965
  have hstable : (prefixWord ++ tailWord_3943965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943965).length < 2 ^ (prefixWord ++ tailWord_3943965).sum := by decide
  have hdescent : baseEnd_3943965 < baseStart_3943965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943982 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3943982 : Nat := 118140960795 + 3943982 * 2 ^ 59
def prefixEnd_3943982 : Nat := 4983230072969 + 3 ^ 40 * 3943982 * 2
def baseEnd_3943982 : Nat := 2025158458680893385986963

theorem tailTrace_3943982 : CollatzResearch.WordTrace tailWord_3943982 prefixEnd_3943982 2025158458680893385986963 := by
  unfold tailWord_3943982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17981105149704283418048275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95899227465089511562924133 17981105149704283418048275)
  ·
    refine ⟨26971657724556425127072413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17981105149704283418048275 26971657724556425127072413)
    ·
      refine ⟨10114371646708659422652155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26971657724556425127072413 10114371646708659422652155)
      ·
        refine ⟨15171557470062989133978233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10114371646708659422652155 15171557470062989133978233)
        ·
          refine ⟨11378668102547241850483675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15171557470062989133978233 11378668102547241850483675)
          ·
            refine ⟨17068002153820862775725513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11378668102547241850483675 17068002153820862775725513)
            ·
              refine ⟨12801001615365647081794135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17068002153820862775725513 12801001615365647081794135)
              ·
                refine ⟨19201502423048470622691203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12801001615365647081794135 19201502423048470622691203)
                ·
                  refine ⟨28802253634572705934036805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19201502423048470622691203 28802253634572705934036805)
                  ·
                    refine ⟨5400422556482382362631901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28802253634572705934036805 5400422556482382362631901)
                    ·
                      refine ⟨2025158458680893385986963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5400422556482382362631901 2025158458680893385986963)
                      ·
                        rfl

theorem cell23_3943982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3943982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943982 prefixEnd_3943982 := by exact prefixLift 3943982
  have htrace : WordTrace (prefixWord ++ tailWord_3943982) baseStart_3943982 baseEnd_3943982 := by
    simpa [prefixWord, tailWord_3943982, baseEnd_3943982] using wordTrace_append hprefix tailTrace_3943982
  have hstable : (prefixWord ++ tailWord_3943982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943982).length < 2 ^ (prefixWord ++ tailWord_3943982).sum := by decide
  have hdescent : baseEnd_3943982 < baseStart_3943982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943989 : List Nat := [1, 3, 3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3943989 : Nat := 118140960795 + 3943989 * 2 ^ 59
def prefixEnd_3943989 : Nat := 4983230072969 + 3 ^ 40 * 3943989 * 2
def baseEnd_3943989 : Nat := 675054017681824952866477

theorem tailTrace_3943989 : CollatzResearch.WordTrace tailWord_3943989 prefixEnd_3943989 675054017681824952866477 := by
  unfold tailWord_3943989
  simp only [CollatzResearch.WordTrace]
  refine ⟨143849096508608907539891021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95899397672405938359927347 143849096508608907539891021)
  ·
    refine ⟨53943411190728340327459133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143849096508608907539891021 53943411190728340327459133)
    ·
      refine ⟨20228779196523127622797175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53943411190728340327459133 20228779196523127622797175)
      ·
        refine ⟨30343168794784691434195763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20228779196523127622797175 30343168794784691434195763)
        ·
          refine ⟨45514753192177037151293645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30343168794784691434195763 45514753192177037151293645)
          ·
            refine ⟨17068032447066388931735117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45514753192177037151293645 17068032447066388931735117)
            ·
              refine ⟨6400512167649895849400669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17068032447066388931735117 6400512167649895849400669)
              ·
                refine ⟨2400192062868710943525251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6400512167649895849400669 2400192062868710943525251)
                ·
                  refine ⟨3600288094303066415287877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400192062868710943525251 3600288094303066415287877)
                  ·
                    refine ⟨675054017681824952866477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3600288094303066415287877 675054017681824952866477)
                    ·
                      rfl

theorem cell23_3943989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3943989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943989 prefixEnd_3943989 := by exact prefixLift 3943989
  have htrace : WordTrace (prefixWord ++ tailWord_3943989) baseStart_3943989 baseEnd_3943989 := by
    simpa [prefixWord, tailWord_3943989, baseEnd_3943989] using wordTrace_append hprefix tailTrace_3943989
  have hstable : (prefixWord ++ tailWord_3943989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943989).length < 2 ^ (prefixWord ++ tailWord_3943989).sum := by decide
  have hdescent : baseEnd_3943989 < baseStart_3943989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944008 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_3944008 : Nat := 118140960795 + 3944008 * 2 ^ 59
def prefixEnd_3944008 : Nat := 4983230072969 + 3 ^ 40 * 3944008 * 2
def baseEnd_3944008 : Nat := 2025171809177910284261843

theorem tailTrace_3944008 : CollatzResearch.WordTrace tailWord_3944008 prefixEnd_3944008 2025171809177910284261843 := by
  unfold tailWord_3944008
  simp only [CollatzResearch.WordTrace]
  refine ⟨71924894747770036892416339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95899859663693382523221785 71924894747770036892416339)
  ·
    refine ⟨107887342121655055338624509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71924894747770036892416339 107887342121655055338624509)
    ·
      refine ⟨40457753295620645751984191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107887342121655055338624509 40457753295620645751984191)
      ·
        refine ⟨60686629943430968627976287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40457753295620645751984191 60686629943430968627976287)
        ·
          refine ⟨91029944915146452941964431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60686629943430968627976287 91029944915146452941964431)
          ·
            refine ⟨136544917372719679412946647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91029944915146452941964431 136544917372719679412946647)
            ·
              refine ⟨204817376059079519119419971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136544917372719679412946647 204817376059079519119419971)
              ·
                refine ⟨307226064088619278679129957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204817376059079519119419971 307226064088619278679129957)
                ·
                  refine ⟨57604887016616114752336867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307226064088619278679129957 57604887016616114752336867)
                  ·
                    refine ⟨86407330524924172128505301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57604887016616114752336867 86407330524924172128505301)
                    ·
                      refine ⟨2025171809177910284261843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86407330524924172128505301 2025171809177910284261843)
                      ·
                        rfl

theorem cell23_3944008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_3944008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944008 prefixEnd_3944008 := by exact prefixLift 3944008
  have htrace : WordTrace (prefixWord ++ tailWord_3944008) baseStart_3944008 baseEnd_3944008 := by
    simpa [prefixWord, tailWord_3944008, baseEnd_3944008] using wordTrace_append hprefix tailTrace_3944008
  have hstable : (prefixWord ++ tailWord_3944008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944008).length < 2 ^ (prefixWord ++ tailWord_3944008).sum := by decide
  have hdescent : baseEnd_3944008 < baseStart_3944008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944069 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 3, 2, 2]
def baseStart_3944069 : Nat := 118140960795 + 3944069 * 2 ^ 59
def prefixEnd_3944069 : Nat := 4983230072969 + 3 ^ 40 * 3944069 * 2
def baseEnd_3944069 : Nat := 2025203131497834545599063

theorem tailTrace_3944069 : CollatzResearch.WordTrace tailWord_3944069 prefixEnd_3944069 2025203131497834545599063 := by
  unfold tailWord_3944069
  simp only [CollatzResearch.WordTrace]
  refine ⟨143852014348319081202803261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95901342898879387468535507 143852014348319081202803261)
  ·
    refine ⟨53944505380619655451051223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143852014348319081202803261 53944505380619655451051223)
    ·
      refine ⟨80916758070929483176576835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53944505380619655451051223 80916758070929483176576835)
      ·
        refine ⟨121375137106394224764865253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80916758070929483176576835 121375137106394224764865253)
        ·
          refine ⟨22757838207448917143412235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121375137106394224764865253 22757838207448917143412235)
          ·
            refine ⟨34136757311173375715118353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22757838207448917143412235 34136757311173375715118353)
            ·
              refine ⟨25602567983380031786338765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34136757311173375715118353 25602567983380031786338765)
              ·
                refine ⟨9600962993767511919877037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25602567983380031786338765 9600962993767511919877037)
                ·
                  refine ⟨3600361122662816969953889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9600962993767511919877037 3600361122662816969953889)
                  ·
                    refine ⟨2700270841997112727465417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3600361122662816969953889 2700270841997112727465417)
                    ·
                      refine ⟨2025203131497834545599063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700270841997112727465417 2025203131497834545599063)
                      ·
                        rfl

theorem cell23_3944069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_3944069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944069 prefixEnd_3944069 := by exact prefixLift 3944069
  have htrace : WordTrace (prefixWord ++ tailWord_3944069) baseStart_3944069 baseEnd_3944069 := by
    simpa [prefixWord, tailWord_3944069, baseEnd_3944069] using wordTrace_append hprefix tailTrace_3944069
  have hstable : (prefixWord ++ tailWord_3944069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944069).length < 2 ^ (prefixWord ++ tailWord_3944069).sum := by decide
  have hdescent : baseEnd_3944069 < baseStart_3944069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944119 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 3]
def baseStart_3944119 : Nat := 118140960795 + 3944119 * 2 ^ 59
def prefixEnd_3944119 : Nat := 4983230072969 + 3 ^ 40 * 3944119 * 2
def baseEnd_3944119 : Nat := 2025228805530559349973833

theorem tailTrace_3944119 : CollatzResearch.WordTrace tailWord_3944119 prefixEnd_3944119 2025228805530559349973833 := by
  unfold tailWord_3944119
  simp only [CollatzResearch.WordTrace]
  refine ⟨143853837998137939742123411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95902558665425293161415607 143853837998137939742123411)
  ·
    refine ⟨215780756997206909613185117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143853837998137939742123411 215780756997206909613185117)
    ·
      refine ⟨80917783873952591104944419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215780756997206909613185117 80917783873952591104944419)
      ·
        refine ⟨121376675810928886657416629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80917783873952591104944419 121376675810928886657416629)
        ·
          refine ⟨11379063357274583124132809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121376675810928886657416629 11379063357274583124132809)
          ·
            refine ⟨8534297517955937343099607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11379063357274583124132809 8534297517955937343099607)
            ·
              refine ⟨12801446276933906014649411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534297517955937343099607 12801446276933906014649411)
              ·
                refine ⟨19202169415400859021974117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12801446276933906014649411 19202169415400859021974117)
                ·
                  refine ⟨3600406765387661066620147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19202169415400859021974117 3600406765387661066620147)
                  ·
                    refine ⟨5400610148081491599930221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3600406765387661066620147 5400610148081491599930221)
                    ·
                      refine ⟨2025228805530559349973833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5400610148081491599930221 2025228805530559349973833)
                      ·
                        rfl

theorem cell23_3944119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_3944119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944119 prefixEnd_3944119 := by exact prefixLift 3944119
  have htrace : WordTrace (prefixWord ++ tailWord_3944119) baseStart_3944119 baseEnd_3944119 := by
    simpa [prefixWord, tailWord_3944119, baseEnd_3944119] using wordTrace_append hprefix tailTrace_3944119
  have hstable : (prefixWord ++ tailWord_3944119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944119).length < 2 ^ (prefixWord ++ tailWord_3944119).sum := by decide
  have hdescent : baseEnd_3944119 < baseStart_3944119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944130 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3944130 : Nat := 118140960795 + 3944130 * 2 ^ 59
def prefixEnd_3944130 : Nat := 4983230072969 + 3 ^ 40 * 3944130 * 2
def baseEnd_3944130 : Nat := 675078151272586268978761

theorem tailTrace_3944130 : CollatzResearch.WordTrace tailWord_3944130 prefixEnd_3944130 675078151272586268978761 := by
  unfold tailWord_3944130
  simp only [CollatzResearch.WordTrace]
  refine ⟨35963559800274522155193461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95902826134065392413849229 35963559800274522155193461)
  ·
    refine ⟨3371583731275736452049387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35963559800274522155193461 3371583731275736452049387)
    ·
      refine ⟨5057375596913604678074081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371583731275736452049387 5057375596913604678074081)
      ·
        refine ⟨3793031697685203508555561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5057375596913604678074081 3793031697685203508555561)
        ·
          refine ⟨2844773773263902631416671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3793031697685203508555561 2844773773263902631416671)
          ·
            refine ⟨4267160659895853947125007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844773773263902631416671 4267160659895853947125007)
            ·
              refine ⟨6400740989843780920687511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267160659895853947125007 6400740989843780920687511)
              ·
                refine ⟨9601111484765671381031267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6400740989843780920687511 9601111484765671381031267)
                ·
                  refine ⟨14401667227148507071546901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9601111484765671381031267 14401667227148507071546901)
                  ·
                    refine ⟨675078151272586268978761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14401667227148507071546901 675078151272586268978761)
                    ·
                      rfl

theorem cell23_3944130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3944130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944130 prefixEnd_3944130 := by exact prefixLift 3944130
  have htrace : WordTrace (prefixWord ++ tailWord_3944130) baseStart_3944130 baseEnd_3944130 := by
    simpa [prefixWord, tailWord_3944130, baseEnd_3944130] using wordTrace_append hprefix tailTrace_3944130
  have hstable : (prefixWord ++ tailWord_3944130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944130).length < 2 ^ (prefixWord ++ tailWord_3944130).sum := by decide
  have hdescent : baseEnd_3944130 < baseStart_3944130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944135 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 2, 6]
def baseStart_3944135 : Nat := 118140960795 + 3944135 * 2 ^ 59
def prefixEnd_3944135 : Nat := 4983230072969 + 3 ^ 40 * 3944135 * 2
def baseEnd_3944135 : Nat := 675079007073677095791253

theorem tailTrace_3944135 : CollatzResearch.WordTrace tailWord_3944135 prefixEnd_3944135 675079007073677095791253 := by
  unfold tailWord_3944135
  simp only [CollatzResearch.WordTrace]
  refine ⟨143854421566079974474705859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95902947710719982983137239 143854421566079974474705859)
  ·
    refine ⟨215781632349119961712058789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143854421566079974474705859 215781632349119961712058789)
    ·
      refine ⟨40459056065459992821011023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215781632349119961712058789 40459056065459992821011023)
      ·
        refine ⟨60688584098189989231516535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40459056065459992821011023 60688584098189989231516535)
        ·
          refine ⟨91032876147284983847274803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60688584098189989231516535 91032876147284983847274803)
          ·
            refine ⟨136549314220927475770912205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91032876147284983847274803 136549314220927475770912205)
            ·
              refine ⟨51205992832847803414092077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136549314220927475770912205 51205992832847803414092077)
              ·
                refine ⟨19202247312317926280284529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51205992832847803414092077 19202247312317926280284529)
                ·
                  refine ⟨14401685484238444710213397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19202247312317926280284529 14401685484238444710213397)
                  ·
                    refine ⟨675079007073677095791253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14401685484238444710213397 675079007073677095791253)
                    ·
                      rfl

theorem cell23_3944135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_3944135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944135 prefixEnd_3944135 := by exact prefixLift 3944135
  have htrace : WordTrace (prefixWord ++ tailWord_3944135) baseStart_3944135 baseEnd_3944135 := by
    simpa [prefixWord, tailWord_3944135, baseEnd_3944135] using wordTrace_append hprefix tailTrace_3944135
  have hstable : (prefixWord ++ tailWord_3944135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944135).length < 2 ^ (prefixWord ++ tailWord_3944135).sum := by decide
  have hdescent : baseEnd_3944135 < baseStart_3944135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944136 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_3944136 : Nat := 118140960795 + 3944136 * 2 ^ 59
def prefixEnd_3944136 : Nat := 4983230072969 + 3 ^ 40 * 3944136 * 2
def baseEnd_3944136 : Nat := 2025237534701685783461255

theorem tailTrace_3944136 : CollatzResearch.WordTrace tailWord_3944136 prefixEnd_3944136 2025237534701685783461255 := by
  unfold tailWord_3944136
  simp only [CollatzResearch.WordTrace]
  refine ⟨71927229019538175822746131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95902972026050901096994841 71927229019538175822746131)
  ·
    refine ⟨107890843529307263734119197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71927229019538175822746131 107890843529307263734119197)
    ·
      refine ⟨40459066323490223900294699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107890843529307263734119197 40459066323490223900294699)
      ·
        refine ⟨60688599485235335850442049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40459066323490223900294699 60688599485235335850442049)
        ·
          refine ⟨45516449613926501887831537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60688599485235335850442049 45516449613926501887831537)
          ·
            refine ⟨34137337210444876415873653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45516449613926501887831537 34137337210444876415873653)
            ·
              refine ⟨3200375363479207163988155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34137337210444876415873653 3200375363479207163988155)
              ·
                refine ⟨4800563045218810745982233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200375363479207163988155 4800563045218810745982233)
                ·
                  refine ⟨3600422283914108059486675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4800563045218810745982233 3600422283914108059486675)
                  ·
                    refine ⟨5400633425871162089230013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3600422283914108059486675 5400633425871162089230013)
                    ·
                      refine ⟨2025237534701685783461255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5400633425871162089230013 2025237534701685783461255)
                      ·
                        rfl

theorem cell23_3944136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_3944136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944136 prefixEnd_3944136 := by exact prefixLift 3944136
  have htrace : WordTrace (prefixWord ++ tailWord_3944136) baseStart_3944136 baseEnd_3944136 := by
    simpa [prefixWord, tailWord_3944136, baseEnd_3944136] using wordTrace_append hprefix tailTrace_3944136
  have hstable : (prefixWord ++ tailWord_3944136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944136).length < 2 ^ (prefixWord ++ tailWord_3944136).sum := by decide
  have hdescent : baseEnd_3944136 < baseStart_3944136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944146 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_3944146 : Nat := 118140960795 + 3944146 * 2 ^ 59
def prefixEnd_3944146 : Nat := 4983230072969 + 3 ^ 40 * 3944146 * 2
def baseEnd_3944146 : Nat := 2025242669508230744336209

theorem tailTrace_3944146 : CollatzResearch.WordTrace tailWord_3944146 prefixEnd_3944146 2025242669508230744336209 := by
  unfold tailWord_3944146
  simp only [CollatzResearch.WordTrace]
  refine ⟨35963705692260030838339073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95903215179360082235570861 35963705692260030838339073)
  ·
    refine ⟨26972779269195023128754305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35963705692260030838339073 26972779269195023128754305)
    ·
      refine ⟨20229584451896267346565729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26972779269195023128754305 20229584451896267346565729)
      ·
        refine ⟨15172188338922200509924297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20229584451896267346565729 15172188338922200509924297)
        ·
          refine ⟨11379141254191650382443223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15172188338922200509924297 11379141254191650382443223)
          ·
            refine ⟨17068711881287475573664835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11379141254191650382443223 17068711881287475573664835)
            ·
              refine ⟨25603067821931213360497253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17068711881287475573664835 25603067821931213360497253)
              ·
                refine ⟨4800575216612102505093235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25603067821931213360497253 4800575216612102505093235)
                ·
                  refine ⟨7200862824918153757639853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800575216612102505093235 7200862824918153757639853)
                  ·
                    refine ⟨2700323559344307659114945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7200862824918153757639853 2700323559344307659114945)
                    ·
                      refine ⟨2025242669508230744336209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700323559344307659114945 2025242669508230744336209)
                      ·
                        rfl

theorem cell23_3944146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_3944146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944146 prefixEnd_3944146 := by exact prefixLift 3944146
  have htrace : WordTrace (prefixWord ++ tailWord_3944146) baseStart_3944146 baseEnd_3944146 := by
    simpa [prefixWord, tailWord_3944146, baseEnd_3944146] using wordTrace_append hprefix tailTrace_3944146
  have hstable : (prefixWord ++ tailWord_3944146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944146).length < 2 ^ (prefixWord ++ tailWord_3944146).sum := by decide
  have hdescent : baseEnd_3944146 < baseStart_3944146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944159 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 6, 2, 2]
def baseStart_3944159 : Nat := 118140960795 + 3944159 * 2 ^ 59
def prefixEnd_3944159 : Nat := 4983230072969 + 3 ^ 40 * 3944159 * 2
def baseEnd_3944159 : Nat := 2025249344756739193473649

theorem tailTrace_3944159 : CollatzResearch.WordTrace tailWord_3944159 prefixEnd_3944159 2025249344756739193473649 := by
  unfold tailWord_3944159
  simp only [CollatzResearch.WordTrace]
  refine ⟨143855296917993026573579531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95903531278662017715719687 143855296917993026573579531)
  ·
    refine ⟨215782945376989539860369297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143855296917993026573579531 215782945376989539860369297)
    ·
      refine ⟨161837209032742154895276973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215782945376989539860369297 161837209032742154895276973)
      ·
        refine ⟨60688953387278308085728865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161837209032742154895276973 60688953387278308085728865)
        ·
          refine ⟨45516715040458731064296649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60688953387278308085728865 45516715040458731064296649)
          ·
            refine ⟨34137536280344048298222487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45516715040458731064296649 34137536280344048298222487)
            ·
              refine ⟨51206304420516072447333731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34137536280344048298222487 51206304420516072447333731)
              ·
                refine ⟨76809456630774108671000597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51206304420516072447333731 76809456630774108671000597)
                ·
                  refine ⟨3600443279567536343953153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76809456630774108671000597 3600443279567536343953153)
                  ·
                    refine ⟨2700332459675652257964865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3600443279567536343953153 2700332459675652257964865)
                    ·
                      refine ⟨2025249344756739193473649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700332459675652257964865 2025249344756739193473649)
                      ·
                        rfl

theorem cell23_3944159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_3944159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944159 prefixEnd_3944159 := by exact prefixLift 3944159
  have htrace : WordTrace (prefixWord ++ tailWord_3944159) baseStart_3944159 baseEnd_3944159 := by
    simpa [prefixWord, tailWord_3944159, baseEnd_3944159] using wordTrace_append hprefix tailTrace_3944159
  have hstable : (prefixWord ++ tailWord_3944159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944159).length < 2 ^ (prefixWord ++ tailWord_3944159).sum := by decide
  have hdescent : baseEnd_3944159 < baseStart_3944159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944175 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_3944175 : Nat := 118140960795 + 3944175 * 2 ^ 59
def prefixEnd_3944175 : Nat := 4983230072969 + 3 ^ 40 * 3944175 * 2
def baseEnd_3944175 : Nat := 2025257560447211130873575

theorem tailTrace_3944175 : CollatzResearch.WordTrace tailWord_3944175 prefixEnd_3944175 2025257560447211130873575 := by
  unfold tailWord_3944175
  simp only [CollatzResearch.WordTrace]
  refine ⟨143855880485935061306161979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95903920323956707537441319 143855880485935061306161979)
  ·
    refine ⟨215783820728902591959242969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143855880485935061306161979 215783820728902591959242969)
    ·
      refine ⟨161837865546676943969432227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215783820728902591959242969 161837865546676943969432227)
      ·
        refine ⟨242756798320015415954148341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161837865546676943969432227 242756798320015415954148341)
        ·
          refine ⟨22758449842501445245701407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242756798320015415954148341 22758449842501445245701407)
          ·
            refine ⟨34137674763752167868552111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22758449842501445245701407 34137674763752167868552111)
            ·
              refine ⟨51206512145628251802828167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34137674763752167868552111 51206512145628251802828167)
              ·
                refine ⟨76809768218442377704242251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51206512145628251802828167 76809768218442377704242251)
                ·
                  refine ⟨115214652327663566556363377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76809768218442377704242251 115214652327663566556363377)
                  ·
                    refine ⟨86410989245747674917272533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115214652327663566556363377 86410989245747674917272533)
                    ·
                      refine ⟨2025257560447211130873575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86410989245747674917272533 2025257560447211130873575)
                      ·
                        rfl

theorem cell23_3944175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_3944175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944175 prefixEnd_3944175 := by exact prefixLift 3944175
  have htrace : WordTrace (prefixWord ++ tailWord_3944175) baseStart_3944175 baseEnd_3944175 := by
    simpa [prefixWord, tailWord_3944175, baseEnd_3944175] using wordTrace_append hprefix tailTrace_3944175
  have hstable : (prefixWord ++ tailWord_3944175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944175).length < 2 ^ (prefixWord ++ tailWord_3944175).sum := by decide
  have hdescent : baseEnd_3944175 < baseStart_3944175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944193 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_3944193 : Nat := 118140960795 + 3944193 * 2 ^ 59
def prefixEnd_3944193 : Nat := 4983230072969 + 3 ^ 40 * 3944193 * 2
def baseEnd_3944193 : Nat := 2025266803098992060448493

theorem tailTrace_3944193 : CollatzResearch.WordTrace tailWord_3944193 prefixEnd_3944193 2025266803098992060448493 := by
  unfold tailWord_3944193
  simp only [CollatzResearch.WordTrace]
  refine ⟨143856536999869850380317233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95904357999913233586878155 143856536999869850380317233)
  ·
    refine ⟨107892402749902387785237925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143856536999869850380317233 107892402749902387785237925)
    ·
      refine ⟨20229825515606697709732111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107892402749902387785237925 20229825515606697709732111)
      ·
        refine ⟨30344738273410046564598167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20229825515606697709732111 30344738273410046564598167)
        ·
          refine ⟨45517107410115069846897251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30344738273410046564598167 45517107410115069846897251)
          ·
            refine ⟨68275661115172604770345877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45517107410115069846897251 68275661115172604770345877)
            ·
              refine ⟨3200421614773715848609963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68275661115172604770345877 3200421614773715848609963)
              ·
                refine ⟨4800632422160573772914945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200421614773715848609963 4800632422160573772914945)
                ·
                  refine ⟨3600474316620430329686209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4800632422160573772914945 3600474316620430329686209)
                  ·
                    refine ⟨2700355737465322747264657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3600474316620430329686209 2700355737465322747264657)
                    ·
                      refine ⟨2025266803098992060448493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700355737465322747264657 2025266803098992060448493)
                      ·
                        rfl

theorem cell23_3944193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_3944193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944193 prefixEnd_3944193 := by exact prefixLift 3944193
  have htrace : WordTrace (prefixWord ++ tailWord_3944193) baseStart_3944193 baseEnd_3944193 := by
    simpa [prefixWord, tailWord_3944193, baseEnd_3944193] using wordTrace_append hprefix tailTrace_3944193
  have hstable : (prefixWord ++ tailWord_3944193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944193).length < 2 ^ (prefixWord ++ tailWord_3944193).sum := by decide
  have hdescent : baseEnd_3944193 < baseStart_3944193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944195 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 3, 7]
def baseStart_3944195 : Nat := 118140960795 + 3944195 * 2 ^ 59
def prefixEnd_3944195 : Nat := 4983230072969 + 3 ^ 40 * 3944195 * 2
def baseEnd_3944195 : Nat := 675089276686767017541161

theorem tailTrace_3944195 : CollatzResearch.WordTrace tailWord_3944195 prefixEnd_3944195 675089276686767017541161 := by
  unfold tailWord_3944195
  simp only [CollatzResearch.WordTrace]
  refine ⟨143856609945862604721890039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95904406630575069814593359 143856609945862604721890039)
  ·
    refine ⟨215784914918793907082835059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143856609945862604721890039 215784914918793907082835059)
    ·
      refine ⟨323677372378190860624252589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215784914918793907082835059 323677372378190860624252589)
      ·
        refine ⟨121379014641821572734094721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323677372378190860624252589 121379014641821572734094721)
        ·
          refine ⟨91034260981366179550571041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121379014641821572734094721 91034260981366179550571041)
          ·
            refine ⟨68275695736024634662928281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91034260981366179550571041 68275695736024634662928281)
            ·
              refine ⟨51206771802018475997196211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68275695736024634662928281 51206771802018475997196211)
              ·
                refine ⟨76810157703027713995794317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51206771802018475997196211 76810157703027713995794317)
                ·
                  refine ⟨28803809138635392748422869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76810157703027713995794317 28803809138635392748422869)
                  ·
                    refine ⟨675089276686767017541161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28803809138635392748422869 675089276686767017541161)
                    ·
                      rfl

theorem cell23_3944195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 7].length) (baseStart_3944195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944195 prefixEnd_3944195 := by exact prefixLift 3944195
  have htrace : WordTrace (prefixWord ++ tailWord_3944195) baseStart_3944195 baseEnd_3944195 := by
    simpa [prefixWord, tailWord_3944195, baseEnd_3944195] using wordTrace_append hprefix tailTrace_3944195
  have hstable : (prefixWord ++ tailWord_3944195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944195).length < 2 ^ (prefixWord ++ tailWord_3944195).sum := by decide
  have hdescent : baseEnd_3944195 < baseStart_3944195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944259 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 3, 4]
def baseStart_3944259 : Nat := 118140960795 + 3944259 * 2 ^ 59
def prefixEnd_3944259 : Nat := 4983230072969 + 3 ^ 40 * 3944259 * 2
def baseEnd_3944259 : Nat := 675100230940729600741063

theorem tailTrace_3944259 : CollatzResearch.WordTrace tailWord_3944259 prefixEnd_3944259 675100230940729600741063 := by
  unfold tailWord_3944259
  simp only [CollatzResearch.WordTrace]
  refine ⟨143858944217630743652219831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95905962811753829101479887 143858944217630743652219831)
  ·
    refine ⟨215788416326446115478329747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143858944217630743652219831 215788416326446115478329747)
    ·
      refine ⟨323682624489669173217494621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215788416326446115478329747 323682624489669173217494621)
      ·
        refine ⟨121380984183625939956560483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323682624489669173217494621 121380984183625939956560483)
        ·
          refine ⟨182071476275438909934840725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121380984183625939956560483 182071476275438909934840725)
          ·
            refine ⟨8534600450411198903195659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182071476275438909934840725 8534600450411198903195659)
            ·
              refine ⟨12801900675616798354793489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534600450411198903195659 12801900675616798354793489)
              ·
                refine ⟨9601425506712598766095117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12801900675616798354793489 9601425506712598766095117)
                ·
                  refine ⟨3600534565017224537285669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9601425506712598766095117 3600534565017224537285669)
                  ·
                    refine ⟨675100230940729600741063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3600534565017224537285669 675100230940729600741063)
                    ·
                      rfl

theorem cell23_3944259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 4].length) (baseStart_3944259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944259 prefixEnd_3944259 := by exact prefixLift 3944259
  have htrace : WordTrace (prefixWord ++ tailWord_3944259) baseStart_3944259 baseEnd_3944259 := by
    simpa [prefixWord, tailWord_3944259, baseEnd_3944259] using wordTrace_append hprefix tailTrace_3944259
  have hstable : (prefixWord ++ tailWord_3944259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944259).length < 2 ^ (prefixWord ++ tailWord_3944259).sum := by decide
  have hdescent : baseEnd_3944259 < baseStart_3944259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944332 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_3944332 : Nat := 118140960795 + 3944332 * 2 ^ 59
def prefixEnd_3944332 : Nat := 4983230072969 + 3 ^ 40 * 3944332 * 2
def baseEnd_3944332 : Nat := 675112725636655672203451

theorem tailTrace_3944332 : CollatzResearch.WordTrace tailWord_3944332 prefixEnd_3944332 675112725636655672203451 := by
  unfold tailWord_3944332
  simp only [CollatzResearch.WordTrace]
  refine ⟨71930803373183138559813625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95907737830910851413084833 71930803373183138559813625)
  ·
    refine ⟨53948102529887353919860219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71930803373183138559813625 53948102529887353919860219)
    ·
      refine ⟨80922153794831030879790329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53948102529887353919860219 80922153794831030879790329)
      ·
        refine ⟨60691615346123273159842747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80922153794831030879790329 60691615346123273159842747)
        ·
          refine ⟨91037423019184909739764121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60691615346123273159842747 91037423019184909739764121)
          ·
            refine ⟨68278067264388682304823091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91037423019184909739764121 68278067264388682304823091)
            ·
              refine ⟨102417100896583023457234637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68278067264388682304823091 102417100896583023457234637)
              ·
                refine ⟨38406412836218633796462989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102417100896583023457234637 38406412836218633796462989)
                ·
                  refine ⟨14402404813581987673673621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38406412836218633796462989 14402404813581987673673621)
                  ·
                    refine ⟨675112725636655672203451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14402404813581987673673621 675112725636655672203451)
                    ·
                      rfl

theorem cell23_3944332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_3944332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944332 prefixEnd_3944332 := by exact prefixLift 3944332
  have htrace : WordTrace (prefixWord ++ tailWord_3944332) baseStart_3944332 baseEnd_3944332 := by
    simpa [prefixWord, tailWord_3944332, baseEnd_3944332] using wordTrace_append hprefix tailTrace_3944332
  have hstable : (prefixWord ++ tailWord_3944332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944332).length < 2 ^ (prefixWord ++ tailWord_3944332).sum := by decide
  have hdescent : baseEnd_3944332 < baseStart_3944332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944369 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3944369 : Nat := 118140960795 + 3944369 * 2 ^ 59
def prefixEnd_3944369 : Nat := 4983230072969 + 3 ^ 40 * 3944369 * 2
def baseEnd_3944369 : Nat := 2025357175694183371847683

theorem tailTrace_3944369 : CollatzResearch.WordTrace tailWord_3944369 prefixEnd_3944369 2025357175694183371847683 := by
  unfold tailWord_3944369
  simp only [CollatzResearch.WordTrace]
  refine ⟨143862956247232232438724161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95908637498154821625816107 143862956247232232438724161)
  ·
    refine ⟨107897217185424174329043121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143862956247232232438724161 107897217185424174329043121)
    ·
      refine ⟨80922912889068130746782341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107897217185424174329043121 80922912889068130746782341)
      ·
        refine ⟨15173046166700274515021689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80922912889068130746782341 15173046166700274515021689)
        ·
          refine ⟨11379784625025205886266267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15173046166700274515021689 11379784625025205886266267)
          ·
            refine ⟨17069676937537808829399401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11379784625025205886266267 17069676937537808829399401)
            ·
              refine ⟨12802257703153356622049551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17069676937537808829399401 12802257703153356622049551)
              ·
                refine ⟨19203386554730034933074327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12802257703153356622049551 19203386554730034933074327)
                ·
                  refine ⟨28805079832095052399611491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19203386554730034933074327 28805079832095052399611491)
                  ·
                    refine ⟨43207619748142578599417237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28805079832095052399611491 43207619748142578599417237)
                    ·
                      refine ⟨2025357175694183371847683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43207619748142578599417237 2025357175694183371847683)
                      ·
                        rfl

theorem cell23_3944369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3944369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944369 prefixEnd_3944369 := by exact prefixLift 3944369
  have htrace : WordTrace (prefixWord ++ tailWord_3944369) baseStart_3944369 baseEnd_3944369 := by
    simpa [prefixWord, tailWord_3944369, baseEnd_3944369] using wordTrace_append hprefix tailTrace_3944369
  have hstable : (prefixWord ++ tailWord_3944369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944369).length < 2 ^ (prefixWord ++ tailWord_3944369).sum := by decide
  have hdescent : baseEnd_3944369 < baseStart_3944369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944373 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_3944373 : Nat := 118140960795 + 3944373 * 2 ^ 59
def prefixEnd_3944373 : Nat := 4983230072969 + 3 ^ 40 * 3944373 * 2
def baseEnd_3944373 : Nat := 2025359229616801356197665

theorem tailTrace_3944373 : CollatzResearch.WordTrace tailWord_3944373 prefixEnd_3944373 2025359229616801356197665 := by
  unfold tailWord_3944373
  simp only [CollatzResearch.WordTrace]
  refine ⟨143863102139217741121869773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95908734759478494081246515 143863102139217741121869773)
  ·
    refine ⟨53948663302206652920701165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143863102139217741121869773 53948663302206652920701165)
    ·
      refine ⟨20230748738327494845262937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53948663302206652920701165 20230748738327494845262937)
      ·
        refine ⟨15173061553745621133947203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20230748738327494845262937 15173061553745621133947203)
        ·
          refine ⟨22759592330618431700920805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15173061553745621133947203 22759592330618431700920805)
          ·
            refine ⟨4267423561990955943922651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22759592330618431700920805 4267423561990955943922651)
            ·
              refine ⟨6401135342986433915883977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267423561990955943922651 6401135342986433915883977)
              ·
                refine ⟨4800851507239825436912983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6401135342986433915883977 4800851507239825436912983)
                ·
                  refine ⟨7201277260859738155369475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800851507239825436912983 7201277260859738155369475)
                  ·
                    refine ⟨10801915891289607233054213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7201277260859738155369475 10801915891289607233054213)
                    ·
                      refine ⟨2025359229616801356197665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10801915891289607233054213 2025359229616801356197665)
                      ·
                        rfl

theorem cell23_3944373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_3944373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944373 prefixEnd_3944373 := by exact prefixLift 3944373
  have htrace : WordTrace (prefixWord ++ tailWord_3944373) baseStart_3944373 baseEnd_3944373 := by
    simpa [prefixWord, tailWord_3944373, baseEnd_3944373] using wordTrace_append hprefix tailTrace_3944373
  have hstable : (prefixWord ++ tailWord_3944373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944373).length < 2 ^ (prefixWord ++ tailWord_3944373).sum := by decide
  have hdescent : baseEnd_3944373 < baseStart_3944373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944413 : List Nat := [1, 4, 3, 1, 4, 1, 1, 8]
def baseStart_3944413 : Nat := 118140960795 + 3944413 * 2 ^ 59
def prefixEnd_3944413 : Nat := 4983230072969 + 3 ^ 40 * 3944413 * 2
def baseEnd_3944413 : Nat := 75014065512703007396203

theorem tailTrace_3944413 : CollatzResearch.WordTrace tailWord_3944413 prefixEnd_3944413 75014065512703007396203 := by
  unfold tailWord_3944413
  simp only [CollatzResearch.WordTrace]
  refine ⟨143864561059072827953325893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95909707372715218635550595 143864561059072827953325893)
  ·
    refine ⟨26974605198576155241248605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143864561059072827953325893 26974605198576155241248605)
    ·
      refine ⟨10115476949466058215468227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26974605198576155241248605 10115476949466058215468227)
      ·
        refine ⟨15173215424199087323202341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10115476949466058215468227 15173215424199087323202341)
        ·
          refine ⟨2844977892037328873100439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15173215424199087323202341 2844977892037328873100439)
          ·
            refine ⟨4267466838055993309650659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844977892037328873100439 4267466838055993309650659)
            ·
              refine ⟨6401200257083989964475989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267466838055993309650659 6401200257083989964475989)
              ·
                refine ⟨75014065512703007396203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6401200257083989964475989 75014065512703007396203)
                ·
                  rfl

theorem cell23_3944413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 8].length) (baseStart_3944413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944413 prefixEnd_3944413 := by exact prefixLift 3944413
  have htrace : WordTrace (prefixWord ++ tailWord_3944413) baseStart_3944413 baseEnd_3944413 := by
    simpa [prefixWord, tailWord_3944413, baseEnd_3944413] using wordTrace_append hprefix tailTrace_3944413
  have hstable : (prefixWord ++ tailWord_3944413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944413).length < 2 ^ (prefixWord ++ tailWord_3944413).sum := by decide
  have hdescent : baseEnd_3944413 < baseStart_3944413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944423 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3944423 : Nat := 118140960795 + 3944423 * 2 ^ 59
def prefixEnd_3944423 : Nat := 4983230072969 + 3 ^ 40 * 3944423 * 2
def baseEnd_3944423 : Nat := 2025384903649526160572435

theorem tailTrace_3944423 : CollatzResearch.WordTrace tailWord_3944423 prefixEnd_3944423 2025384903649526160572435 := by
  unfold tailWord_3944423
  simp only [CollatzResearch.WordTrace]
  refine ⟨143864925789036599661189923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95909950526024399774126615 143864925789036599661189923)
  ·
    refine ⟨215797388683554899491784885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143864925789036599661189923 215797388683554899491784885)
    ·
      refine ⟨20231005189083271827354833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215797388683554899491784885 20231005189083271827354833)
      ·
        refine ⟨15173253891812453870516125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20231005189083271827354833 15173253891812453870516125)
        ·
          refine ⟨5689970209429670201443547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15173253891812453870516125 5689970209429670201443547)
          ·
            refine ⟨8534955314144505302165321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689970209429670201443547 8534955314144505302165321)
            ·
              refine ⟨6401216485608378976623991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8534955314144505302165321 6401216485608378976623991)
              ·
                refine ⟨9601824728412568464935987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6401216485608378976623991 9601824728412568464935987)
                ·
                  refine ⟨14402737092618852697403981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9601824728412568464935987 14402737092618852697403981)
                  ·
                    refine ⟨5401026409732069761526493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14402737092618852697403981 5401026409732069761526493)
                    ·
                      refine ⟨2025384903649526160572435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5401026409732069761526493 2025384903649526160572435)
                      ·
                        rfl

theorem cell23_3944423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3944423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944423 prefixEnd_3944423 := by exact prefixLift 3944423
  have htrace : WordTrace (prefixWord ++ tailWord_3944423) baseStart_3944423 baseEnd_3944423 := by
    simpa [prefixWord, tailWord_3944423, baseEnd_3944423] using wordTrace_append hprefix tailTrace_3944423
  have hstable : (prefixWord ++ tailWord_3944423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944423).length < 2 ^ (prefixWord ++ tailWord_3944423).sum := by decide
  have hdescent : baseEnd_3944423 < baseStart_3944423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944449 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_3944449 : Nat := 118140960795 + 3944449 * 2 ^ 59
def prefixEnd_3944449 : Nat := 4983230072969 + 3 ^ 40 * 3944449 * 2
def baseEnd_3944449 : Nat := 2025398254146543058847315

theorem tailTrace_3944449 : CollatzResearch.WordTrace tailWord_3944449 prefixEnd_3944449 2025398254146543058847315 := by
  unfold tailWord_3944449
  simp only [CollatzResearch.WordTrace]
  refine ⟨143865874086942406101636401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95910582724628270734424267 143865874086942406101636401)
  ·
    refine ⟨107899405565206804576227301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143865874086942406101636401 107899405565206804576227301)
    ·
      refine ⟨20231138543476275858042619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107899405565206804576227301 20231138543476275858042619)
      ·
        refine ⟨30346707815214413787063929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20231138543476275858042619 30346707815214413787063929)
        ·
          refine ⟨22760030861410810340297947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30346707815214413787063929 22760030861410810340297947)
          ·
            refine ⟨34140046292116215510446921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22760030861410810340297947 34140046292116215510446921)
            ·
              refine ⟨25605034719087161632835191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34140046292116215510446921 25605034719087161632835191)
              ·
                refine ⟨38407552078630742449252787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25605034719087161632835191 38407552078630742449252787)
                ·
                  refine ⟨57611328117946113673879181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38407552078630742449252787 57611328117946113673879181)
                  ·
                    refine ⟨21604248044229792627704693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57611328117946113673879181 21604248044229792627704693)
                    ·
                      refine ⟨2025398254146543058847315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21604248044229792627704693 2025398254146543058847315)
                      ·
                        rfl

theorem cell23_3944449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_3944449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944449 prefixEnd_3944449 := by exact prefixLift 3944449
  have htrace : WordTrace (prefixWord ++ tailWord_3944449) baseStart_3944449 baseEnd_3944449 := by
    simpa [prefixWord, tailWord_3944449, baseEnd_3944449] using wordTrace_append hprefix tailTrace_3944449
  have hstable : (prefixWord ++ tailWord_3944449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944449).length < 2 ^ (prefixWord ++ tailWord_3944449).sum := by decide
  have hdescent : baseEnd_3944449 < baseStart_3944449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944459 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 4]
def baseStart_3944459 : Nat := 118140960795 + 3944459 * 2 ^ 59
def prefixEnd_3944459 : Nat := 4983230072969 + 3 ^ 40 * 3944459 * 2
def baseEnd_3944459 : Nat := 2025403388953088019722269

theorem tailTrace_3944459 : CollatzResearch.WordTrace tailWord_3944459 prefixEnd_3944459 2025403388953088019722269 := by
  unfold tailWord_3944459
  simp only [CollatzResearch.WordTrace]
  refine ⟨143866238816906177809500431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95910825877937451873000287 143866238816906177809500431)
  ·
    refine ⟨215799358225359266714250647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143866238816906177809500431 215799358225359266714250647)
    ·
      refine ⟨323699037338038900071375971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215799358225359266714250647 323699037338038900071375971)
      ·
        refine ⟨485548556007058350107063957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323699037338038900071375971 485548556007058350107063957)
        ·
          refine ⟨22760088562830860161268623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 485548556007058350107063957 22760088562830860161268623)
          ·
            refine ⟨34140132844246290241902935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22760088562830860161268623 34140132844246290241902935)
            ·
              refine ⟨51210199266369435362854403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34140132844246290241902935 51210199266369435362854403)
              ·
                refine ⟨76815298899554153044281605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51210199266369435362854403 76815298899554153044281605)
                ·
                  refine ⟨14402868543666403695802801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76815298899554153044281605 14402868543666403695802801)
                  ·
                    refine ⟨10802151407749802771852101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14402868543666403695802801 10802151407749802771852101)
                    ·
                      refine ⟨2025403388953088019722269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10802151407749802771852101 2025403388953088019722269)
                      ·
                        rfl

theorem cell23_3944459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 4].length) (baseStart_3944459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944459 prefixEnd_3944459 := by exact prefixLift 3944459
  have htrace : WordTrace (prefixWord ++ tailWord_3944459) baseStart_3944459 baseEnd_3944459 := by
    simpa [prefixWord, tailWord_3944459, baseEnd_3944459] using wordTrace_append hprefix tailTrace_3944459
  have hstable : (prefixWord ++ tailWord_3944459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944459).length < 2 ^ (prefixWord ++ tailWord_3944459).sum := by decide
  have hdescent : baseEnd_3944459 < baseStart_3944459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944476 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3944476 : Nat := 118140960795 + 3944476 * 2 ^ 59
def prefixEnd_3944476 : Nat := 4983230072969 + 3 ^ 40 * 3944476 * 2
def baseEnd_3944476 : Nat := 2025412118124214453209691

theorem tailTrace_3944476 : CollatzResearch.WordTrace tailWord_3944476 prefixEnd_3944476 2025412118124214453209691 := by
  unfold tailWord_3944476
  simp only [CollatzResearch.WordTrace]
  refine ⟨71933429428922294856434641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95911239238563059808579521 71933429428922294856434641)
  ·
    refine ⟨53950072071691721142325981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71933429428922294856434641 53950072071691721142325981)
    ·
      refine ⟨20231277026884395428372243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53950072071691721142325981 20231277026884395428372243)
      ·
        refine ⟨30346915540326593142558365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20231277026884395428372243 30346915540326593142558365)
        ·
          refine ⟨11380093327622472428459387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30346915540326593142558365 11380093327622472428459387)
          ·
            refine ⟨17070139991433708642689081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11380093327622472428459387 17070139991433708642689081)
            ·
              refine ⟨12802604993575281482016811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17070139991433708642689081 12802604993575281482016811)
              ·
                refine ⟨19203907490362922223025217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12802604993575281482016811 19203907490362922223025217)
                ·
                  refine ⟨14402930617772191667268913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19203907490362922223025217 14402930617772191667268913)
                  ·
                    refine ⟨10802197963329143750451685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14402930617772191667268913 10802197963329143750451685)
                    ·
                      refine ⟨2025412118124214453209691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10802197963329143750451685 2025412118124214453209691)
                      ·
                        rfl

theorem cell23_3944476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3944476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944476 prefixEnd_3944476 := by exact prefixLift 3944476
  have htrace : WordTrace (prefixWord ++ tailWord_3944476) baseStart_3944476 baseEnd_3944476 := by
    simpa [prefixWord, tailWord_3944476, baseEnd_3944476] using wordTrace_append hprefix tailTrace_3944476
  have hstable : (prefixWord ++ tailWord_3944476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944476).length < 2 ^ (prefixWord ++ tailWord_3944476).sum := by decide
  have hdescent : baseEnd_3944476 < baseStart_3944476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944499 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 1, 7]
def baseStart_3944499 : Nat := 118140960795 + 3944499 * 2 ^ 59
def prefixEnd_3944499 : Nat := 4983230072969 + 3 ^ 40 * 3944499 * 2
def baseEnd_3944499 : Nat := 675141309393089287740695

theorem tailTrace_3944499 : CollatzResearch.WordTrace tailWord_3944499 prefixEnd_3944499 675141309393089287740695 := by
  unfold tailWord_3944499
  simp only [CollatzResearch.WordTrace]
  refine ⟨143867697736761264640956551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95911798491174176427304367 143867697736761264640956551)
  ·
    refine ⟨215801546605141896961434827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143867697736761264640956551 215801546605141896961434827)
    ·
      refine ⟨323702319907712845442152241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215801546605141896961434827 323702319907712845442152241)
      ·
        refine ⟨242776739930784634081614181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323702319907712845442152241 242776739930784634081614181)
        ·
          refine ⟨45520638737022118890302659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242776739930784634081614181 45520638737022118890302659)
          ·
            refine ⟨68280958105533178335453989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45520638737022118890302659 68280958105533178335453989)
            ·
              refine ⟨12802679644787470937897623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68280958105533178335453989 12802679644787470937897623)
              ·
                refine ⟨19204019467181206406846435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12802679644787470937897623 19204019467181206406846435)
                ·
                  refine ⟨28806029200771809610269653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19204019467181206406846435 28806029200771809610269653)
                  ·
                    refine ⟨675141309393089287740695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28806029200771809610269653 675141309393089287740695)
                    ·
                      rfl

theorem cell23_3944499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 7].length) (baseStart_3944499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944499 prefixEnd_3944499 := by exact prefixLift 3944499
  have htrace : WordTrace (prefixWord ++ tailWord_3944499) baseStart_3944499 baseEnd_3944499 := by
    simpa [prefixWord, tailWord_3944499, baseEnd_3944499] using wordTrace_append hprefix tailTrace_3944499
  have hstable : (prefixWord ++ tailWord_3944499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944499).length < 2 ^ (prefixWord ++ tailWord_3944499).sum := by decide
  have hdescent : baseEnd_3944499 < baseStart_3944499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944506 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2]
def baseStart_3944506 : Nat := 118140960795 + 3944506 * 2 ^ 59
def prefixEnd_3944506 : Nat := 4983230072969 + 3 ^ 40 * 3944506 * 2
def baseEnd_3944506 : Nat := 2025427522543849335834553

theorem tailTrace_3944506 : CollatzResearch.WordTrace tailWord_3944506 prefixEnd_3944506 2025427522543849335834553 := by
  unfold tailWord_3944506
  simp only [CollatzResearch.WordTrace]
  refine ⟨35966988261933976209115343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95911968698490603224307581 35966988261933976209115343)
  ·
    refine ⟨53950482392900964313673015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35966988261933976209115343 53950482392900964313673015)
    ·
      refine ⟨80925723589351446470509523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53950482392900964313673015 80925723589351446470509523)
      ·
        refine ⟨121388585384027169705764285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80925723589351446470509523 121388585384027169705764285)
        ·
          refine ⟨45520719519010188639661607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121388585384027169705764285 45520719519010188639661607)
          ·
            refine ⟨68281079278515282959492411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45520719519010188639661607 68281079278515282959492411)
            ·
              refine ⟨102421618917772924439238617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68281079278515282959492411 102421618917772924439238617)
              ·
                refine ⟨76816214188329693329428963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102421618917772924439238617 76816214188329693329428963)
                ·
                  refine ⟨115224321282494539994143445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76816214188329693329428963 115224321282494539994143445)
                  ·
                    refine ⟨2700570030058465781112737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 115224321282494539994143445 2700570030058465781112737)
                    ·
                      refine ⟨2025427522543849335834553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700570030058465781112737 2025427522543849335834553)
                      ·
                        rfl

theorem cell23_3944506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_3944506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944506 prefixEnd_3944506 := by exact prefixLift 3944506
  have htrace : WordTrace (prefixWord ++ tailWord_3944506) baseStart_3944506 baseEnd_3944506 := by
    simpa [prefixWord, tailWord_3944506, baseEnd_3944506] using wordTrace_append hprefix tailTrace_3944506
  have hstable : (prefixWord ++ tailWord_3944506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944506).length < 2 ^ (prefixWord ++ tailWord_3944506).sum := by decide
  have hdescent : baseEnd_3944506 < baseStart_3944506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944526 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_3944526 : Nat := 118140960795 + 3944526 * 2 ^ 59
def prefixEnd_3944526 : Nat := 4983230072969 + 3 ^ 40 * 3944526 * 2
def baseEnd_3944526 : Nat := 2025437792156939257584461

theorem tailTrace_3944526 : CollatzResearch.WordTrace tailWord_3944526 prefixEnd_3944526 2025437792156939257584461 := by
  unfold tailWord_3944526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983585313457931031523679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95912455005108965501459621 17983585313457931031523679)
  ·
    refine ⟨26975377970186896547285519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17983585313457931031523679 26975377970186896547285519)
    ·
      refine ⟨40463066955280344820928279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26975377970186896547285519 40463066955280344820928279)
      ·
        refine ⟨60694600432920517231392419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40463066955280344820928279 60694600432920517231392419)
        ·
          refine ⟨91041900649380775847088629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60694600432920517231392419 91041900649380775847088629)
          ·
            refine ⟨8535178185879447735664559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91041900649380775847088629 8535178185879447735664559)
            ·
              refine ⟨12802767278819171603496839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8535178185879447735664559 12802767278819171603496839)
              ·
                refine ⟨19204150918228757405245259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12802767278819171603496839 19204150918228757405245259)
                ·
                  refine ⟨28806226377343136107867889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19204150918228757405245259 28806226377343136107867889)
                  ·
                    refine ⟨21604669783007352080900917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28806226377343136107867889 21604669783007352080900917)
                    ·
                      refine ⟨2025437792156939257584461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21604669783007352080900917 2025437792156939257584461)
                      ·
                        rfl

theorem cell23_3944526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_3944526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944526 prefixEnd_3944526 := by exact prefixLift 3944526
  have htrace : WordTrace (prefixWord ++ tailWord_3944526) baseStart_3944526 baseEnd_3944526 := by
    simpa [prefixWord, tailWord_3944526, baseEnd_3944526] using wordTrace_append hprefix tailTrace_3944526
  have hstable : (prefixWord ++ tailWord_3944526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944526).length < 2 ^ (prefixWord ++ tailWord_3944526).sum := by decide
  have hdescent : baseEnd_3944526 < baseStart_3944526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944573 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_3944573 : Nat := 118140960795 + 3944573 * 2 ^ 59
def prefixEnd_3944573 : Nat := 4983230072969 + 3 ^ 40 * 3944573 * 2
def baseEnd_3944573 : Nat := 2025461925747700573696745

theorem tailTrace_3944573 : CollatzResearch.WordTrace tailWord_3944573 prefixEnd_3944573 2025461925747700573696745 := by
  unfold tailWord_3944573
  simp only [CollatzResearch.WordTrace]
  refine ⟨143870396738493175279150373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95913597825662116852766915 143870396738493175279150373)
  ·
    refine ⟨26975699388467470364840695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143870396738493175279150373 26975699388467470364840695)
    ·
      refine ⟨40463549082701205547261043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26975699388467470364840695 40463549082701205547261043)
      ·
        refine ⟨60695323624051808320891565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40463549082701205547261043 60695323624051808320891565)
        ·
          refine ⟨22760746359019428120334337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60695323624051808320891565 22760746359019428120334337)
          ·
            refine ⟨17070559769264571090250753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22760746359019428120334337 17070559769264571090250753)
            ·
              refine ⟨12802919826948428317688065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17070559769264571090250753 12802919826948428317688065)
              ·
                refine ⟨9602189870211321238266049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12802919826948428317688065 9602189870211321238266049)
                ·
                  refine ⟨7201642402658490928699537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9602189870211321238266049 7201642402658490928699537)
                  ·
                    refine ⟨5401231801993868196524653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7201642402658490928699537 5401231801993868196524653)
                    ·
                      refine ⟨2025461925747700573696745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5401231801993868196524653 2025461925747700573696745)
                      ·
                        rfl

theorem cell23_3944573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_3944573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944573 prefixEnd_3944573 := by exact prefixLift 3944573
  have htrace : WordTrace (prefixWord ++ tailWord_3944573) baseStart_3944573 baseEnd_3944573 := by
    simpa [prefixWord, tailWord_3944573, baseEnd_3944573] using wordTrace_append hprefix tailTrace_3944573
  have hstable : (prefixWord ++ tailWord_3944573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944573).length < 2 ^ (prefixWord ++ tailWord_3944573).sum := by decide
  have hdescent : baseEnd_3944573 < baseStart_3944573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944580 : List Nat := [2, 3, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_3944580 : Nat := 118140960795 + 3944580 * 2 ^ 59
def prefixEnd_3944580 : Nat := 4983230072969 + 3 ^ 40 * 3944580 * 2
def baseEnd_3944580 : Nat := 675155173370760682103071

theorem tailTrace_3944580 : CollatzResearch.WordTrace tailWord_3944580 prefixEnd_3944580 675155173370760682103071 := by
  unfold tailWord_3944580
  simp only [CollatzResearch.WordTrace]
  refine ⟨71935326024733907737327597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95913768032978543649770129 71935326024733907737327597)
  ·
    refine ⟨26975747259275215401497849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71935326024733907737327597 26975747259275215401497849)
    ·
      refine ⟨20231810444456411551123387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26975747259275215401497849 20231810444456411551123387)
      ·
        refine ⟨30347715666684617326685081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20231810444456411551123387 30347715666684617326685081)
        ·
          refine ⟨22760786750013462995013811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30347715666684617326685081 22760786750013462995013811)
          ·
            refine ⟨34141180125020194492520717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22760786750013462995013811 34141180125020194492520717)
            ·
              refine ⟨12802942546882572934695269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34141180125020194492520717 12802942546882572934695269)
              ·
                refine ⟨2400551727540482425255363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12802942546882572934695269 2400551727540482425255363)
                ·
                  refine ⟨3600827591310723637883045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400551727540482425255363 3600827591310723637883045)
                  ·
                    refine ⟨675155173370760682103071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3600827591310723637883045 675155173370760682103071)
                    ·
                      rfl

theorem cell23_3944580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_3944580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944580 prefixEnd_3944580 := by exact prefixLift 3944580
  have htrace : WordTrace (prefixWord ++ tailWord_3944580) baseStart_3944580 baseEnd_3944580 := by
    simpa [prefixWord, tailWord_3944580, baseEnd_3944580] using wordTrace_append hprefix tailTrace_3944580
  have hstable : (prefixWord ++ tailWord_3944580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944580).length < 2 ^ (prefixWord ++ tailWord_3944580).sum := by decide
  have hdescent : baseEnd_3944580 < baseStart_3944580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944613 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 1, 5, 2]
def baseStart_3944613 : Nat := 118140960795 + 3944613 * 2 ^ 59
def prefixEnd_3944613 : Nat := 4983230072969 + 3 ^ 40 * 3944613 * 2
def baseEnd_3944613 : Nat := 2025482464973880417196561

theorem tailTrace_3944613 : CollatzResearch.WordTrace tailWord_3944613 prefixEnd_3944613 2025482464973880417196561 := by
  unfold tailWord_3944613
  simp only [CollatzResearch.WordTrace]
  refine ⟨143871855658348262110606493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95914570438898841407070995 143871855658348262110606493)
  ·
    refine ⟨53951945871880598291477435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143871855658348262110606493 53951945871880598291477435)
    ·
      refine ⟨80927918807820897437216153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53951945871880598291477435 80927918807820897437216153)
      ·
        refine ⟨60695939105865673077912115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80927918807820897437216153 60695939105865673077912115)
        ·
          refine ⟨91043908658798509616868173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60695939105865673077912115 91043908658798509616868173)
          ·
            refine ⟨34141465747049441106325565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91043908658798509616868173 34141465747049441106325565)
            ·
              refine ⟨12803049655143540414872087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34141465747049441106325565 12803049655143540414872087)
              ·
                refine ⟨19204574482715310622308131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12803049655143540414872087 19204574482715310622308131)
                ·
                  refine ⟨28806861724072965933462197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19204574482715310622308131 28806861724072965933462197)
                  ·
                    refine ⟨2700643286631840556262081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28806861724072965933462197 2700643286631840556262081)
                    ·
                      refine ⟨2025482464973880417196561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700643286631840556262081 2025482464973880417196561)
                      ·
                        rfl

theorem cell23_3944613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_3944613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944613 prefixEnd_3944613 := by exact prefixLift 3944613
  have htrace : WordTrace (prefixWord ++ tailWord_3944613) baseStart_3944613 baseEnd_3944613 := by
    simpa [prefixWord, tailWord_3944613, baseEnd_3944613] using wordTrace_append hprefix tailTrace_3944613
  have hstable : (prefixWord ++ tailWord_3944613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944613).length < 2 ^ (prefixWord ++ tailWord_3944613).sum := by decide
  have hdescent : baseEnd_3944613 < baseStart_3944613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944619 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 4, 10]
def baseStart_3944619 : Nat := 118140960795 + 3944619 * 2 ^ 59
def prefixEnd_3944619 : Nat := 4983230072969 + 3 ^ 40 * 3944619 * 2
def baseEnd_3944619 : Nat := 675161848619269131240511

theorem tailTrace_3944619 : CollatzResearch.WordTrace tailWord_3944619 prefixEnd_3944619 675161848619269131240511 := by
  unfold tailWord_3944619
  simp only [CollatzResearch.WordTrace]
  refine ⟨143872074496326525135324911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95914716330884350090216607 143872074496326525135324911)
  ·
    refine ⟨215808111744489787702987367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143872074496326525135324911 215808111744489787702987367)
    ·
      refine ⟨323712167616734681554481051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215808111744489787702987367 323712167616734681554481051)
      ·
        refine ⟨485568251425102022331721577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323712167616734681554481051 485568251425102022331721577)
        ·
          refine ⟨364176188568826516748791183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485568251425102022331721577 364176188568826516748791183)
          ·
            refine ⟨546264282853239775123186775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364176188568826516748791183 546264282853239775123186775)
            ·
              refine ⟨819396424279859662684780163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546264282853239775123186775 819396424279859662684780163)
              ·
                refine ⟨1229094636419789494027170245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819396424279859662684780163 1229094636419789494027170245)
                ·
                  refine ⟨230455244328710530130094421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229094636419789494027170245 230455244328710530130094421)
                  ·
                    refine ⟨675161848619269131240511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 230455244328710530130094421 675161848619269131240511)
                    ·
                      rfl

theorem cell23_3944619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 10].length) (baseStart_3944619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944619 prefixEnd_3944619 := by exact prefixLift 3944619
  have htrace : WordTrace (prefixWord ++ tailWord_3944619) baseStart_3944619 baseEnd_3944619 := by
    simpa [prefixWord, tailWord_3944619, baseEnd_3944619] using wordTrace_append hprefix tailTrace_3944619
  have hstable : (prefixWord ++ tailWord_3944619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944619).length < 2 ^ (prefixWord ++ tailWord_3944619).sum := by decide
  have hdescent : baseEnd_3944619 < baseStart_3944619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944680 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3944680 : Nat := 118140960795 + 3944680 * 2 ^ 59
def prefixEnd_3944680 : Nat := 4983230072969 + 3 ^ 40 * 3944680 * 2
def baseEnd_3944680 : Nat := 2025516868177731655058753

theorem tailTrace_3944680 : CollatzResearch.WordTrace tailWord_3944680 prefixEnd_3944680 2025516868177731655058753 := by
  unfold tailWord_3944680
  simp only [CollatzResearch.WordTrace]
  refine ⟨71937149674552766276647747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95916199566070355035530329 71937149674552766276647747)
  ·
    refine ⟨107905724511829149414971621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71937149674552766276647747 107905724511829149414971621)
    ·
      refine ⟨20232323345967965515307179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107905724511829149414971621 20232323345967965515307179)
      ·
        refine ⟨30348485018951948272960769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20232323345967965515307179 30348485018951948272960769)
        ·
          refine ⟨22761363764213961204720577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30348485018951948272960769 22761363764213961204720577)
          ·
            refine ⟨17071022823160470903540433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22761363764213961204720577 17071022823160470903540433)
            ·
              refine ⟨12803267117370353177655325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17071022823160470903540433 12803267117370353177655325)
              ·
                refine ⟨4801225169013882441620747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12803267117370353177655325 4801225169013882441620747)
                ·
                  refine ⟨7201837753520823662431121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801225169013882441620747 7201837753520823662431121)
                  ·
                    refine ⟨5401378315140617746823341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7201837753520823662431121 5401378315140617746823341)
                    ·
                      refine ⟨2025516868177731655058753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5401378315140617746823341 2025516868177731655058753)
                      ·
                        rfl

theorem cell23_3944680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3944680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944680 prefixEnd_3944680 := by exact prefixLift 3944680
  have htrace : WordTrace (prefixWord ++ tailWord_3944680) baseStart_3944680 baseEnd_3944680 := by
    simpa [prefixWord, tailWord_3944680, baseEnd_3944680] using wordTrace_append hprefix tailTrace_3944680
  have hstable : (prefixWord ++ tailWord_3944680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944680).length < 2 ^ (prefixWord ++ tailWord_3944680).sum := by decide
  have hdescent : baseEnd_3944680 < baseStart_3944680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944694 : List Nat := [5, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_3944694 : Nat := 118140960795 + 3944694 * 2 ^ 59
def prefixEnd_3944694 : Nat := 4983230072969 + 3 ^ 40 * 3944694 * 2
def baseEnd_3944694 : Nat := 2025524056906894600283689

theorem tailTrace_3944694 : CollatzResearch.WordTrace tailWord_3944694 prefixEnd_3944694 2025524056906894600283689 := by
  unfold tailWord_3944694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8992175623190925809019071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95916539980703208629536757 8992175623190925809019071)
  ·
    refine ⟨13488263434786388713528607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8992175623190925809019071 13488263434786388713528607)
    ·
      refine ⟨20232395152179583070292911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13488263434786388713528607 20232395152179583070292911)
      ·
        refine ⟨30348592728269374605439367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20232395152179583070292911 30348592728269374605439367)
        ·
          refine ⟨45522889092404061908159051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30348592728269374605439367 45522889092404061908159051)
          ·
            refine ⟨68284333638606092862238577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45522889092404061908159051 68284333638606092862238577)
            ·
              refine ⟨51213250228954569646678933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68284333638606092862238577 51213250228954569646678933)
              ·
                refine ⟨2400621104482245452188075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51213250228954569646678933 2400621104482245452188075)
                ·
                  refine ⟨3600931656723368178282113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400621104482245452188075 3600931656723368178282113)
                  ·
                    refine ⟨2700698742542526133711585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3600931656723368178282113 2700698742542526133711585)
                    ·
                      refine ⟨2025524056906894600283689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700698742542526133711585 2025524056906894600283689)
                      ·
                        rfl

theorem cell23_3944694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_3944694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944694 prefixEnd_3944694 := by exact prefixLift 3944694
  have htrace : WordTrace (prefixWord ++ tailWord_3944694) baseStart_3944694 baseEnd_3944694 := by
    simpa [prefixWord, tailWord_3944694, baseEnd_3944694] using wordTrace_append hprefix tailTrace_3944694
  have hstable : (prefixWord ++ tailWord_3944694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944694).length < 2 ^ (prefixWord ++ tailWord_3944694).sum := by decide
  have hdescent : baseEnd_3944694 < baseStart_3944694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944744 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3944744 : Nat := 118140960795 + 3944744 * 2 ^ 59
def prefixEnd_3944744 : Nat := 4983230072969 + 3 ^ 40 * 3944744 * 2
def baseEnd_3944744 : Nat := 2025549730939619404658459

theorem tailTrace_3944744 : CollatzResearch.WordTrace tailWord_3944744 prefixEnd_3944744 2025549730939619404658459 := by
  unfold tailWord_3944744
  simp only [CollatzResearch.WordTrace]
  refine ⟨71938316810436835741812643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95917755747249114322416857 71938316810436835741812643)
  ·
    refine ⟨107907475215655253612718965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71938316810436835741812643 107907475215655253612718965)
    ·
      refine ⟨10116325801467680026192403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107907475215655253612718965 10116325801467680026192403)
      ·
        refine ⟨15174488702201520039288605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10116325801467680026192403 15174488702201520039288605)
        ·
          refine ⟨5690433263325570014733227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15174488702201520039288605 5690433263325570014733227)
          ·
            refine ⟨8535649894988355022099841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5690433263325570014733227 8535649894988355022099841)
            ·
              refine ⟨6401737421241266266574881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8535649894988355022099841 6401737421241266266574881)
              ·
                refine ⟨4801303065930949699931161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6401737421241266266574881 4801303065930949699931161)
                ·
                  refine ⟨3600977299448212274948371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4801303065930949699931161 3600977299448212274948371)
                  ·
                    refine ⟨5401465949172318412422557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3600977299448212274948371 5401465949172318412422557)
                    ·
                      refine ⟨2025549730939619404658459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5401465949172318412422557 2025549730939619404658459)
                      ·
                        rfl

theorem cell23_3944744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3944744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944744 prefixEnd_3944744 := by exact prefixLift 3944744
  have htrace : WordTrace (prefixWord ++ tailWord_3944744) baseStart_3944744 baseEnd_3944744 := by
    simpa [prefixWord, tailWord_3944744, baseEnd_3944744] using wordTrace_append hprefix tailTrace_3944744
  have hstable : (prefixWord ++ tailWord_3944744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944744).length < 2 ^ (prefixWord ++ tailWord_3944744).sum := by decide
  have hdescent : baseEnd_3944744 < baseStart_3944744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944767 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 2, 2, 2]
def baseStart_3944767 : Nat := 118140960795 + 3944767 * 2 ^ 59
def prefixEnd_3944767 : Nat := 4983230072969 + 3 ^ 40 * 3944767 * 2
def baseEnd_3944767 : Nat := 2025561540994672814670853

theorem tailTrace_3944767 : CollatzResearch.WordTrace tailWord_3944767 prefixEnd_3944767 2025561540994672814670853 := by
  unfold tailWord_3944767
  simp only [CollatzResearch.WordTrace]
  refine ⟨143877472499790346411712555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95918314999860230941141703 143877472499790346411712555)
  ·
    refine ⟨215816208749685519617568833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143877472499790346411712555 215816208749685519617568833)
    ·
      refine ⟨161862156562264139713176625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215816208749685519617568833 161862156562264139713176625)
      ·
        refine ⟨121396617421698104784882469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161862156562264139713176625 121396617421698104784882469)
        ·
          refine ⟨22761865766568394647165463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121396617421698104784882469 22761865766568394647165463)
          ·
            refine ⟨34142798649852591970748195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22761865766568394647165463 34142798649852591970748195)
            ·
              refine ⟨51214197974778887956122293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34142798649852591970748195 51214197974778887956122293)
              ·
                refine ⟨4801331060135520745886465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51214197974778887956122293 4801331060135520745886465)
                ·
                  refine ⟨3600998295101640559414849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4801331060135520745886465 3600998295101640559414849)
                  ·
                    refine ⟨2700748721326230419561137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3600998295101640559414849 2700748721326230419561137)
                    ·
                      refine ⟨2025561540994672814670853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700748721326230419561137 2025561540994672814670853)
                      ·
                        rfl

theorem cell23_3944767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_3944767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944767 prefixEnd_3944767 := by exact prefixLift 3944767
  have htrace : WordTrace (prefixWord ++ tailWord_3944767) baseStart_3944767 baseEnd_3944767 := by
    simpa [prefixWord, tailWord_3944767, baseEnd_3944767] using wordTrace_append hprefix tailTrace_3944767
  have hstable : (prefixWord ++ tailWord_3944767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944767).length < 2 ^ (prefixWord ++ tailWord_3944767).sum := by decide
  have hdescent : baseEnd_3944767 < baseStart_3944767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944803 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 4, 5]
def baseStart_3944803 : Nat := 118140960795 + 3944803 * 2 ^ 59
def prefixEnd_3944803 : Nat := 4983230072969 + 3 ^ 40 * 3944803 * 2
def baseEnd_3944803 : Nat := 675193342099411557940229

theorem tailTrace_3944803 : CollatzResearch.WordTrace tailWord_3944803 prefixEnd_3944803 675193342099411557940229 := by
  unfold tailWord_3944803
  simp only [CollatzResearch.WordTrace]
  refine ⟨143878785527659924560023063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95919190351773283040015375 143878785527659924560023063)
  ·
    refine ⟨215818178291489886840034595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143878785527659924560023063 215818178291489886840034595)
    ·
      refine ⟨323727267437234830260051893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215818178291489886840034595 323727267437234830260051893)
      ·
        refine ⟨30349431322240765336879865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323727267437234830260051893 30349431322240765336879865)
        ·
          refine ⟨22762073491680574002659899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30349431322240765336879865 22762073491680574002659899)
          ·
            refine ⟨34143110237520861003989849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22762073491680574002659899 34143110237520861003989849)
            ·
              refine ⟨25607332678140645752992387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34143110237520861003989849 25607332678140645752992387)
              ·
                refine ⟨38410999017210968629488581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25607332678140645752992387 38410999017210968629488581)
                ·
                  refine ⟨7202062315727056618029109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38410999017210968629488581 7202062315727056618029109)
                  ·
                    refine ⟨675193342099411557940229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7202062315727056618029109 675193342099411557940229)
                    ·
                      rfl

theorem cell23_3944803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 5].length) (baseStart_3944803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944803 prefixEnd_3944803 := by exact prefixLift 3944803
  have htrace : WordTrace (prefixWord ++ tailWord_3944803) baseStart_3944803 baseEnd_3944803 := by
    simpa [prefixWord, tailWord_3944803, baseEnd_3944803] using wordTrace_append hprefix tailTrace_3944803
  have hstable : (prefixWord ++ tailWord_3944803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944803).length < 2 ^ (prefixWord ++ tailWord_3944803).sum := by decide
  have hdescent : baseEnd_3944803 < baseStart_3944803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944813 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3944813 : Nat := 118140960795 + 3944813 * 2 ^ 59
def prefixEnd_3944813 : Nat := 4983230072969 + 3 ^ 40 * 3944813 * 2
def baseEnd_3944813 : Nat := 2025585161104779634695641

theorem tailTrace_3944813 : CollatzResearch.WordTrace tailWord_3944813 prefixEnd_3944813 2025585161104779634695641 := by
  unfold tailWord_3944813
  simp only [CollatzResearch.WordTrace]
  refine ⟨143879150257623696267887093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95919433505082464178591395 143879150257623696267887093)
  ·
    refine ⟨13488670336652221525114415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143879150257623696267887093 13488670336652221525114415)
    ·
      refine ⟨20233005504978332287671623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13488670336652221525114415 20233005504978332287671623)
      ·
        refine ⟨30349508257467498431507435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20233005504978332287671623 30349508257467498431507435)
        ·
          refine ⟨45524262386201247647261153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30349508257467498431507435 45524262386201247647261153)
          ·
            refine ⟨34143196789650935735445865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45524262386201247647261153 34143196789650935735445865)
            ·
              refine ⟨25607397592238201801584399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34143196789650935735445865 25607397592238201801584399)
              ·
                refine ⟨38411096388357302702376599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25607397592238201801584399 38411096388357302702376599)
                ·
                  refine ⟨57616644582535954053564899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38411096388357302702376599 57616644582535954053564899)
                  ·
                    refine ⟨86424966873803931080347349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57616644582535954053564899 86424966873803931080347349)
                    ·
                      refine ⟨2025585161104779634695641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86424966873803931080347349 2025585161104779634695641)
                      ·
                        rfl

theorem cell23_3944813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3944813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944813 prefixEnd_3944813 := by exact prefixLift 3944813
  have htrace : WordTrace (prefixWord ++ tailWord_3944813) baseStart_3944813 baseEnd_3944813 := by
    simpa [prefixWord, tailWord_3944813, baseEnd_3944813] using wordTrace_append hprefix tailTrace_3944813
  have hstable : (prefixWord ++ tailWord_3944813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944813).length < 2 ^ (prefixWord ++ tailWord_3944813).sum := by decide
  have hdescent : baseEnd_3944813 < baseStart_3944813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944823 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_3944823 : Nat := 118140960795 + 3944823 * 2 ^ 59
def prefixEnd_3944823 : Nat := 4983230072969 + 3 ^ 40 * 3944823 * 2
def baseEnd_3944823 : Nat := 2025590295911324595570595

theorem tailTrace_3944823 : CollatzResearch.WordTrace tailWord_3944823 prefixEnd_3944823 2025590295911324595570595 := by
  unfold tailWord_3944823
  simp only [CollatzResearch.WordTrace]
  refine ⟨143879514987587467975751123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95919676658391645317167415 143879514987587467975751123)
  ·
    refine ⟨215819272481381201963626685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143879514987587467975751123 215819272481381201963626685)
    ·
      refine ⟨80932227180517950736360007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215819272481381201963626685 80932227180517950736360007)
      ·
        refine ⟨121398340770776926104540011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80932227180517950736360007 121398340770776926104540011)
        ·
          refine ⟨182097511156165389156810017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121398340770776926104540011 182097511156165389156810017)
          ·
            refine ⟨136573133367124041867607513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182097511156165389156810017 136573133367124041867607513)
            ·
              refine ⟨102429850025343031400705635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136573133367124041867607513 102429850025343031400705635)
              ·
                refine ⟨153644775038014547101058453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102429850025343031400705635 153644775038014547101058453)
                ·
                  refine ⟨7202098829906931895362115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153644775038014547101058453 7202098829906931895362115)
                  ·
                    refine ⟨10803148244860397843043173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7202098829906931895362115 10803148244860397843043173)
                    ·
                      refine ⟨2025590295911324595570595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10803148244860397843043173 2025590295911324595570595)
                      ·
                        rfl

theorem cell23_3944823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_3944823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944823 prefixEnd_3944823 := by exact prefixLift 3944823
  have htrace : WordTrace (prefixWord ++ tailWord_3944823) baseStart_3944823 baseEnd_3944823 := by
    simpa [prefixWord, tailWord_3944823, baseEnd_3944823] using wordTrace_append hprefix tailTrace_3944823
  have hstable : (prefixWord ++ tailWord_3944823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944823).length < 2 ^ (prefixWord ++ tailWord_3944823).sum := by decide
  have hdescent : baseEnd_3944823 < baseStart_3944823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944840 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3944840 : Nat := 118140960795 + 3944840 * 2 ^ 59
def prefixEnd_3944840 : Nat := 4983230072969 + 3 ^ 40 * 3944840 * 2
def baseEnd_3944840 : Nat := 2025599025082451029058017

theorem tailTrace_3944840 : CollatzResearch.WordTrace tailWord_3944840 prefixEnd_3944840 2025599025082451029058017 := by
  unfold tailWord_3944840
  simp only [CollatzResearch.WordTrace]
  refine ⟨71940067514262939939559987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95920090019017253252746649 71940067514262939939559987)
  ·
    refine ⟨107910101271394409909339981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71940067514262939939559987 107910101271394409909339981)
    ·
      refine ⟨40466287976772903716002493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107910101271394409909339981 40466287976772903716002493)
      ·
        refine ⟨15174857991289838893500935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40466287976772903716002493 15174857991289838893500935)
        ·
          refine ⟨22762286986934758340251403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15174857991289838893500935 22762286986934758340251403)
          ·
            refine ⟨34143430480402137510377105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22762286986934758340251403 34143430480402137510377105)
            ·
              refine ⟨25607572860301603132782829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34143430480402137510377105 25607572860301603132782829)
              ·
                refine ⟨9602839822613101174793561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25607572860301603132782829 9602839822613101174793561)
                ·
                  refine ⟨7202129866959825881095171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9602839822613101174793561 7202129866959825881095171)
                  ·
                    refine ⟨10803194800439738821642757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7202129866959825881095171 10803194800439738821642757)
                    ·
                      refine ⟨2025599025082451029058017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10803194800439738821642757 2025599025082451029058017)
                      ·
                        rfl

theorem cell23_3944840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3944840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944840 prefixEnd_3944840 := by exact prefixLift 3944840
  have htrace : WordTrace (prefixWord ++ tailWord_3944840) baseStart_3944840 baseEnd_3944840 := by
    simpa [prefixWord, tailWord_3944840, baseEnd_3944840] using wordTrace_append hprefix tailTrace_3944840
  have hstable : (prefixWord ++ tailWord_3944840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944840).length < 2 ^ (prefixWord ++ tailWord_3944840).sum := by decide
  have hdescent : baseEnd_3944840 < baseStart_3944840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944863 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 8]
def baseStart_3944863 : Nat := 118140960795 + 3944863 * 2 ^ 59
def prefixEnd_3944863 : Nat := 4983230072969 + 3 ^ 40 * 3944863 * 2
def baseEnd_3944863 : Nat := 225067870570833826563379

theorem tailTrace_3944863 : CollatzResearch.WordTrace tailWord_3944863 prefixEnd_3944863 225067870570833826563379 := by
  unfold tailWord_3944863
  simp only [CollatzResearch.WordTrace]
  refine ⟨143880973907442554807207243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95920649271628369871471495 143880973907442554807207243)
  ·
    refine ⟨215821460861163832210810865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143880973907442554807207243 215821460861163832210810865)
    ·
      refine ⟨161866095645872874158108149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215821460861163832210810865 161866095645872874158108149)
      ·
        refine ⟨15174946466800581952322639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161866095645872874158108149 15174946466800581952322639)
        ·
          refine ⟨22762419700200872928483959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15174946466800581952322639 22762419700200872928483959)
          ·
            refine ⟨34143629550301309392725939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22762419700200872928483959 34143629550301309392725939)
            ·
              refine ⟨51215444325451964089088909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34143629550301309392725939 51215444325451964089088909)
              ·
                refine ⟨19205791622044486533408341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51215444325451964089088909 19205791622044486533408341)
                ·
                  refine ⟨225067870570833826563379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19205791622044486533408341 225067870570833826563379)
                  ·
                    rfl

theorem cell23_3944863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 8].length) (baseStart_3944863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944863 prefixEnd_3944863 := by exact prefixLift 3944863
  have htrace : WordTrace (prefixWord ++ tailWord_3944863) baseStart_3944863 baseEnd_3944863 := by
    simpa [prefixWord, tailWord_3944863, baseEnd_3944863] using wordTrace_append hprefix tailTrace_3944863
  have hstable : (prefixWord ++ tailWord_3944863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944863).length < 2 ^ (prefixWord ++ tailWord_3944863).sum := by decide
  have hdescent : baseEnd_3944863 < baseStart_3944863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944867 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 3, 4]
def baseStart_3944867 : Nat := 118140960795 + 3944867 * 2 ^ 59
def prefixEnd_3944867 : Nat := 4983230072969 + 3 ^ 40 * 3944867 * 2
def baseEnd_3944867 : Nat := 675204296353374141140131

theorem tailTrace_3944867 : CollatzResearch.WordTrace tailWord_3944867 prefixEnd_3944867 675204296353374141140131 := by
  unfold tailWord_3944867
  simp only [CollatzResearch.WordTrace]
  refine ⟨143881119799428063490352855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95920746532952042326901903 143881119799428063490352855)
  ·
    refine ⟨215821679699142095235529283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143881119799428063490352855 215821679699142095235529283)
    ·
      refine ⟨323732519548713142853293925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215821679699142095235529283 323732519548713142853293925)
      ·
        refine ⟨60699847415383714284992611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323732519548713142853293925 60699847415383714284992611)
        ·
          refine ⟨91049771123075571427488917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60699847415383714284992611 91049771123075571427488917)
          ·
            refine ⟨4267958021394167410663543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91049771123075571427488917 4267958021394167410663543)
            ·
              refine ⟨6401937032091251115995315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267958021394167410663543 6401937032091251115995315)
              ·
                refine ⟨9602905548136876673992973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6401937032091251115995315 9602905548136876673992973)
                ·
                  refine ⟨3601089580551328752747365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9602905548136876673992973 3601089580551328752747365)
                  ·
                    refine ⟨675204296353374141140131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3601089580551328752747365 675204296353374141140131)
                    ·
                      rfl

theorem cell23_3944867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 4].length) (baseStart_3944867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944867 prefixEnd_3944867 := by exact prefixLift 3944867
  have htrace : WordTrace (prefixWord ++ tailWord_3944867) baseStart_3944867 baseEnd_3944867 := by
    simpa [prefixWord, tailWord_3944867, baseEnd_3944867] using wordTrace_append hprefix tailTrace_3944867
  have hstable : (prefixWord ++ tailWord_3944867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944867).length < 2 ^ (prefixWord ++ tailWord_3944867).sum := by decide
  have hdescent : baseEnd_3944867 < baseStart_3944867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944914 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 6]
def baseStart_3944914 : Nat := 118140960795 + 3944914 * 2 ^ 59
def prefixEnd_3944914 : Nat := 4983230072969 + 3 ^ 40 * 3944914 * 2
def baseEnd_3944914 : Nat := 225070780294542637725853

theorem tailTrace_3944914 : CollatzResearch.WordTrace tailWord_3944914 prefixEnd_3944914 225070780294542637725853 := by
  unfold tailWord_3944914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35970708507564447629328449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95921889353505193678209197 35970708507564447629328449)
  ·
    refine ⟨26978031380673335721996337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35970708507564447629328449 26978031380673335721996337)
    ·
      refine ⟨20233523535505001791497253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26978031380673335721996337 20233523535505001791497253)
      ·
        refine ⟨3793785662907187835905735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20233523535505001791497253 3793785662907187835905735)
        ·
          refine ⟨5690678494360781753858603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793785662907187835905735 5690678494360781753858603)
          ·
            refine ⟨8536017741541172630787905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5690678494360781753858603 8536017741541172630787905)
            ·
              refine ⟨6402013306155879473090929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8536017741541172630787905 6402013306155879473090929)
              ·
                refine ⟨4801509979616909604818197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6402013306155879473090929 4801509979616909604818197)
                ·
                  refine ⟨225070780294542637725853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4801509979616909604818197 225070780294542637725853)
                  ·
                    rfl

theorem cell23_3944914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_3944914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944914 prefixEnd_3944914 := by exact prefixLift 3944914
  have htrace : WordTrace (prefixWord ++ tailWord_3944914) baseStart_3944914 baseEnd_3944914 := by
    simpa [prefixWord, tailWord_3944914, baseEnd_3944914] using wordTrace_append hprefix tailTrace_3944914
  have hstable : (prefixWord ++ tailWord_3944914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944914).length < 2 ^ (prefixWord ++ tailWord_3944914).sum := by decide
  have hdescent : baseEnd_3944914 < baseStart_3944914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944940 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_3944940 : Nat := 118140960795 + 3944940 * 2 ^ 59
def prefixEnd_3944940 : Nat := 4983230072969 + 3 ^ 40 * 3944940 * 2
def baseEnd_3944940 : Nat := 675216791049300212602519

theorem tailTrace_3944940 : CollatzResearch.WordTrace tailWord_3944940 prefixEnd_3944940 675216791049300212602519 := by
  unfold tailWord_3944940
  simp only [CollatzResearch.WordTrace]
  refine ⟨71941891164081798478880137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95922521552109064638506849 71941891164081798478880137)
  ·
    refine ⟨53956418373061348859160103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71941891164081798478880137 53956418373061348859160103)
    ·
      refine ⟨80934627559592023288740155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53956418373061348859160103 80934627559592023288740155)
      ·
        refine ⟨121401941339388034933110233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80934627559592023288740155 121401941339388034933110233)
        ·
          refine ⟨91051456004541026199832675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121401941339388034933110233 91051456004541026199832675)
          ·
            refine ⟨136577184006811539299749013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91051456004541026199832675 136577184006811539299749013)
            ·
              refine ⟨6402055500319290904675735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136577184006811539299749013 6402055500319290904675735)
              ·
                refine ⟨9603083250478936357013603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6402055500319290904675735 9603083250478936357013603)
                ·
                  refine ⟨14404624875718404535520405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9603083250478936357013603 14404624875718404535520405)
                  ·
                    refine ⟨675216791049300212602519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14404624875718404535520405 675216791049300212602519)
                    ·
                      rfl

theorem cell23_3944940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_3944940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944940 prefixEnd_3944940 := by exact prefixLift 3944940
  have htrace : WordTrace (prefixWord ++ tailWord_3944940) baseStart_3944940 baseEnd_3944940 := by
    simpa [prefixWord, tailWord_3944940, baseEnd_3944940] using wordTrace_append hprefix tailTrace_3944940
  have hstable : (prefixWord ++ tailWord_3944940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944940).length < 2 ^ (prefixWord ++ tailWord_3944940).sum := by decide
  have hdescent : baseEnd_3944940 < baseStart_3944940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944953 : List Nat := [1, 2, 1, 3, 1, 2, 2, 11]
def baseStart_3944953 : Nat := 118140960795 + 3944953 * 2 ^ 59
def prefixEnd_3944953 : Nat := 4983230072969 + 3 ^ 40 * 3944953 * 2
def baseEnd_3944953 : Nat := 75024335125792929146111

theorem tailTrace_3944953 : CollatzResearch.WordTrace tailWord_3944953 prefixEnd_3944953 75024335125792929146111 := by
  unfold tailWord_3944953
  simp only [CollatzResearch.WordTrace]
  refine ⟨143884256477116500177983513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95922837651411000118655675 143884256477116500177983513)
  ·
    refine ⟨107913192357837375133487635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143884256477116500177983513 107913192357837375133487635)
    ·
      refine ⟨161869788536756062700231453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107913192357837375133487635 161869788536756062700231453)
      ·
        refine ⟨60701170701283523512586795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161869788536756062700231453 60701170701283523512586795)
        ·
          refine ⟨91051756051925285268880193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60701170701283523512586795 91051756051925285268880193)
          ·
            refine ⟨68288817038943963951660145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91051756051925285268880193 68288817038943963951660145)
            ·
              refine ⟨51216612779207972963745109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68288817038943963951660145 51216612779207972963745109)
              ·
                refine ⟨75024335125792929146111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 51216612779207972963745109 75024335125792929146111)
                ·
                  rfl

theorem cell23_3944953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 11].length) (baseStart_3944953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944953 prefixEnd_3944953 := by exact prefixLift 3944953
  have htrace : WordTrace (prefixWord ++ tailWord_3944953) baseStart_3944953 baseEnd_3944953 := by
    simpa [prefixWord, tailWord_3944953, baseEnd_3944953] using wordTrace_append hprefix tailTrace_3944953
  have hstable : (prefixWord ++ tailWord_3944953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944953).length < 2 ^ (prefixWord ++ tailWord_3944953).sum := by decide
  have hdescent : baseEnd_3944953 < baseStart_3944953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944964 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3944964 : Nat := 118140960795 + 3944964 * 2 ^ 59
def prefixEnd_3944964 : Nat := 4983230072969 + 3 ^ 40 * 3944964 * 2
def baseEnd_3944964 : Nat := 2025662696683608543907447

theorem tailTrace_3944964 : CollatzResearch.WordTrace tailWord_3944964 prefixEnd_3944964 2025662696683608543907447 := by
  unfold tailWord_3944964
  simp only [CollatzResearch.WordTrace]
  refine ⟨71942328840038324528316973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95923105120051099371089297 71942328840038324528316973)
  ·
    refine ⟨26978373315014371698118865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71942328840038324528316973 26978373315014371698118865)
    ·
      refine ⟨20233779986260778773589149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26978373315014371698118865 20233779986260778773589149)
      ·
        refine ⟨7587667494847792040095931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20233779986260778773589149 7587667494847792040095931)
        ·
          refine ⟨11381501242271688060143897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7587667494847792040095931 11381501242271688060143897)
          ·
            refine ⟨8536125931703766045107923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11381501242271688060143897 8536125931703766045107923)
            ·
              refine ⟨12804188897555649067661885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8536125931703766045107923 12804188897555649067661885)
              ·
                refine ⟨4801570836583368400373207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12804188897555649067661885 4801570836583368400373207)
                ·
                  refine ⟨7202356254875052600559811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801570836583368400373207 7202356254875052600559811)
                  ·
                    refine ⟨10803534382312578900839717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7202356254875052600559811 10803534382312578900839717)
                    ·
                      refine ⟨2025662696683608543907447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10803534382312578900839717 2025662696683608543907447)
                      ·
                        rfl

theorem cell23_3944964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3944964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944964 prefixEnd_3944964 := by exact prefixLift 3944964
  have htrace : WordTrace (prefixWord ++ tailWord_3944964) baseStart_3944964 baseEnd_3944964 := by
    simpa [prefixWord, tailWord_3944964, baseEnd_3944964] using wordTrace_append hprefix tailTrace_3944964
  have hstable : (prefixWord ++ tailWord_3944964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944964).length < 2 ^ (prefixWord ++ tailWord_3944964).sum := by decide
  have hdescent : baseEnd_3944964 < baseStart_3944964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944974 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_3944974 : Nat := 118140960795 + 3944974 * 2 ^ 59
def prefixEnd_3944974 : Nat := 4983230072969 + 3 ^ 40 * 3944974 * 2
def baseEnd_3944974 : Nat := 675222610496717834927467

theorem tailTrace_3944974 : CollatzResearch.WordTrace tailWord_3944974 prefixEnd_3944974 675222610496717834927467 := by
  unfold tailWord_3944974
  simp only [CollatzResearch.WordTrace]
  refine ⟨17985627801255052595562247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95923348273360280509665317 17985627801255052595562247)
  ·
    refine ⟨26978441701882578893343371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17985627801255052595562247 26978441701882578893343371)
    ·
      refine ⟨40467662552823868340015057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26978441701882578893343371 40467662552823868340015057)
      ·
        refine ⟨30350746914617901255011293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40467662552823868340015057 30350746914617901255011293)
        ·
          refine ⟨11381530092981712970629235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30350746914617901255011293 11381530092981712970629235)
          ·
            refine ⟨17072295139472569455943853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11381530092981712970629235 17072295139472569455943853)
            ·
              refine ⟨6402110677302213545978945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17072295139472569455943853 6402110677302213545978945)
              ·
                refine ⟨4801583007976660159484209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6402110677302213545978945 4801583007976660159484209)
                ·
                  refine ⟨3601187255982495119613157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4801583007976660159484209 3601187255982495119613157)
                  ·
                    refine ⟨675222610496717834927467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3601187255982495119613157 675222610496717834927467)
                    ·
                      rfl

theorem cell23_3944974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_3944974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944974 prefixEnd_3944974 := by exact prefixLift 3944974
  have htrace : WordTrace (prefixWord ++ tailWord_3944974) baseStart_3944974 baseEnd_3944974 := by
    simpa [prefixWord, tailWord_3944974, baseEnd_3944974] using wordTrace_append hprefix tailTrace_3944974
  have hstable : (prefixWord ++ tailWord_3944974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944974).length < 2 ^ (prefixWord ++ tailWord_3944974).sum := by decide
  have hdescent : baseEnd_3944974 < baseStart_3944974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944981 : List Nat := [1, 3, 2, 1, 3, 1, 1, 6, 1, 2, 2]
def baseStart_3944981 : Nat := 118140960795 + 3944981 * 2 ^ 59
def prefixEnd_3944981 : Nat := 4983230072969 + 3 ^ 40 * 3944981 * 2
def baseEnd_3944981 : Nat := 2025671425854734977394869

theorem tailTrace_3944981 : CollatzResearch.WordTrace tailWord_3944981 prefixEnd_3944981 2025671425854734977394869 := by
  unfold tailWord_3944981
  simp only [CollatzResearch.WordTrace]
  refine ⟨143885277721015060960002797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95923518480676707306668531 143885277721015060960002797)
  ·
    refine ⟨53956979145380647860001049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143885277721015060960002797 53956979145380647860001049)
    ·
      refine ⟨40467734359035485895000787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53956979145380647860001049 40467734359035485895000787)
      ·
        refine ⟨60701601538553228842501181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40467734359035485895000787 60701601538553228842501181)
        ·
          refine ⟨22763100576957460815937943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60701601538553228842501181 22763100576957460815937943)
          ·
            refine ⟨34144650865436191223906915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22763100576957460815937943 34144650865436191223906915)
            ·
              refine ⟨51216976298154286835860373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34144650865436191223906915 51216976298154286835860373)
              ·
                refine ⟨2400795763975982195430955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51216976298154286835860373 2400795763975982195430955)
                ·
                  refine ⟨3601193645963973293146433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400795763975982195430955 3601193645963973293146433)
                  ·
                    refine ⟨2700895234472979969859825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3601193645963973293146433 2700895234472979969859825)
                    ·
                      refine ⟨2025671425854734977394869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700895234472979969859825 2025671425854734977394869)
                      ·
                        rfl

theorem cell23_3944981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_3944981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944981 prefixEnd_3944981 := by exact prefixLift 3944981
  have htrace : WordTrace (prefixWord ++ tailWord_3944981) baseStart_3944981 baseEnd_3944981 := by
    simpa [prefixWord, tailWord_3944981, baseEnd_3944981] using wordTrace_append hprefix tailTrace_3944981
  have hstable : (prefixWord ++ tailWord_3944981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944981).length < 2 ^ (prefixWord ++ tailWord_3944981).sum := by decide
  have hdescent : baseEnd_3944981 < baseStart_3944981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3944997 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_3944997 : Nat := 118140960795 + 3944997 * 2 ^ 59
def prefixEnd_3944997 : Nat := 4983230072969 + 3 ^ 40 * 3944997 * 2
def baseEnd_3944997 : Nat := 2025679641545206914794795

theorem tailTrace_3944997 : CollatzResearch.WordTrace tailWord_3944997 prefixEnd_3944997 2025679641545206914794795 := by
  unfold tailWord_3944997
  simp only [CollatzResearch.WordTrace]
  refine ⟨143885861288957095692585245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95923907525971397128390163 143885861288957095692585245)
  ·
    refine ⟨53957197983358910884719467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143885861288957095692585245 53957197983358910884719467)
    ·
      refine ⟨80935796975038366327079201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53957197983358910884719467 80935796975038366327079201)
      ·
        refine ⟨60701847731278774745309401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80935796975038366327079201 60701847731278774745309401)
        ·
          refine ⟨45526385798459081058982051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60701847731278774745309401 45526385798459081058982051)
          ·
            refine ⟨68289578697688621588473077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45526385798459081058982051 68289578697688621588473077)
            ·
              refine ⟨6402148002908308273919351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68289578697688621588473077 6402148002908308273919351)
              ·
                refine ⟨9603222004362462410879027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6402148002908308273919351 9603222004362462410879027)
                ·
                  refine ⟨14404833006543693616318541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9603222004362462410879027 14404833006543693616318541)
                  ·
                    refine ⟨5401812377453885106119453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14404833006543693616318541 5401812377453885106119453)
                    ·
                      refine ⟨2025679641545206914794795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5401812377453885106119453 2025679641545206914794795)
                      ·
                        rfl

theorem cell23_3944997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_3944997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3944997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3944997 prefixEnd_3944997 := by exact prefixLift 3944997
  have htrace : WordTrace (prefixWord ++ tailWord_3944997) baseStart_3944997 baseEnd_3944997 := by
    simpa [prefixWord, tailWord_3944997, baseEnd_3944997] using wordTrace_append hprefix tailTrace_3944997
  have hstable : (prefixWord ++ tailWord_3944997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3944997).length < 2 ^ (prefixWord ++ tailWord_3944997).sum := by decide
  have hdescent : baseEnd_3944997 < baseStart_3944997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3944997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945010 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_3945010 : Nat := 118140960795 + 3945010 * 2 ^ 59
def prefixEnd_3945010 : Nat := 4983230072969 + 3 ^ 40 * 3945010 * 2
def baseEnd_3945010 : Nat := 2025686316793715363932235

theorem tailTrace_3945010 : CollatzResearch.WordTrace tailWord_3945010 prefixEnd_3945010 2025686316793715363932235 := by
  unfold tailWord_3945010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35971583859477499728202121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95924223625273332608538989 35971583859477499728202121)
  ·
    refine ⟨26978687894608124796151591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35971583859477499728202121 26978687894608124796151591)
    ·
      refine ⟨40468031841912187194227387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26978687894608124796151591 40468031841912187194227387)
      ·
        refine ⟨60702047762868280791341081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40468031841912187194227387 60702047762868280791341081)
        ·
          refine ⟨45526535822151210593505811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60702047762868280791341081 45526535822151210593505811)
          ·
            refine ⟨68289803733226815890258717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45526535822151210593505811 68289803733226815890258717)
            ·
              refine ⟨25608676399960055958847019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68289803733226815890258717 25608676399960055958847019)
              ·
                refine ⟨38413014599940083938270529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25608676399960055958847019 38413014599940083938270529)
                ·
                  refine ⟨28809760949955062953702897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38413014599940083938270529 28809760949955062953702897)
                  ·
                    refine ⟨21607320712466297215277173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28809760949955062953702897 21607320712466297215277173)
                    ·
                      refine ⟨2025686316793715363932235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21607320712466297215277173 2025686316793715363932235)
                      ·
                        rfl

theorem cell23_3945010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_3945010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945010 prefixEnd_3945010 := by exact prefixLift 3945010
  have htrace : WordTrace (prefixWord ++ tailWord_3945010) baseStart_3945010 baseEnd_3945010 := by
    simpa [prefixWord, tailWord_3945010, baseEnd_3945010] using wordTrace_append hprefix tailTrace_3945010
  have hstable : (prefixWord ++ tailWord_3945010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945010).length < 2 ^ (prefixWord ++ tailWord_3945010).sum := by decide
  have hdescent : baseEnd_3945010 < baseStart_3945010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945024 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 1, 3, 2]
def baseStart_3945024 : Nat := 118140960795 + 3945024 * 2 ^ 59
def prefixEnd_3945024 : Nat := 4983230072969 + 3 ^ 40 * 3945024 * 2
def baseEnd_3945024 : Nat := 2025693505522878309157171

theorem tailTrace_3945024 : CollatzResearch.WordTrace tailWord_3945024 prefixEnd_3945024 2025693505522878309157171 := by
  unfold tailWord_3945024
  simp only [CollatzResearch.WordTrace]
  refine ⟨71943423029929639651909063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95924564039906186202545417 71943423029929639651909063)
  ·
    refine ⟨107915134544894459477863595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71943423029929639651909063 107915134544894459477863595)
    ·
      refine ⟨161872701817341689216795393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107915134544894459477863595 161872701817341689216795393)
      ·
        refine ⟨121404526363006266912596545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161872701817341689216795393 121404526363006266912596545)
        ·
          refine ⟨91053394772254700184447409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121404526363006266912596545 91053394772254700184447409)
          ·
            refine ⟨68290046079191025138335557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91053394772254700184447409 68290046079191025138335557)
            ·
              refine ⟨12804383639848317213437917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68290046079191025138335557 12804383639848317213437917)
              ·
                refine ⟨4801643864943118955039219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12804383639848317213437917 4801643864943118955039219)
                ·
                  refine ⟨7202465797414678432558829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801643864943118955039219 7202465797414678432558829)
                  ·
                    refine ⟨2700924674030504412209561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7202465797414678432558829 2700924674030504412209561)
                    ·
                      refine ⟨2025693505522878309157171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700924674030504412209561 2025693505522878309157171)
                      ·
                        rfl

theorem cell23_3945024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_3945024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945024 prefixEnd_3945024 := by exact prefixLift 3945024
  have htrace : WordTrace (prefixWord ++ tailWord_3945024) baseStart_3945024 baseEnd_3945024 := by
    simpa [prefixWord, tailWord_3945024, baseEnd_3945024] using wordTrace_append hprefix tailTrace_3945024
  have hstable : (prefixWord ++ tailWord_3945024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945024).length < 2 ^ (prefixWord ++ tailWord_3945024).sum := by decide
  have hdescent : baseEnd_3945024 < baseStart_3945024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945058 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3945058 : Nat := 118140960795 + 3945058 * 2 ^ 59
def prefixEnd_3945058 : Nat := 4983230072969 + 3 ^ 40 * 3945058 * 2
def baseEnd_3945058 : Nat := 2025710963865131176132015

theorem tailTrace_3945058 : CollatzResearch.WordTrace tailWord_3945058 prefixEnd_3945058 2025710963865131176132015 := by
  unfold tailWord_3945058
  simp only [CollatzResearch.WordTrace]
  refine ⟨35972021535434025777638957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95925390761157402073703885 35972021535434025777638957)
  ·
    refine ⟨13489508075787759666614609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35972021535434025777638957 13489508075787759666614609)
    ·
      refine ⟨10117131056840819749960957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13489508075787759666614609 10117131056840819749960957)
      ·
        refine ⟨3793924146315307406235359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10117131056840819749960957 3793924146315307406235359)
        ·
          refine ⟨5690886219472961109353039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793924146315307406235359 5690886219472961109353039)
          ·
            refine ⟨8536329329209441664029559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5690886219472961109353039 8536329329209441664029559)
            ·
              refine ⟨12804493993814162496044339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8536329329209441664029559 12804493993814162496044339)
              ·
                refine ⟨19206740990721243744066509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12804493993814162496044339 19206740990721243744066509)
                ·
                  refine ⟨7202527871520466404024941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19206740990721243744066509 7202527871520466404024941)
                  ·
                    refine ⟨2700947951820174901509353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7202527871520466404024941 2700947951820174901509353)
                    ·
                      refine ⟨2025710963865131176132015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2700947951820174901509353 2025710963865131176132015)
                      ·
                        rfl

theorem cell23_3945058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3945058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945058 prefixEnd_3945058 := by exact prefixLift 3945058
  have htrace : WordTrace (prefixWord ++ tailWord_3945058) baseStart_3945058 baseEnd_3945058 := by
    simpa [prefixWord, tailWord_3945058, baseEnd_3945058] using wordTrace_append hprefix tailTrace_3945058
  have hstable : (prefixWord ++ tailWord_3945058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945058).length < 2 ^ (prefixWord ++ tailWord_3945058).sum := by decide
  have hdescent : baseEnd_3945058 < baseStart_3945058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945060 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 9]
def baseStart_3945060 : Nat := 118140960795 + 3945060 * 2 ^ 59
def prefixEnd_3945060 : Nat := 4983230072969 + 3 ^ 40 * 3945060 * 2
def baseEnd_3945060 : Nat := 225079110091826685367445

theorem tailTrace_3945060 : CollatzResearch.WordTrace tailWord_3945060 prefixEnd_3945060 225079110091826685367445 := by
  unfold tailWord_3945060
  simp only [CollatzResearch.WordTrace]
  refine ⟨71944079543864428726064317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95925439391819238301419089 71944079543864428726064317)
  ·
    refine ⟨26979029828949160772274119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71944079543864428726064317 26979029828949160772274119)
    ·
      refine ⟨40468544743423741158411179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26979029828949160772274119 40468544743423741158411179)
      ·
        refine ⟨60702817115135611737616769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40468544743423741158411179 60702817115135611737616769)
        ·
          refine ⟨45527112836351708803212577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60702817115135611737616769 45527112836351708803212577)
          ·
            refine ⟨34145334627263781602409433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45527112836351708803212577 34145334627263781602409433)
            ·
              refine ⟨25609000970447836201807075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34145334627263781602409433 25609000970447836201807075)
              ·
                refine ⟨38413501455671754302710613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25609000970447836201807075 38413501455671754302710613)
                ·
                  refine ⟨225079110091826685367445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38413501455671754302710613 225079110091826685367445)
                  ·
                    rfl

theorem cell23_3945060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_3945060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945060 prefixEnd_3945060 := by exact prefixLift 3945060
  have htrace : WordTrace (prefixWord ++ tailWord_3945060) baseStart_3945060 baseEnd_3945060 := by
    simpa [prefixWord, tailWord_3945060, baseEnd_3945060] using wordTrace_append hprefix tailTrace_3945060
  have hstable : (prefixWord ++ tailWord_3945060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945060).length < 2 ^ (prefixWord ++ tailWord_3945060).sum := by decide
  have hdescent : baseEnd_3945060 < baseStart_3945060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945100 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_3945100 : Nat := 118140960795 + 3945100 * 2 ^ 59
def prefixEnd_3945100 : Nat := 4983230072969 + 3 ^ 40 * 3945100 * 2
def baseEnd_3945100 : Nat := 2025732530052620011806821

theorem tailTrace_3945100 : CollatzResearch.WordTrace tailWord_3945100 prefixEnd_3945100 2025732530052620011806821 := by
  unfold tailWord_3945100
  simp only [CollatzResearch.WordTrace]
  refine ⟨71944809003791972141792377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95926412005055962855723169 71944809003791972141792377)
  ·
    refine ⟨53958606752843979106344283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71944809003791972141792377 53958606752843979106344283)
    ·
      refine ⟨80937910129265968659516425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53958606752843979106344283 80937910129265968659516425)
      ·
        refine ⟨60703432596949476494637319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80937910129265968659516425 60703432596949476494637319)
        ·
          refine ⟨91055148895424214741955979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60703432596949476494637319 91055148895424214741955979)
          ·
            refine ⟨136582723343136322112933969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91055148895424214741955979 136582723343136322112933969)
            ·
              refine ⟨102437042507352241584700477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136582723343136322112933969 102437042507352241584700477)
              ·
                refine ⟨38413890940257090594262679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102437042507352241584700477 38413890940257090594262679)
                ·
                  refine ⟨57620836410385635891394019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38413890940257090594262679 57620836410385635891394019)
                  ·
                    refine ⟨86431254615578453837091029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57620836410385635891394019 86431254615578453837091029)
                    ·
                      refine ⟨2025732530052620011806821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86431254615578453837091029 2025732530052620011806821)
                      ·
                        rfl

theorem cell23_3945100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_3945100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945100 prefixEnd_3945100 := by exact prefixLift 3945100
  have htrace : WordTrace (prefixWord ++ tailWord_3945100) baseStart_3945100 baseEnd_3945100 := by
    simpa [prefixWord, tailWord_3945100, baseEnd_3945100] using wordTrace_append hprefix tailTrace_3945100
  have hstable : (prefixWord ++ tailWord_3945100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945100).length < 2 ^ (prefixWord ++ tailWord_3945100).sum := by decide
  have hdescent : baseEnd_3945100 < baseStart_3945100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945164 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3945164 : Nat := 118140960795 + 3945164 * 2 ^ 59
def prefixEnd_3945164 : Nat := 4983230072969 + 3 ^ 40 * 3945164 * 2
def baseEnd_3945164 : Nat := 2025765392814507761406527

theorem tailTrace_3945164 : CollatzResearch.WordTrace tailWord_3945164 prefixEnd_3945164 2025765392814507761406527 := by
  unfold tailWord_3945164
  simp only [CollatzResearch.WordTrace]
  refine ⟨71945976139676041606957273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95927968186234722142609697 71945976139676041606957273)
  ·
    refine ⟨53959482104757031205217955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71945976139676041606957273 53959482104757031205217955)
    ·
      refine ⟨80939223157135546807826933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53959482104757031205217955 80939223157135546807826933)
      ·
        refine ⟨7588052170981457513233775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80939223157135546807826933 7588052170981457513233775)
        ·
          refine ⟨11382078256472186269850663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588052170981457513233775 11382078256472186269850663)
          ·
            refine ⟨17073117384708279404775995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382078256472186269850663 17073117384708279404775995)
            ·
              refine ⟨25609676077062419107163993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17073117384708279404775995 25609676077062419107163993)
              ·
                refine ⟨19207257057796814330372995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25609676077062419107163993 19207257057796814330372995)
                ·
                  refine ⟨28810885586695221495559493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19207257057796814330372995 28810885586695221495559493)
                  ·
                    refine ⟨5402041047505354030417405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28810885586695221495559493 5402041047505354030417405)
                    ·
                      refine ⟨2025765392814507761406527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5402041047505354030417405 2025765392814507761406527)
                      ·
                        rfl

theorem cell23_3945164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3945164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945164 prefixEnd_3945164 := by exact prefixLift 3945164
  have htrace : WordTrace (prefixWord ++ tailWord_3945164) baseStart_3945164 baseEnd_3945164 := by
    simpa [prefixWord, tailWord_3945164, baseEnd_3945164] using wordTrace_append hprefix tailTrace_3945164
  have hstable : (prefixWord ++ tailWord_3945164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945164).length < 2 ^ (prefixWord ++ tailWord_3945164).sum := by decide
  have hdescent : baseEnd_3945164 < baseStart_3945164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945177 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 3]
def baseStart_3945177 : Nat := 118140960795 + 3945177 * 2 ^ 59
def prefixEnd_3945177 : Nat := 4983230072969 + 3 ^ 40 * 3945177 * 2
def baseEnd_3945177 : Nat := 2025772068063016210543967

theorem tailTrace_3945177 : CollatzResearch.WordTrace tailWord_3945177 prefixEnd_3945177 2025772068063016210543967 := by
  unfold tailWord_3945177
  simp only [CollatzResearch.WordTrace]
  refine ⟨143892426428304986434137785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95928284285536657622758523 143892426428304986434137785)
  ·
    refine ⟨107919319821228739825603339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143892426428304986434137785 107919319821228739825603339)
    ·
      refine ⟨161878979731843109738405009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107919319821228739825603339 161878979731843109738405009)
      ·
        refine ⟨121409234798882332303803757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161878979731843109738405009 121409234798882332303803757)
        ·
          refine ⟨45528463049580874613926409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121409234798882332303803757 45528463049580874613926409)
          ·
            refine ⟨34146347287185655960444807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45528463049580874613926409 34146347287185655960444807)
            ·
              refine ⟨51219520930778483940667211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34146347287185655960444807 51219520930778483940667211)
              ·
                refine ⟨76829281396167725911000817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51219520930778483940667211 76829281396167725911000817)
                ·
                  refine ⟨57621961047125794433250613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76829281396167725911000817 57621961047125794433250613)
                  ·
                    refine ⟨5402058848168043228117245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57621961047125794433250613 5402058848168043228117245)
                    ·
                      refine ⟨2025772068063016210543967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5402058848168043228117245 2025772068063016210543967)
                      ·
                        rfl

theorem cell23_3945177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_3945177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945177 prefixEnd_3945177 := by exact prefixLift 3945177
  have htrace : WordTrace (prefixWord ++ tailWord_3945177) baseStart_3945177 baseEnd_3945177 := by
    simpa [prefixWord, tailWord_3945177, baseEnd_3945177] using wordTrace_append hprefix tailTrace_3945177
  have hstable : (prefixWord ++ tailWord_3945177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945177).length < 2 ^ (prefixWord ++ tailWord_3945177).sum := by decide
  have hdescent : baseEnd_3945177 < baseStart_3945177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945188 : List Nat := [2, 3, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_3945188 : Nat := 118140960795 + 3945188 * 2 ^ 59
def prefixEnd_3945188 : Nat := 4983230072969 + 3 ^ 40 * 3945188 * 2
def baseEnd_3945188 : Nat := 675259238783405222502139

theorem tailTrace_3945188 : CollatzResearch.WordTrace tailWord_3945188 prefixEnd_3945188 675259238783405222502139 := by
  unfold tailWord_3945188
  simp only [CollatzResearch.WordTrace]
  refine ⟨71946413815632567656394109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95928551754176756875192145 71946413815632567656394109)
  ·
    refine ⟨26979905180862212871147791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71946413815632567656394109 26979905180862212871147791)
    ·
      refine ⟨40469857771293319306721687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26979905180862212871147791 40469857771293319306721687)
      ·
        refine ⟨60704786656939978960082531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40469857771293319306721687 60704786656939978960082531)
        ·
          refine ⟨91057179985409968440123797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60704786656939978960082531 91057179985409968440123797)
          ·
            refine ⟨4268305311816092270630803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91057179985409968440123797 4268305311816092270630803)
            ·
              refine ⟨6402457967724138405946205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268305311816092270630803 6402457967724138405946205)
              ·
                refine ⟨2400921737896551902229827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6402457967724138405946205 2400921737896551902229827)
                ·
                  refine ⟨3601382606844827853344741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400921737896551902229827 3601382606844827853344741)
                  ·
                    refine ⟨675259238783405222502139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3601382606844827853344741 675259238783405222502139)
                    ·
                      rfl

theorem cell23_3945188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_3945188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945188 prefixEnd_3945188 := by exact prefixLift 3945188
  have htrace : WordTrace (prefixWord ++ tailWord_3945188) baseStart_3945188 baseEnd_3945188 := by
    simpa [prefixWord, tailWord_3945188, baseEnd_3945188] using wordTrace_append hprefix tailTrace_3945188
  have hstable : (prefixWord ++ tailWord_3945188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945188).length < 2 ^ (prefixWord ++ tailWord_3945188).sum := by decide
  have hdescent : baseEnd_3945188 < baseStart_3945188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945217 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_3945217 : Nat := 118140960795 + 3945217 * 2 ^ 59
def prefixEnd_3945217 : Nat := 4983230072969 + 3 ^ 40 * 3945217 * 2
def baseEnd_3945217 : Nat := 2025792607289196054043783

theorem tailTrace_3945217 : CollatzResearch.WordTrace tailWord_3945217 prefixEnd_3945217 2025792607289196054043783 := by
  unfold tailWord_3945217
  simp only [CollatzResearch.WordTrace]
  refine ⟨143893885348160073265593905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95929256898773382177062603 143893885348160073265593905)
  ·
    refine ⟨107920414011120054949195429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143893885348160073265593905 107920414011120054949195429)
    ·
      refine ⟨20235077627085010302974143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107920414011120054949195429 20235077627085010302974143)
      ·
        refine ⟨30352616440627515454461215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20235077627085010302974143 30352616440627515454461215)
        ·
          refine ⟨45528924660941273181691823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30352616440627515454461215 45528924660941273181691823)
          ·
            refine ⟨68293386991411909772537735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45528924660941273181691823 68293386991411909772537735)
            ·
              refine ⟨102440080487117864658806603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68293386991411909772537735 102440080487117864658806603)
              ·
                refine ⟨153660120730676796988209905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102440080487117864658806603 153660120730676796988209905)
                ·
                  refine ⟨115245090548007597741157429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153660120730676796988209905 115245090548007597741157429)
                  ·
                    refine ⟨10804227238875712288233509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115245090548007597741157429 10804227238875712288233509)
                    ·
                      refine ⟨2025792607289196054043783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10804227238875712288233509 2025792607289196054043783)
                      ·
                        rfl

theorem cell23_3945217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_3945217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945217 prefixEnd_3945217 := by exact prefixLift 3945217
  have htrace : WordTrace (prefixWord ++ tailWord_3945217) baseStart_3945217 baseEnd_3945217 := by
    simpa [prefixWord, tailWord_3945217, baseEnd_3945217] using wordTrace_append hprefix tailTrace_3945217
  have hstable : (prefixWord ++ tailWord_3945217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945217).length < 2 ^ (prefixWord ++ tailWord_3945217).sum := by decide
  have hdescent : baseEnd_3945217 < baseStart_3945217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945218 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 6]
def baseStart_3945218 : Nat := 118140960795 + 3945218 * 2 ^ 59
def prefixEnd_3945218 : Nat := 4983230072969 + 3 ^ 40 * 3945218 * 2
def baseEnd_3945218 : Nat := 225088124529983394459031

theorem tailTrace_3945218 : CollatzResearch.WordTrace tailWord_3945218 prefixEnd_3945218 225088124529983394459031 := by
  unfold tailWord_3945218
  simp only [CollatzResearch.WordTrace]
  refine ⟨35973480455289112609095077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95929281214104300290920205 35973480455289112609095077)
  ·
    refine ⟨6745027585366708614205327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35973480455289112609095077 6745027585366708614205327)
    ·
      refine ⟨10117541378050062921307991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6745027585366708614205327 10117541378050062921307991)
      ·
        refine ⟨15176312067075094381961987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10117541378050062921307991 15176312067075094381961987)
        ·
          refine ⟨22764468100612641572942981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15176312067075094381961987 22764468100612641572942981)
          ·
            refine ⟨4268337768864870294926809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22764468100612641572942981 4268337768864870294926809)
            ·
              refine ⟨3201253326648652721195107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4268337768864870294926809 3201253326648652721195107)
              ·
                refine ⟨4801879989972979081792661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201253326648652721195107 4801879989972979081792661)
                ·
                  refine ⟨225088124529983394459031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4801879989972979081792661 225088124529983394459031)
                  ·
                    rfl

theorem cell23_3945218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_3945218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945218 prefixEnd_3945218 := by exact prefixLift 3945218
  have htrace : WordTrace (prefixWord ++ tailWord_3945218) baseStart_3945218 baseEnd_3945218 := by
    simpa [prefixWord, tailWord_3945218, baseEnd_3945218] using wordTrace_append hprefix tailTrace_3945218
  have hstable : (prefixWord ++ tailWord_3945218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945218).length < 2 ^ (prefixWord ++ tailWord_3945218).sum := by decide
  have hdescent : baseEnd_3945218 < baseStart_3945218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945227 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 1, 6]
def baseStart_3945227 : Nat := 118140960795 + 3945227 * 2 ^ 59
def prefixEnd_3945227 : Nat := 4983230072969 + 3 ^ 40 * 3945227 * 2
def baseEnd_3945227 : Nat := 675265914031913671639579

theorem tailTrace_3945227 : CollatzResearch.WordTrace tailWord_3945227 prefixEnd_3945227 675265914031913671639579 := by
  unfold tailWord_3945227
  simp only [CollatzResearch.WordTrace]
  refine ⟨143894250078123844973457935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95929500052082563315638623 143894250078123844973457935)
  ·
    refine ⟨215841375117185767460186903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143894250078123844973457935 215841375117185767460186903)
    ·
      refine ⟨323762062675778651190280355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215841375117185767460186903 323762062675778651190280355)
      ·
        refine ⟨485643094013667976785420533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323762062675778651190280355 485643094013667976785420533)
        ·
          refine ⟨45529040063781372823633175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 485643094013667976785420533 45529040063781372823633175)
          ·
            refine ⟨68293560095672059235449763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45529040063781372823633175 68293560095672059235449763)
            ·
              refine ⟨102440340143508088853174645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68293560095672059235449763 102440340143508088853174645)
              ·
                refine ⟨9603781888453883329985123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102440340143508088853174645 9603781888453883329985123)
                ·
                  refine ⟨14405672832680824994977685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9603781888453883329985123 14405672832680824994977685)
                  ·
                    refine ⟨675265914031913671639579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14405672832680824994977685 675265914031913671639579)
                    ·
                      rfl

theorem cell23_3945227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 6].length) (baseStart_3945227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945227 prefixEnd_3945227 := by exact prefixLift 3945227
  have htrace : WordTrace (prefixWord ++ tailWord_3945227) baseStart_3945227 baseEnd_3945227 := by
    simpa [prefixWord, tailWord_3945227, baseEnd_3945227] using wordTrace_append hprefix tailTrace_3945227
  have hstable : (prefixWord ++ tailWord_3945227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945227).length < 2 ^ (prefixWord ++ tailWord_3945227).sum := by decide
  have hdescent : baseEnd_3945227 < baseStart_3945227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945244 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_3945244 : Nat := 118140960795 + 3945244 * 2 ^ 59
def prefixEnd_3945244 : Nat := 4983230072969 + 3 ^ 40 * 3945244 * 2
def baseEnd_3945244 : Nat := 675268823755622482802053

theorem tailTrace_3945244 : CollatzResearch.WordTrace tailWord_3945244 prefixEnd_3945244 675268823755622482802053 := by
  unfold tailWord_3945244
  simp only [CollatzResearch.WordTrace]
  refine ⟨71947435059531128438413393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95929913412708171251217857 71947435059531128438413393)
  ·
    refine ⟨53960576294648346328810045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71947435059531128438413393 53960576294648346328810045)
    ·
      refine ⟨20235216110493129873303767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53960576294648346328810045 20235216110493129873303767)
      ·
        refine ⟨30352824165739694809955651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20235216110493129873303767 30352824165739694809955651)
        ·
          refine ⟨45529236248609542214933477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30352824165739694809955651 45529236248609542214933477)
          ·
            refine ⟨8536731796614289165300027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45529236248609542214933477 8536731796614289165300027)
            ·
              refine ⟨12805097694921433747950041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8536731796614289165300027 12805097694921433747950041)
              ·
                refine ⟨9603823271191075310962531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12805097694921433747950041 9603823271191075310962531)
                ·
                  refine ⟨14405734906786612966443797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9603823271191075310962531 14405734906786612966443797)
                  ·
                    refine ⟨675268823755622482802053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14405734906786612966443797 675268823755622482802053)
                    ·
                      rfl

theorem cell23_3945244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_3945244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945244 prefixEnd_3945244 := by exact prefixLift 3945244
  have htrace : WordTrace (prefixWord ++ tailWord_3945244) baseStart_3945244 baseEnd_3945244 := by
    simpa [prefixWord, tailWord_3945244, baseEnd_3945244] using wordTrace_append hprefix tailTrace_3945244
  have hstable : (prefixWord ++ tailWord_3945244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945244).length < 2 ^ (prefixWord ++ tailWord_3945244).sum := by decide
  have hdescent : baseEnd_3945244 < baseStart_3945244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945262 : List Nat := [4, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_3945262 : Nat := 118140960795 + 3945262 * 2 ^ 59
def prefixEnd_3945262 : Nat := 4983230072969 + 3 ^ 40 * 3945262 * 2
def baseEnd_3945262 : Nat := 2025815713918648377981077

theorem tailTrace_3945262 : CollatzResearch.WordTrace tailWord_3945262 prefixEnd_3945262 2025815713918648377981077 := by
  unfold tailWord_3945262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17986940829124630743872755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95930351088664697300654693 17986940829124630743872755)
  ·
    refine ⟨26980411243686946115809133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17986940829124630743872755 26980411243686946115809133)
    ·
      refine ⟨10117654216382604793428425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26980411243686946115809133 10117654216382604793428425)
      ·
        refine ⟨7588240662286953595071319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10117654216382604793428425 7588240662286953595071319)
        ·
          refine ⟨11382360993430430392606979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588240662286953595071319 11382360993430430392606979)
          ·
            refine ⟨17073541490145645588910469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382360993430430392606979 17073541490145645588910469)
            ·
              refine ⟨3201289029402308547920713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17073541490145645588910469 3201289029402308547920713)
              ·
                refine ⟨2400966772051731410940535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201289029402308547920713 2400966772051731410940535)
                ·
                  refine ⟨3601450158077597116410803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400966772051731410940535 3601450158077597116410803)
                  ·
                    refine ⟨5402175237116395674616205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3601450158077597116410803 5402175237116395674616205)
                    ·
                      refine ⟨2025815713918648377981077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5402175237116395674616205 2025815713918648377981077)
                      ·
                        rfl

theorem cell23_3945262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_3945262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945262 prefixEnd_3945262 := by exact prefixLift 3945262
  have htrace : WordTrace (prefixWord ++ tailWord_3945262) baseStart_3945262 baseEnd_3945262 := by
    simpa [prefixWord, tailWord_3945262, baseEnd_3945262] using wordTrace_append hprefix tailTrace_3945262
  have hstable : (prefixWord ++ tailWord_3945262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945262).length < 2 ^ (prefixWord ++ tailWord_3945262).sum := by decide
  have hdescent : baseEnd_3945262 < baseStart_3945262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945287 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 4, 7]
def baseStart_3945287 : Nat := 118140960795 + 3945287 * 2 ^ 59
def prefixEnd_3945287 : Nat := 4983230072969 + 3 ^ 40 * 3945287 * 2
def baseEnd_3945287 : Nat := 675276183645003593389487

theorem tailTrace_3945287 : CollatzResearch.WordTrace tailWord_3945287 prefixEnd_3945287 675276183645003593389487 := by
  unfold tailWord_3945287
  simp only [CollatzResearch.WordTrace]
  refine ⟨143896438457906475220642115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95930958971937650147094743 143896438457906475220642115)
  ·
    refine ⟨215844657686859712830963173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143896438457906475220642115 215844657686859712830963173)
    ·
      refine ⟨40470873316286196155805595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215844657686859712830963173 40470873316286196155805595)
      ·
        refine ⟨60706309974429294233708393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40470873316286196155805595 60706309974429294233708393)
        ·
          refine ⟨45529732480821970675281295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60706309974429294233708393 45529732480821970675281295)
          ·
            refine ⟨68294598721232956012921943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45529732480821970675281295 68294598721232956012921943)
            ·
              refine ⟨102441898081849434019382915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68294598721232956012921943 102441898081849434019382915)
              ·
                refine ⟨153662847122774151029074373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102441898081849434019382915 153662847122774151029074373)
                ·
                  refine ⟨28811783835520153317951445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153662847122774151029074373 28811783835520153317951445)
                  ·
                    refine ⟨675276183645003593389487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28811783835520153317951445 675276183645003593389487)
                    ·
                      rfl

theorem cell23_3945287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_3945287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945287 prefixEnd_3945287 := by exact prefixLift 3945287
  have htrace : WordTrace (prefixWord ++ tailWord_3945287) baseStart_3945287 baseEnd_3945287 := by
    simpa [prefixWord, tailWord_3945287, baseEnd_3945287] using wordTrace_append hprefix tailTrace_3945287
  have hstable : (prefixWord ++ tailWord_3945287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945287).length < 2 ^ (prefixWord ++ tailWord_3945287).sum := by decide
  have hdescent : baseEnd_3945287 < baseStart_3945287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945301 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3945301 : Nat := 118140960795 + 3945301 * 2 ^ 59
def prefixEnd_3945301 : Nat := 4983230072969 + 3 ^ 40 * 3945301 * 2
def baseEnd_3945301 : Nat := 2025835739664173725393397

theorem tailTrace_3945301 : CollatzResearch.WordTrace tailWord_3945301 prefixEnd_3945301 2025835739664173725393397 := by
  unfold tailWord_3945301
  simp only [CollatzResearch.WordTrace]
  refine ⟨143896949079855755611651757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95931299386570503741101171 143896949079855755611651757)
  ·
    refine ⟨53961355904945908354369409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143896949079855755611651757 53961355904945908354369409)
    ·
      refine ⟨40471016928709431265777057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53961355904945908354369409 40471016928709431265777057)
      ·
        refine ⟨30353262696532073449332793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40471016928709431265777057 30353262696532073449332793)
        ·
          refine ⟨22764947022399055086999595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30353262696532073449332793 22764947022399055086999595)
          ·
            refine ⟨34147420533598582630499393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22764947022399055086999595 34147420533598582630499393)
            ·
              refine ⟨25610565400198936972874545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34147420533598582630499393 25610565400198936972874545)
              ·
                refine ⟨19207924050149202729655909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25610565400198936972874545 19207924050149202729655909)
                ·
                  refine ⟨3601485759402975511810483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19207924050149202729655909 3601485759402975511810483)
                  ·
                    refine ⟨5402228639104463267715725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3601485759402975511810483 5402228639104463267715725)
                    ·
                      refine ⟨2025835739664173725393397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5402228639104463267715725 2025835739664173725393397)
                      ·
                        rfl

theorem cell23_3945301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3945301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945301 prefixEnd_3945301 := by exact prefixLift 3945301
  have htrace : WordTrace (prefixWord ++ tailWord_3945301) baseStart_3945301 baseEnd_3945301 := by
    simpa [prefixWord, tailWord_3945301, baseEnd_3945301] using wordTrace_append hprefix tailTrace_3945301
  have hstable : (prefixWord ++ tailWord_3945301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945301).length < 2 ^ (prefixWord ++ tailWord_3945301).sum := by decide
  have hdescent : baseEnd_3945301 < baseStart_3945301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945441 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 3, 4]
def baseStart_3945441 : Nat := 118140960795 + 3945441 * 2 ^ 59
def prefixEnd_3945441 : Nat := 4983230072969 + 3 ^ 40 * 3945441 * 2
def baseEnd_3945441 : Nat := 675302542318601059214251

theorem tailTrace_3945441 : CollatzResearch.WordTrace tailWord_3945441 prefixEnd_3945441 675302542318601059214251 := by
  unfold tailWord_3945441
  simp only [CollatzResearch.WordTrace]
  refine ⟨143902055299348559521748177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95934703532899039681165451 143902055299348559521748177)
  ·
    refine ⟨107926541474511419641311133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143902055299348559521748177 107926541474511419641311133)
    ·
      refine ⟨40472453052941782365491675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107926541474511419641311133 40472453052941782365491675)
      ·
        refine ⟨60708679579412673548237513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40472453052941782365491675 60708679579412673548237513)
        ·
          refine ⟨45531509684559505161178135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60708679579412673548237513 45531509684559505161178135)
          ·
            refine ⟨68297264526839257741767203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45531509684559505161178135 68297264526839257741767203)
            ·
              refine ⟨102445896790258886612650805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68297264526839257741767203 102445896790258886612650805)
              ·
                refine ⟨9604302824086770619936013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102445896790258886612650805 9604302824086770619936013)
                ·
                  refine ⟨3601613559032538982476005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9604302824086770619936013 3601613559032538982476005)
                  ·
                    refine ⟨675302542318601059214251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3601613559032538982476005 675302542318601059214251)
                    ·
                      rfl

theorem cell23_3945441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_3945441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945441 prefixEnd_3945441 := by exact prefixLift 3945441
  have htrace : WordTrace (prefixWord ++ tailWord_3945441) baseStart_3945441 baseEnd_3945441 := by
    simpa [prefixWord, tailWord_3945441, baseEnd_3945441] using wordTrace_append hprefix tailTrace_3945441
  have hstable : (prefixWord ++ tailWord_3945441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945441).length < 2 ^ (prefixWord ++ tailWord_3945441).sum := by decide
  have hdescent : baseEnd_3945441 < baseStart_3945441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945444 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3945444 : Nat := 118140960795 + 3945444 * 2 ^ 59
def prefixEnd_3945444 : Nat := 4983230072969 + 3 ^ 40 * 3945444 * 2
def baseEnd_3945444 : Nat := 2025909167397766665905239

theorem tailTrace_3945444 : CollatzResearch.WordTrace tailWord_3945444 prefixEnd_3945444 2025909167397766665905239 := by
  unfold tailWord_3945444
  simp only [CollatzResearch.WordTrace]
  refine ⟨71951082359168845517053693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95934776478891794022738257 71951082359168845517053693)
  ·
    refine ⟨26981655884688317068895135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71951082359168845517053693 26981655884688317068895135)
    ·
      refine ⟨40472483827032475603342703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26981655884688317068895135 40472483827032475603342703)
      ·
        refine ⟨60708725740548713405014055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40472483827032475603342703 60708725740548713405014055)
        ·
          refine ⟨91063088610823070107521083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60708725740548713405014055 91063088610823070107521083)
          ·
            refine ⟨136594632916234605161281625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91063088610823070107521083 136594632916234605161281625)
            ·
              refine ⟨102445974687175953870961219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136594632916234605161281625 102445974687175953870961219)
              ·
                refine ⟨153668962030763930806441829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102445974687175953870961219 153668962030763930806441829)
                ·
                  refine ⟨28812930380768237026207843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153668962030763930806441829 28812930380768237026207843)
                  ·
                    refine ⟨43219395571152355539311765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28812930380768237026207843 43219395571152355539311765)
                    ·
                      refine ⟨2025909167397766665905239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43219395571152355539311765 2025909167397766665905239)
                      ·
                        rfl

theorem cell23_3945444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3945444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945444 prefixEnd_3945444 := by exact prefixLift 3945444
  have htrace : WordTrace (prefixWord ++ tailWord_3945444) baseStart_3945444 baseEnd_3945444 := by
    simpa [prefixWord, tailWord_3945444, baseEnd_3945444] using wordTrace_append hprefix tailTrace_3945444
  have hstable : (prefixWord ++ tailWord_3945444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945444).length < 2 ^ (prefixWord ++ tailWord_3945444).sum := by decide
  have hdescent : baseEnd_3945444 < baseStart_3945444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945468 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_3945468 : Nat := 118140960795 + 3945468 * 2 ^ 59
def prefixEnd_3945468 : Nat := 4983230072969 + 3 ^ 40 * 3945468 * 2
def baseEnd_3945468 : Nat := 2025921490933474572005129

theorem tailTrace_3945468 : CollatzResearch.WordTrace tailWord_3945468 prefixEnd_3945468 2025921490933474572005129 := by
  unfold tailWord_3945468
  simp only [CollatzResearch.WordTrace]
  refine ⟨71951520035125371566490529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95935360046833828755320705 71951520035125371566490529)
  ·
    refine ⟨53963640026344028674867897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71951520035125371566490529 53963640026344028674867897)
    ·
      refine ⟨40472730019758021506150923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53963640026344028674867897 40472730019758021506150923)
      ·
        refine ⟨60709095029637032259226385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40472730019758021506150923 60709095029637032259226385)
        ·
          refine ⟨45531821272227774194419789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60709095029637032259226385 45531821272227774194419789)
          ·
            refine ⟨17074432977085415322907421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45531821272227774194419789 17074432977085415322907421)
            ·
              refine ⟨6402912366407030746090283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17074432977085415322907421 6402912366407030746090283)
              ·
                refine ⟨9604368549610546119135425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6402912366407030746090283 9604368549610546119135425)
                ·
                  refine ⟨7203276412207909589351569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9604368549610546119135425 7203276412207909589351569)
                  ·
                    refine ⟨5402457309155932192013677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7203276412207909589351569 5402457309155932192013677)
                    ·
                      refine ⟨2025921490933474572005129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5402457309155932192013677 2025921490933474572005129)
                      ·
                        rfl

theorem cell23_3945468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_3945468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945468 prefixEnd_3945468 := by exact prefixLift 3945468
  have htrace : WordTrace (prefixWord ++ tailWord_3945468) baseStart_3945468 baseEnd_3945468 := by
    simpa [prefixWord, tailWord_3945468, baseEnd_3945468] using wordTrace_append hprefix tailTrace_3945468
  have hstable : (prefixWord ++ tailWord_3945468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945468).length < 2 ^ (prefixWord ++ tailWord_3945468).sum := by decide
  have hdescent : baseEnd_3945468 < baseStart_3945468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945532 : List Nat := [2, 2, 2, 2, 2, 2, 3, 3, 1, 1, 3]
def baseStart_3945532 : Nat := 118140960795 + 3945532 * 2 ^ 59
def prefixEnd_3945532 : Nat := 4983230072969 + 3 ^ 40 * 3945532 * 2
def baseEnd_3945532 : Nat := 2025954353695362321604835

theorem tailTrace_3945532 : CollatzResearch.WordTrace tailWord_3945532 prefixEnd_3945532 2025954353695362321604835 := by
  unfold tailWord_3945532
  simp only [CollatzResearch.WordTrace]
  refine ⟨71952687171009441031655425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95936916228012588042207233 71952687171009441031655425)
  ·
    refine ⟨53964515378257080773741569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71952687171009441031655425 53964515378257080773741569)
    ·
      refine ⟨40473386533692810580306177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53964515378257080773741569 40473386533692810580306177)
      ·
        refine ⟨30355039900269607935229633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40473386533692810580306177 30355039900269607935229633)
        ·
          refine ⟨22766279925202205951422225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30355039900269607935229633 22766279925202205951422225)
          ·
            refine ⟨17074709943901654463566669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22766279925202205951422225 17074709943901654463566669)
            ·
              refine ⟨6403016228963120423837501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17074709943901654463566669 6403016228963120423837501)
              ·
                refine ⟨2401131085861170158939063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6403016228963120423837501 2401131085861170158939063)
                ·
                  refine ⟨3601696628791755238408595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401131085861170158939063 3601696628791755238408595)
                  ·
                    refine ⟨5402544943187632857612893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3601696628791755238408595 5402544943187632857612893)
                    ·
                      refine ⟨2025954353695362321604835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5402544943187632857612893 2025954353695362321604835)
                      ·
                        rfl

theorem cell23_3945532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_3945532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945532 prefixEnd_3945532 := by exact prefixLift 3945532
  have htrace : WordTrace (prefixWord ++ tailWord_3945532) baseStart_3945532 baseEnd_3945532 := by
    simpa [prefixWord, tailWord_3945532, baseEnd_3945532] using wordTrace_append hprefix tailTrace_3945532
  have hstable : (prefixWord ++ tailWord_3945532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945532).length < 2 ^ (prefixWord ++ tailWord_3945532).sum := by decide
  have hdescent : baseEnd_3945532 < baseStart_3945532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945541 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_3945541 : Nat := 118140960795 + 3945541 * 2 ^ 59
def prefixEnd_3945541 : Nat := 4983230072969 + 3 ^ 40 * 3945541 * 2
def baseEnd_3945541 : Nat := 2025958975021252786392293

theorem tailTrace_3945541 : CollatzResearch.WordTrace tailWord_3945541 prefixEnd_3945541 2025958975021252786392293 := by
  unfold tailWord_3945541
  simp only [CollatzResearch.WordTrace]
  refine ⟨143905702598986276600388477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95937135065990851066925651 143905702598986276600388477)
  ·
    refine ⟨53964638474619853725145679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143905702598986276600388477 53964638474619853725145679)
    ·
      refine ⟨80946957711929780587718519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53964638474619853725145679 80946957711929780587718519)
      ·
        refine ⟨121420436567894670881577779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80946957711929780587718519 121420436567894670881577779)
        ·
          refine ⟨182130654851842006322366669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121420436567894670881577779 182130654851842006322366669)
          ·
            refine ⟨68298995569440752370887501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182130654851842006322366669 68298995569440752370887501)
            ·
              refine ⟨25612123338540282139082813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68298995569440752370887501 25612123338540282139082813)
              ·
                refine ⟨9604546251952605802156055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25612123338540282139082813 9604546251952605802156055)
                ·
                  refine ⟨14406819377928908703234083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9604546251952605802156055 14406819377928908703234083)
                  ·
                    refine ⟨21610229066893363054851125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14406819377928908703234083 21610229066893363054851125)
                    ·
                      refine ⟨2025958975021252786392293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21610229066893363054851125 2025958975021252786392293)
                      ·
                        rfl

theorem cell23_3945541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_3945541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945541 prefixEnd_3945541 := by exact prefixLift 3945541
  have htrace : WordTrace (prefixWord ++ tailWord_3945541) baseStart_3945541 baseEnd_3945541 := by
    simpa [prefixWord, tailWord_3945541, baseEnd_3945541] using wordTrace_append hprefix tailTrace_3945541
  have hstable : (prefixWord ++ tailWord_3945541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945541).length < 2 ^ (prefixWord ++ tailWord_3945541).sum := by decide
  have hdescent : baseEnd_3945541 < baseStart_3945541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945542 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_3945542 : Nat := 118140960795 + 3945542 * 2 ^ 59
def prefixEnd_3945542 : Nat := 4983230072969 + 3 ^ 40 * 3945542 * 2
def baseEnd_3945542 : Nat := 2025959488501907282479789

theorem tailTrace_3945542 : CollatzResearch.WordTrace tailWord_3945542 prefixEnd_3945542 2025959488501907282479789 := by
  unfold tailWord_3945542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4497054345999457930349215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95937159381321769180783253 4497054345999457930349215)
  ·
    refine ⟨6745581518999186895523823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4497054345999457930349215 6745581518999186895523823)
    ·
      refine ⟨10118372278498780343285735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6745581518999186895523823 10118372278498780343285735)
      ·
        refine ⟨15177558417748170514928603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10118372278498780343285735 15177558417748170514928603)
        ·
          refine ⟨22766337626622255772392905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15177558417748170514928603 22766337626622255772392905)
          ·
            refine ⟨17074753219966691829294679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22766337626622255772392905 17074753219966691829294679)
            ·
              refine ⟨25612129829950037743942019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17074753219966691829294679 25612129829950037743942019)
              ·
                refine ⟨38418194744925056615913029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25612129829950037743942019 38418194744925056615913029)
                ·
                  refine ⟨7203411514673448115483693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38418194744925056615913029 7203411514673448115483693)
                  ·
                    refine ⟨2701279318002543043306385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7203411514673448115483693 2701279318002543043306385)
                    ·
                      refine ⟨2025959488501907282479789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2701279318002543043306385 2025959488501907282479789)
                      ·
                        rfl

theorem cell23_3945542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_3945542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945542 prefixEnd_3945542 := by exact prefixLift 3945542
  have htrace : WordTrace (prefixWord ++ tailWord_3945542) baseStart_3945542 baseEnd_3945542 := by
    simpa [prefixWord, tailWord_3945542, baseEnd_3945542] using wordTrace_append hprefix tailTrace_3945542
  have hstable : (prefixWord ++ tailWord_3945542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945542).length < 2 ^ (prefixWord ++ tailWord_3945542).sum := by decide
  have hdescent : baseEnd_3945542 < baseStart_3945542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945548 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_3945548 : Nat := 118140960795 + 3945548 * 2 ^ 59
def prefixEnd_3945548 : Nat := 4983230072969 + 3 ^ 40 * 3945548 * 2
def baseEnd_3945548 : Nat := 675320856461944753001587

theorem tailTrace_3945548 : CollatzResearch.WordTrace tailWord_3945548 prefixEnd_3945548 675320856461944753001587 := by
  unfold tailWord_3945548
  simp only [CollatzResearch.WordTrace]
  refine ⟨71952978954980458397946649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95937305273307277863928865 71952978954980458397946649)
  ·
    refine ⟨53964734216235343798459987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71952978954980458397946649 53964734216235343798459987)
    ·
      refine ⟨80947101324353015697689981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53964734216235343798459987 80947101324353015697689981)
      ·
        refine ⟨30355162996632380886633743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80947101324353015697689981 30355162996632380886633743)
        ·
          refine ⟨45532744494948571329950615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30355162996632380886633743 45532744494948571329950615)
          ·
            refine ⟨68299116742422856994925923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45532744494948571329950615 68299116742422856994925923)
            ·
              refine ⟨102448675113634285492388885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68299116742422856994925923 102448675113634285492388885)
              ·
                refine ⟨4802281645951607132455729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102448675113634285492388885 4802281645951607132455729)
                ·
                  refine ⟨3601711234463705349341797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4802281645951607132455729 3601711234463705349341797)
                  ·
                    refine ⟨675320856461944753001587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3601711234463705349341797 675320856461944753001587)
                    ·
                      rfl

theorem cell23_3945548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_3945548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945548 prefixEnd_3945548 := by exact prefixLift 3945548
  have htrace : WordTrace (prefixWord ++ tailWord_3945548) baseStart_3945548 baseEnd_3945548 := by
    simpa [prefixWord, tailWord_3945548, baseEnd_3945548] using wordTrace_append hprefix tailTrace_3945548
  have hstable : (prefixWord ++ tailWord_3945548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945548).length < 2 ^ (prefixWord ++ tailWord_3945548).sum := by decide
  have hdescent : baseEnd_3945548 < baseStart_3945548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945575 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_3945575 : Nat := 118140960795 + 3945575 * 2 ^ 59
def prefixEnd_3945575 : Nat := 4983230072969 + 3 ^ 40 * 3945575 * 2
def baseEnd_3945575 : Nat := 2025976433363505653367137

theorem tailTrace_3945575 : CollatzResearch.WordTrace tailWord_3945575 prefixEnd_3945575 2025976433363505653367137 := by
  unfold tailWord_3945575
  simp only [CollatzResearch.WordTrace]
  refine ⟨143906942680863100407126179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95937961787242066938084119 143906942680863100407126179)
  ·
    refine ⟨215860414021294650610689269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143906942680863100407126179 215860414021294650610689269)
    ·
      refine ⟨20236913814496373494752119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215860414021294650610689269 20236913814496373494752119)
      ·
        refine ⟨30355370721744560242128179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20236913814496373494752119 30355370721744560242128179)
        ·
          refine ⟨45533056082616840363192269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30355370721744560242128179 45533056082616840363192269)
          ·
            refine ⟨17074896030981315136197101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45533056082616840363192269 17074896030981315136197101)
            ·
              refine ⟨6403086011617993176073913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17074896030981315136197101 6403086011617993176073913)
              ·
                refine ⟨4802314508713494882055435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6403086011617993176073913 4802314508713494882055435)
                ·
                  refine ⟨7203471763070242323083153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802314508713494882055435 7203471763070242323083153)
                  ·
                    refine ⟨5402603822302681742312365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7203471763070242323083153 5402603822302681742312365)
                    ·
                      refine ⟨2025976433363505653367137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5402603822302681742312365 2025976433363505653367137)
                      ·
                        rfl

theorem cell23_3945575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_3945575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945575 prefixEnd_3945575 := by exact prefixLift 3945575
  have htrace : WordTrace (prefixWord ++ tailWord_3945575) baseStart_3945575 baseEnd_3945575 := by
    simpa [prefixWord, tailWord_3945575, baseEnd_3945575] using wordTrace_append hprefix tailTrace_3945575
  have hstable : (prefixWord ++ tailWord_3945575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945575).length < 2 ^ (prefixWord ++ tailWord_3945575).sum := by decide
  have hdescent : baseEnd_3945575 < baseStart_3945575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945589 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3945589 : Nat := 118140960795 + 3945589 * 2 ^ 59
def prefixEnd_3945589 : Nat := 4983230072969 + 3 ^ 40 * 3945589 * 2
def baseEnd_3945589 : Nat := 2025983622092668598592073

theorem tailTrace_3945589 : CollatzResearch.WordTrace tailWord_3945589 prefixEnd_3945589 2025983622092668598592073 := by
  unfold tailWord_3945589
  simp only [CollatzResearch.WordTrace]
  refine ⟨143907453302812380798135821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95938302201874920532090547 143907453302812380798135821)
  ·
    refine ⟨53965294988554642799300933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143907453302812380798135821 53965294988554642799300933)
    ·
      refine ⟨10118492810353995524868925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53965294988554642799300933 10118492810353995524868925)
      ·
        refine ⟨3794434803882748321825847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10118492810353995524868925 3794434803882748321825847)
        ·
          refine ⟨5691652205824122482738771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794434803882748321825847 5691652205824122482738771)
          ·
            refine ⟨8537478308736183724108157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691652205824122482738771 8537478308736183724108157)
            ·
              refine ⟨3201554365776068896540559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8537478308736183724108157 3201554365776068896540559)
              ·
                refine ⟨4802331548664103344810839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201554365776068896540559 4802331548664103344810839)
                ·
                  refine ⟨7203497322996155017216259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802331548664103344810839 7203497322996155017216259)
                  ·
                    refine ⟨10805245984494232525824389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7203497322996155017216259 10805245984494232525824389)
                    ·
                      refine ⟨2025983622092668598592073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10805245984494232525824389 2025983622092668598592073)
                      ·
                        rfl

theorem cell23_3945589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3945589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945589 prefixEnd_3945589 := by exact prefixLift 3945589
  have htrace : WordTrace (prefixWord ++ tailWord_3945589) baseStart_3945589 baseEnd_3945589 := by
    simpa [prefixWord, tailWord_3945589, baseEnd_3945589] using wordTrace_append hprefix tailTrace_3945589
  have hstable : (prefixWord ++ tailWord_3945589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945589).length < 2 ^ (prefixWord ++ tailWord_3945589).sum := by decide
  have hdescent : baseEnd_3945589 < baseStart_3945589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945649 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 1, 3, 2]
def baseStart_3945649 : Nat := 118140960795 + 3945649 * 2 ^ 59
def prefixEnd_3945649 : Nat := 4983230072969 + 3 ^ 40 * 3945649 * 2
def baseEnd_3945649 : Nat := 2026014430931938363841797

theorem tailTrace_3945649 : CollatzResearch.WordTrace tailWord_3945649 prefixEnd_3945649 2026014430931938363841797 := by
  unfold tailWord_3945649
  simp only [CollatzResearch.WordTrace]
  refine ⟨143909641682595011045320001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95939761121730007363546667 143909641682595011045320001)
  ·
    refine ⟨107932231261946258283990001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143909641682595011045320001 107932231261946258283990001)
    ·
      refine ⟨80949173446459693712992501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107932231261946258283990001 80949173446459693712992501)
      ·
        refine ⟨7588985010605596285593047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80949173446459693712992501 7588985010605596285593047)
        ·
          refine ⟨11383477515908394428389571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588985010605596285593047 11383477515908394428389571)
          ·
            refine ⟨17075216273862591642584357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11383477515908394428389571 17075216273862591642584357)
            ·
              refine ⟨3201603051349235932984567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17075216273862591642584357 3201603051349235932984567)
              ·
                refine ⟨4802404577023853899476851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201603051349235932984567 4802404577023853899476851)
                ·
                  refine ⟨7203606865535780849215277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802404577023853899476851 7203606865535780849215277)
                  ·
                    refine ⟨2701352574575917818455729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7203606865535780849215277 2701352574575917818455729)
                    ·
                      refine ⟨2026014430931938363841797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2701352574575917818455729 2026014430931938363841797)
                      ·
                        rfl

theorem cell23_3945649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_3945649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945649 prefixEnd_3945649 := by exact prefixLift 3945649
  have htrace : WordTrace (prefixWord ++ tailWord_3945649) baseStart_3945649 baseEnd_3945649 := by
    simpa [prefixWord, tailWord_3945649, baseEnd_3945649] using wordTrace_append hprefix tailTrace_3945649
  have hstable : (prefixWord ++ tailWord_3945649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945649).length < 2 ^ (prefixWord ++ tailWord_3945649).sum := by decide
  have hdescent : baseEnd_3945649 < baseStart_3945649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945730 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_3945730 : Nat := 118140960795 + 3945730 * 2 ^ 59
def prefixEnd_3945730 : Nat := 4983230072969 + 3 ^ 40 * 3945730 * 2
def baseEnd_3945730 : Nat := 2026056022864952546928925

theorem tailTrace_3945730 : CollatzResearch.WordTrace tailWord_3945730 prefixEnd_3945730 2026056022864952546928925 := by
  unfold tailWord_3945730
  simp only [CollatzResearch.WordTrace]
  refine ⟨35978148998825390469754661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95941730663534374586012429 35978148998825390469754661)
  ·
    refine ⟨6745902937279760713078999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35978148998825390469754661 6745902937279760713078999)
    ·
      refine ⟨10118854405919641069618499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6745902937279760713078999 10118854405919641069618499)
      ·
        refine ⟨15178281608879461604427749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10118854405919641069618499 15178281608879461604427749)
        ·
          refine ⟨2845927801664899050830203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15178281608879461604427749 2845927801664899050830203)
          ·
            refine ⟨4268891702497348576245305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845927801664899050830203 4268891702497348576245305)
            ·
              refine ⟨3201668776873011432183979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4268891702497348576245305 3201668776873011432183979)
              ·
                refine ⟨4802503165309517148275969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201668776873011432183979 4802503165309517148275969)
                ·
                  refine ⟨3601877373982137861206977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4802503165309517148275969 3601877373982137861206977)
                  ·
                    refine ⟨2701408030486603395905233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3601877373982137861206977 2701408030486603395905233)
                    ·
                      refine ⟨2026056022864952546928925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2701408030486603395905233 2026056022864952546928925)
                      ·
                        rfl

theorem cell23_3945730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_3945730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945730 prefixEnd_3945730 := by exact prefixLift 3945730
  have htrace : WordTrace (prefixWord ++ tailWord_3945730) baseStart_3945730 baseEnd_3945730 := by
    simpa [prefixWord, tailWord_3945730, baseEnd_3945730] using wordTrace_append hprefix tailTrace_3945730
  have hstable : (prefixWord ++ tailWord_3945730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945730).length < 2 ^ (prefixWord ++ tailWord_3945730).sum := by decide
  have hdescent : baseEnd_3945730 < baseStart_3945730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945779 : List Nat := [1, 1, 1, 2, 5, 2, 4, 2, 1, 4]
def baseStart_3945779 : Nat := 118140960795 + 3945779 * 2 ^ 59
def prefixEnd_3945779 : Nat := 4983230072969 + 3 ^ 40 * 3945779 * 2
def baseEnd_3945779 : Nat := 675360394472340951738733

theorem tailTrace_3945779 : CollatzResearch.WordTrace tailWord_3945779 prefixEnd_3945779 675360394472340951738733 := by
  unfold tailWord_3945779
  simp only [CollatzResearch.WordTrace]
  refine ⟨143914383172124043247552391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95942922114749362165034927 143914383172124043247552391)
  ·
    refine ⟨215871574758186064871328587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143914383172124043247552391 215871574758186064871328587)
    ·
      refine ⟨323807362137279097306992881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215871574758186064871328587 323807362137279097306992881)
      ·
        refine ⟨242855521602959322980244661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323807362137279097306992881 242855521602959322980244661)
        ·
          refine ⟨22767705150277436529397937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242855521602959322980244661 22767705150277436529397937)
          ·
            refine ⟨17075778862708077397048453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22767705150277436529397937 17075778862708077397048453)
            ·
              refine ⟨3201708536757764511946585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17075778862708077397048453 3201708536757764511946585)
              ·
                refine ⟨2401281402568323383959939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201708536757764511946585 2401281402568323383959939)
                ·
                  refine ⟨3601922103852485075939909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401281402568323383959939 3601922103852485075939909)
                  ·
                    refine ⟨675360394472340951738733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3601922103852485075939909 675360394472340951738733)
                    ·
                      rfl

theorem cell23_3945779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 4].length) (baseStart_3945779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945779 prefixEnd_3945779 := by exact prefixLift 3945779
  have htrace : WordTrace (prefixWord ++ tailWord_3945779) baseStart_3945779 baseEnd_3945779 := by
    simpa [prefixWord, tailWord_3945779, baseEnd_3945779] using wordTrace_append hprefix tailTrace_3945779
  have hstable : (prefixWord ++ tailWord_3945779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945779).length < 2 ^ (prefixWord ++ tailWord_3945779).sum := by decide
  have hdescent : baseEnd_3945779 < baseStart_3945779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945795 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 1, 5, 2]
def baseStart_3945795 : Nat := 118140960795 + 3945795 * 2 ^ 59
def prefixEnd_3945795 : Nat := 4983230072969 + 3 ^ 40 * 3945795 * 2
def baseEnd_3945795 : Nat := 2026089399107494792616125

theorem tailTrace_3945795 : CollatzResearch.WordTrace tailWord_3945795 prefixEnd_3945795 2026089399107494792616125 := by
  unfold tailWord_3945795
  simp only [CollatzResearch.WordTrace]
  refine ⟨143914966740066077980134839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95943311160044051986756559 143914966740066077980134839)
  ·
    refine ⟨215872450110099116970202259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143914966740066077980134839 215872450110099116970202259)
    ·
      refine ⟨323808675165148675455303389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215872450110099116970202259 323808675165148675455303389)
      ·
        refine ⟨121428253186930753295738771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323808675165148675455303389 121428253186930753295738771)
        ·
          refine ⟨182142379780396129943608157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121428253186930753295738771 182142379780396129943608157)
          ·
            refine ⟨68303392417648548728853059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182142379780396129943608157 68303392417648548728853059)
            ·
              refine ⟨102455088626472823093279589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68303392417648548728853059 102455088626472823093279589)
              ·
                refine ⟨19210329117463654329989923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102455088626472823093279589 19210329117463654329989923)
                ·
                  refine ⟨28815493676195481494984885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19210329117463654329989923 28815493676195481494984885)
                  ·
                    refine ⟨2701452532143326390154833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28815493676195481494984885 2701452532143326390154833)
                    ·
                      refine ⟨2026089399107494792616125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2701452532143326390154833 2026089399107494792616125)
                      ·
                        rfl

theorem cell23_3945795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_3945795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945795 prefixEnd_3945795 := by exact prefixLift 3945795
  have htrace : WordTrace (prefixWord ++ tailWord_3945795) baseStart_3945795 baseEnd_3945795 := by
    simpa [prefixWord, tailWord_3945795, baseEnd_3945795] using wordTrace_append hprefix tailTrace_3945795
  have hstable : (prefixWord ++ tailWord_3945795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945795).length < 2 ^ (prefixWord ++ tailWord_3945795).sum := by decide
  have hdescent : baseEnd_3945795 < baseStart_3945795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945812 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_3945812 : Nat := 118140960795 + 3945812 * 2 ^ 59
def prefixEnd_3945812 : Nat := 4983230072969 + 3 ^ 40 * 3945812 * 2
def baseEnd_3945812 : Nat := 2026098128278621226103547

theorem tailTrace_3945812 : CollatzResearch.WordTrace tailWord_3945812 prefixEnd_3945812 2026098128278621226103547 := by
  unfold tailWord_3945812
  simp only [CollatzResearch.WordTrace]
  refine ⟨71957793390502244941751845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95943724520669659922335793 71957793390502244941751845)
  ·
    refine ⟨13492086260719170926578471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71957793390502244941751845 13492086260719170926578471)
    ·
      refine ⟨20238129391078756389867707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13492086260719170926578471 20238129391078756389867707)
      ·
        refine ⟨30357194086618134584801561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20238129391078756389867707 30357194086618134584801561)
        ·
          refine ⟨22767895564963600938601171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30357194086618134584801561 22767895564963600938601171)
          ·
            refine ⟨34151843347445401407901757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22767895564963600938601171 34151843347445401407901757)
            ·
              refine ⟨12806941255292025527963159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34151843347445401407901757 12806941255292025527963159)
              ·
                refine ⟨19210411882938038291944739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12806941255292025527963159 19210411882938038291944739)
                ·
                  refine ⟨28815617824407057437917109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19210411882938038291944739 28815617824407057437917109)
                  ·
                    refine ⟨2701464171038161634804729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28815617824407057437917109 2701464171038161634804729)
                    ·
                      refine ⟨2026098128278621226103547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2701464171038161634804729 2026098128278621226103547)
                      ·
                        rfl

theorem cell23_3945812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_3945812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945812 prefixEnd_3945812 := by exact prefixLift 3945812
  have htrace : WordTrace (prefixWord ++ tailWord_3945812) baseStart_3945812 baseEnd_3945812 := by
    simpa [prefixWord, tailWord_3945812, baseEnd_3945812] using wordTrace_append hprefix tailTrace_3945812
  have hstable : (prefixWord ++ tailWord_3945812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945812).length < 2 ^ (prefixWord ++ tailWord_3945812).sum := by decide
  have hdescent : baseEnd_3945812 < baseStart_3945812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945825 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_3945825 : Nat := 118140960795 + 3945825 * 2 ^ 59
def prefixEnd_3945825 : Nat := 4983230072969 + 3 ^ 40 * 3945825 * 2
def baseEnd_3945825 : Nat := 2026104803527129675240987

theorem tailTrace_3945825 : CollatzResearch.WordTrace tailWord_3945825 prefixEnd_3945825 2026104803527129675240987 := by
  unfold tailWord_3945825
  simp only [CollatzResearch.WordTrace]
  refine ⟨143916060929957393103726929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95944040619971595402484619 143916060929957393103726929)
  ·
    refine ⟨107937045697468044827795197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143916060929957393103726929 107937045697468044827795197)
    ·
      refine ⟨40476392136550516810423199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107937045697468044827795197 40476392136550516810423199)
      ·
        refine ⟨60714588204825775215634799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40476392136550516810423199 60714588204825775215634799)
        ·
          refine ⟨91071882307238662823452199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60714588204825775215634799 91071882307238662823452199)
          ·
            refine ⟨136607823460857994235178299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91071882307238662823452199 136607823460857994235178299)
            ·
              refine ⟨204911735191286991352767449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136607823460857994235178299 204911735191286991352767449)
              ·
                refine ⟨153683801393465243514575587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204911735191286991352767449 153683801393465243514575587)
                ·
                  refine ⟨230525702090197865271863381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153683801393465243514575587 230525702090197865271863381)
                  ·
                    refine ⟨2701473071369506233654649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 230525702090197865271863381 2701473071369506233654649)
                    ·
                      refine ⟨2026104803527129675240987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2701473071369506233654649 2026104803527129675240987)
                      ·
                        rfl

theorem cell23_3945825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_3945825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945825 prefixEnd_3945825 := by exact prefixLift 3945825
  have htrace : WordTrace (prefixWord ++ tailWord_3945825) baseStart_3945825 baseEnd_3945825 := by
    simpa [prefixWord, tailWord_3945825, baseEnd_3945825] using wordTrace_append hprefix tailTrace_3945825
  have hstable : (prefixWord ++ tailWord_3945825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945825).length < 2 ^ (prefixWord ++ tailWord_3945825).sum := by decide
  have hdescent : baseEnd_3945825 < baseStart_3945825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945859 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 3, 2, 2]
def baseStart_3945859 : Nat := 118140960795 + 3945859 * 2 ^ 59
def prefixEnd_3945859 : Nat := 4983230072969 + 3 ^ 40 * 3945859 * 2
def baseEnd_3945859 : Nat := 2026122261869382542215831

theorem tailTrace_3945859 : CollatzResearch.WordTrace tailWord_3945859 prefixEnd_3945859 2026122261869382542215831 := by
  unfold tailWord_3945859
  simp only [CollatzResearch.WordTrace]
  refine ⟨143917301011834216910464631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95944867341222811273643087 143917301011834216910464631)
  ·
    refine ⟨215875951517751325365696947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143917301011834216910464631 215875951517751325365696947)
    ·
      refine ⟨323813927276626988048545421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215875951517751325365696947 323813927276626988048545421)
      ·
        refine ⟨121430222728735120518204533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323813927276626988048545421 121430222728735120518204533)
        ·
          refine ⟨11384083380818917548581675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121430222728735120518204533 11384083380818917548581675)
          ·
            refine ⟨17076125071228376322872513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11384083380818917548581675 17076125071228376322872513)
            ·
              refine ⟨12807093803421282242154385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17076125071228376322872513 12807093803421282242154385)
              ·
                refine ⟨9605320352565961681615789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12807093803421282242154385 9605320352565961681615789)
                ·
                  refine ⟨3601995132212235630605921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9605320352565961681615789 3601995132212235630605921)
                  ·
                    refine ⟨2701496349159176722954441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3601995132212235630605921 2701496349159176722954441)
                    ·
                      refine ⟨2026122261869382542215831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2701496349159176722954441 2026122261869382542215831)
                      ·
                        rfl

theorem cell23_3945859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_3945859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945859 prefixEnd_3945859 := by exact prefixLift 3945859
  have htrace : WordTrace (prefixWord ++ tailWord_3945859) baseStart_3945859 baseEnd_3945859 := by
    simpa [prefixWord, tailWord_3945859, baseEnd_3945859] using wordTrace_append hprefix tailTrace_3945859
  have hstable : (prefixWord ++ tailWord_3945859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945859).length < 2 ^ (prefixWord ++ tailWord_3945859).sum := by decide
  have hdescent : baseEnd_3945859 < baseStart_3945859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945865 : List Nat := [1, 2, 1, 1, 7, 1, 1, 9]
def baseStart_3945865 : Nat := 118140960795 + 3945865 * 2 ^ 59
def prefixEnd_3945865 : Nat := 4983230072969 + 3 ^ 40 * 3945865 * 2
def baseEnd_3945865 : Nat := 75041679361233685879289

theorem tailTrace_3945865 : CollatzResearch.WordTrace tailWord_3945865 prefixEnd_3945865 75041679361233685879289 := by
  unfold tailWord_3945865
  simp only [CollatzResearch.WordTrace]
  refine ⟨143917519849812479935183049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95945013233208319956788699 143917519849812479935183049)
  ·
    refine ⟨107938139887359359951387287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143917519849812479935183049 107938139887359359951387287)
    ·
      refine ⟨161907209831039039927080931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107938139887359359951387287 161907209831039039927080931)
      ·
        refine ⟨242860814746558559890621397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161907209831039039927080931 242860814746558559890621397)
        ·
          refine ⟨5692050345622466247436439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 242860814746558559890621397 5692050345622466247436439)
          ·
            refine ⟨8538075518433699371154659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692050345622466247436439 8538075518433699371154659)
            ·
              refine ⟨12807113277650549056731989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8538075518433699371154659 12807113277650549056731989)
              ·
                refine ⟨75041679361233685879289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12807113277650549056731989 75041679361233685879289)
                ·
                  rfl

theorem cell23_3945865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 9].length) (baseStart_3945865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945865 prefixEnd_3945865 := by exact prefixLift 3945865
  have htrace : WordTrace (prefixWord ++ tailWord_3945865) baseStart_3945865 baseEnd_3945865 := by
    simpa [prefixWord, tailWord_3945865, baseEnd_3945865] using wordTrace_append hprefix tailTrace_3945865
  have hstable : (prefixWord ++ tailWord_3945865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945865).length < 2 ^ (prefixWord ++ tailWord_3945865).sum := by decide
  have hdescent : baseEnd_3945865 < baseStart_3945865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945870 : List Nat := [4, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3945870 : Nat := 118140960795 + 3945870 * 2 ^ 59
def prefixEnd_3945870 : Nat := 4983230072969 + 3 ^ 40 * 3945870 * 2
def baseEnd_3945870 : Nat := 2026127910156581999178281

theorem tailTrace_3945870 : CollatzResearch.WordTrace tailWord_3945870 prefixEnd_3945870 2026127910156581999178281 := by
  unfold tailWord_3945870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989712776849295723639383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95945134809862910526076709 17989712776849295723639383)
  ·
    refine ⟨26984569165273943585459075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17989712776849295723639383 26984569165273943585459075)
    ·
      refine ⟨40476853747910915378188613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26984569165273943585459075 40476853747910915378188613)
      ·
        refine ⟨7589410077733296633410365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40476853747910915378188613 7589410077733296633410365)
        ·
          refine ⟨2846028779149986237528887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7589410077733296633410365 2846028779149986237528887)
          ·
            refine ⟨4269043168724979356293331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846028779149986237528887 4269043168724979356293331)
            ·
              refine ⟨6403564753087469034439997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269043168724979356293331 6403564753087469034439997)
              ·
                refine ⟨2401336782407800887914999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6403564753087469034439997 2401336782407800887914999)
                ·
                  refine ⟨3602005173611701331872499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401336782407800887914999 3602005173611701331872499)
                  ·
                    refine ⟨5403007760417551997808749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3602005173611701331872499 5403007760417551997808749)
                    ·
                      refine ⟨2026127910156581999178281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5403007760417551997808749 2026127910156581999178281)
                      ·
                        rfl

theorem cell23_3945870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3945870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945870 prefixEnd_3945870 := by exact prefixLift 3945870
  have htrace : WordTrace (prefixWord ++ tailWord_3945870) baseStart_3945870 baseEnd_3945870 := by
    simpa [prefixWord, tailWord_3945870, baseEnd_3945870] using wordTrace_append hprefix tailTrace_3945870
  have hstable : (prefixWord ++ tailWord_3945870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945870).length < 2 ^ (prefixWord ++ tailWord_3945870).sum := by decide
  have hdescent : baseEnd_3945870 < baseStart_3945870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945895 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3945895 : Nat := 118140960795 + 3945895 * 2 ^ 59
def prefixEnd_3945895 : Nat := 4983230072969 + 3 ^ 40 * 3945895 * 2
def baseEnd_3945895 : Nat := 675380249057648133788555

theorem tailTrace_3945895 : CollatzResearch.WordTrace tailWord_3945895 prefixEnd_3945895 675380249057648133788555 := by
  unfold tailWord_3945895
  simp only [CollatzResearch.WordTrace]
  refine ⟨143918614039703795058775139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95945742693135863372516759 143918614039703795058775139)
  ·
    refine ⟨215877921059555692588162709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143918614039703795058775139 215877921059555692588162709)
    ·
      refine ⟨10119277549666673090070127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215877921059555692588162709 10119277549666673090070127)
      ·
        refine ⟨15178916324500009635105191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10119277549666673090070127 15178916324500009635105191)
        ·
          refine ⟨22768374486750014452657787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15178916324500009635105191 22768374486750014452657787)
          ·
            refine ⟨34152561730125021678986681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22768374486750014452657787 34152561730125021678986681)
            ·
              refine ⟨25614421297593766259240011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34152561730125021678986681 25614421297593766259240011)
              ·
                refine ⟨38421631946390649388860017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25614421297593766259240011 38421631946390649388860017)
                ·
                  refine ⟨28816223959792987041645013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38421631946390649388860017 28816223959792987041645013)
                  ·
                    refine ⟨675380249057648133788555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28816223959792987041645013 675380249057648133788555)
                    ·
                      rfl

theorem cell23_3945895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3945895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945895 prefixEnd_3945895 := by exact prefixLift 3945895
  have htrace : WordTrace (prefixWord ++ tailWord_3945895) baseStart_3945895 baseEnd_3945895 := by
    simpa [prefixWord, tailWord_3945895, baseEnd_3945895] using wordTrace_append hprefix tailTrace_3945895
  have hstable : (prefixWord ++ tailWord_3945895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945895).length < 2 ^ (prefixWord ++ tailWord_3945895).sum := by decide
  have hdescent : baseEnd_3945895 < baseStart_3945895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945935 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_3945935 : Nat := 118140960795 + 3945935 * 2 ^ 59
def prefixEnd_3945935 : Nat := 4983230072969 + 3 ^ 40 * 3945935 * 2
def baseEnd_3945935 : Nat := 2026161286399124244865481

theorem tailTrace_3945935 : CollatzResearch.WordTrace tailWord_3945935 prefixEnd_3945935 2026161286399124244865481 := by
  unfold tailWord_3945935
  simp only [CollatzResearch.WordTrace]
  refine ⟨143920072959558881890231259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95946715306372587926820839 143920072959558881890231259)
  ·
    refine ⟨215880109439338322835346889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143920072959558881890231259 215880109439338322835346889)
    ·
      refine ⟨161910082079503742126510167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215880109439338322835346889 161910082079503742126510167)
      ·
        refine ⟨242865123119255613189765251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161910082079503742126510167 242865123119255613189765251)
        ·
          refine ⟨364297684678883419784647877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242865123119255613189765251 364297684678883419784647877)
          ·
            refine ⟨68305815877290641209621477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364297684678883419784647877 68305815877290641209621477)
            ·
              refine ⟨12807340476991995226804027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68305815877290641209621477 12807340476991995226804027)
              ·
                refine ⟨19211010715487992840206041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12807340476991995226804027 19211010715487992840206041)
                ·
                  refine ⟨14408258036615994630154531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19211010715487992840206041 14408258036615994630154531)
                  ·
                    refine ⟨21612387054923991945231797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14408258036615994630154531 21612387054923991945231797)
                    ·
                      refine ⟨2026161286399124244865481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21612387054923991945231797 2026161286399124244865481)
                      ·
                        rfl

theorem cell23_3945935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_3945935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945935 prefixEnd_3945935 := by exact prefixLift 3945935
  have htrace : WordTrace (prefixWord ++ tailWord_3945935) baseStart_3945935 baseEnd_3945935 := by
    simpa [prefixWord, tailWord_3945935, baseEnd_3945935] using wordTrace_append hprefix tailTrace_3945935
  have hstable : (prefixWord ++ tailWord_3945935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945935).length < 2 ^ (prefixWord ++ tailWord_3945935).sum := by decide
  have hdescent : baseEnd_3945935 < baseStart_3945935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3945966 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_3945966 : Nat := 118140960795 + 3945966 * 2 ^ 59
def prefixEnd_3945966 : Nat := 4983230072969 + 3 ^ 40 * 3945966 * 2
def baseEnd_3945966 : Nat := 2026177204299413623577839

theorem tailTrace_3945966 : CollatzResearch.WordTrace tailWord_3945966 prefixEnd_3945966 2026177204299413623577839 := by
  unfold tailWord_3945966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17990150452805821773076219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95947469081631049456406501 17990150452805821773076219)
  ·
    refine ⟨26985225679208732659614329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17990150452805821773076219 26985225679208732659614329)
    ·
      refine ⟨20238919259406549494710747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26985225679208732659614329 20238919259406549494710747)
      ·
        refine ⟨30358378889109824242066121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20238919259406549494710747 30358378889109824242066121)
        ·
          refine ⟨22768784166832368181549591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30358378889109824242066121 22768784166832368181549591)
          ·
            refine ⟨34153176250248552272324387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22768784166832368181549591 34153176250248552272324387)
            ·
              refine ⟨51229764375372828408486581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34153176250248552272324387 51229764375372828408486581)
              ·
                refine ⟨4802790410191202663295617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51229764375372828408486581 4802790410191202663295617)
                ·
                  refine ⟨3602092807643401997471713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4802790410191202663295617 3602092807643401997471713)
                  ·
                    refine ⟨2701569605732551498103785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3602092807643401997471713 2701569605732551498103785)
                    ·
                      refine ⟨2026177204299413623577839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2701569605732551498103785 2026177204299413623577839)
                      ·
                        rfl

theorem cell23_3945966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_3945966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3945966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3945966 prefixEnd_3945966 := by exact prefixLift 3945966
  have htrace : WordTrace (prefixWord ++ tailWord_3945966) baseStart_3945966 baseEnd_3945966 := by
    simpa [prefixWord, tailWord_3945966, baseEnd_3945966] using wordTrace_append hprefix tailTrace_3945966
  have hstable : (prefixWord ++ tailWord_3945966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3945966).length < 2 ^ (prefixWord ++ tailWord_3945966).sum := by decide
  have hdescent : baseEnd_3945966 < baseStart_3945966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3945966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946042 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_3946042 : Nat := 118140960795 + 3946042 * 2 ^ 59
def prefixEnd_3946042 : Nat := 4983230072969 + 3 ^ 40 * 3946042 * 2
def baseEnd_3946042 : Nat := 2026216228829155326227489

theorem tailTrace_3946042 : CollatzResearch.WordTrace tailWord_3946042 prefixEnd_3946042 2026216228829155326227489 := by
  unfold tailWord_3946042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35980993892542809791094095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95949317046780826109584253 35980993892542809791094095)
  ·
    refine ⟨53971490838814214686641143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35980993892542809791094095 53971490838814214686641143)
    ·
      refine ⟨80957236258221322029961715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53971490838814214686641143 80957236258221322029961715)
      ·
        refine ⟨121435854387331983044942573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80957236258221322029961715 121435854387331983044942573)
        ·
          refine ⟨45538445395249493641853465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121435854387331983044942573 45538445395249493641853465)
          ·
            refine ⟨34153834046437120231390099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45538445395249493641853465 34153834046437120231390099)
            ·
              refine ⟨51230751069655680347085149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34153834046437120231390099 51230751069655680347085149)
              ·
                refine ⟨19211531651120880130156931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51230751069655680347085149 19211531651120880130156931)
                ·
                  refine ⟨28817297476681320195235397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19211531651120880130156931 28817297476681320195235397)
                  ·
                    refine ⟨5403243276877747536606637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28817297476681320195235397 5403243276877747536606637)
                    ·
                      refine ⟨2026216228829155326227489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5403243276877747536606637 2026216228829155326227489)
                      ·
                        rfl

theorem cell23_3946042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_3946042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946042 prefixEnd_3946042 := by exact prefixLift 3946042
  have htrace : WordTrace (prefixWord ++ tailWord_3946042) baseStart_3946042 baseEnd_3946042 := by
    simpa [prefixWord, tailWord_3946042, baseEnd_3946042] using wordTrace_append hprefix tailTrace_3946042
  have hstable : (prefixWord ++ tailWord_3946042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946042).length < 2 ^ (prefixWord ++ tailWord_3946042).sum := by decide
  have hdescent : baseEnd_3946042 < baseStart_3946042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946062 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_3946062 : Nat := 118140960795 + 3946062 * 2 ^ 59
def prefixEnd_3946062 : Nat := 4983230072969 + 3 ^ 40 * 3946062 * 2
def baseEnd_3946062 : Nat := 225136277604693916441933

theorem tailTrace_3946062 : CollatzResearch.WordTrace tailWord_3946062 prefixEnd_3946062 225136277604693916441933 := by
  unfold tailWord_3946062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17990588128762347822513055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95949803353399188386736293 17990588128762347822513055)
  ·
    refine ⟨26985882193143521733769583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17990588128762347822513055 26985882193143521733769583)
    ·
      refine ⟨40478823289715282600654375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26985882193143521733769583 40478823289715282600654375)
      ·
        refine ⟨60718234934572923900981563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40478823289715282600654375 60718234934572923900981563)
        ·
          refine ⟨91077352401859385851472345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60718234934572923900981563 91077352401859385851472345)
          ·
            refine ⟨68308014301394539388604259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91077352401859385851472345 68308014301394539388604259)
            ·
              refine ⟨102462021452091809082906389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68308014301394539388604259 102462021452091809082906389)
              ·
                refine ⟨4802907255566803550761237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102462021452091809082906389 4802907255566803550761237)
                ·
                  refine ⟨225136277604693916441933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4802907255566803550761237 225136277604693916441933)
                  ·
                    rfl

theorem cell23_3946062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_3946062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946062 prefixEnd_3946062 := by exact prefixLift 3946062
  have htrace : WordTrace (prefixWord ++ tailWord_3946062) baseStart_3946062 baseEnd_3946062 := by
    simpa [prefixWord, tailWord_3946062, baseEnd_3946062] using wordTrace_append hprefix tailTrace_3946062
  have hstable : (prefixWord ++ tailWord_3946062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946062).length < 2 ^ (prefixWord ++ tailWord_3946062).sum := by decide
  have hdescent : baseEnd_3946062 < baseStart_3946062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946066 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_3946066 : Nat := 118140960795 + 3946066 * 2 ^ 59
def prefixEnd_3946066 : Nat := 4983230072969 + 3 ^ 40 * 3946066 * 2
def baseEnd_3946066 : Nat := 675409517454954410775793

theorem tailTrace_3946066 : CollatzResearch.WordTrace tailWord_3946066 prefixEnd_3946066 675409517454954410775793 := by
  unfold tailWord_3946066
  simp only [CollatzResearch.WordTrace]
  refine ⟨35981212730521072815812513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95949900614722860842166701 35981212730521072815812513)
  ·
    refine ⟨26985909547890804611859385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35981212730521072815812513 26985909547890804611859385)
    ·
      refine ⟨20239432160918103458894539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26985909547890804611859385 20239432160918103458894539)
      ·
        refine ⟨30359148241377155188341809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20239432160918103458894539 30359148241377155188341809)
        ·
          refine ⟨22769361181032866391256357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30359148241377155188341809 22769361181032866391256357)
          ·
            refine ⟨4269255221443662448360567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22769361181032866391256357 4269255221443662448360567)
            ·
              refine ⟨6403882832165493672540851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269255221443662448360567 6403882832165493672540851)
              ·
                refine ⟨9605824248248240508811277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403882832165493672540851 9605824248248240508811277)
                ·
                  refine ⟨3602184093093090190804229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9605824248248240508811277 3602184093093090190804229)
                  ·
                    refine ⟨675409517454954410775793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3602184093093090190804229 675409517454954410775793)
                    ·
                      rfl

theorem cell23_3946066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_3946066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946066 prefixEnd_3946066 := by exact prefixLift 3946066
  have htrace : WordTrace (prefixWord ++ tailWord_3946066) baseStart_3946066 baseEnd_3946066 := by
    simpa [prefixWord, tailWord_3946066, baseEnd_3946066] using wordTrace_append hprefix tailTrace_3946066
  have hstable : (prefixWord ++ tailWord_3946066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946066).length < 2 ^ (prefixWord ++ tailWord_3946066).sum := by decide
  have hdescent : baseEnd_3946066 < baseStart_3946066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946089 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 3]
def baseStart_3946089 : Nat := 118140960795 + 3946089 * 2 ^ 59
def prefixEnd_3946089 : Nat := 4983230072969 + 3 ^ 40 * 3946089 * 2
def baseEnd_3946089 : Nat := 2026240362419916642339773

theorem tailTrace_3946089 : CollatzResearch.WordTrace tailWord_3946089 prefixEnd_3946089 2026240362419916642339773 := by
  unfold tailWord_3946089
  simp only [CollatzResearch.WordTrace]
  refine ⟨143925689801000966191337321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95950459867333977460891547 143925689801000966191337321)
  ·
    refine ⟨107944267350750724643502991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143925689801000966191337321 107944267350750724643502991)
    ·
      refine ⟨161916401026126086965254487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107944267350750724643502991 161916401026126086965254487)
      ·
        refine ⟨242874601539189130447881731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161916401026126086965254487 242874601539189130447881731)
        ·
          refine ⟨364311902308783695671822597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242874601539189130447881731 364311902308783695671822597)
          ·
            refine ⟨68308481682896942938466737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364311902308783695671822597 68308481682896942938466737)
            ·
              refine ⟨51231361262172707203850053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68308481682896942938466737 51231361262172707203850053)
              ·
                refine ⟨9605880236657382600721885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51231361262172707203850053 9605880236657382600721885)
                ·
                  refine ⟨3602205088746518475270707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9605880236657382600721885 3602205088746518475270707)
                  ·
                    refine ⟨5403307633119777712906061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3602205088746518475270707 5403307633119777712906061)
                    ·
                      refine ⟨2026240362419916642339773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5403307633119777712906061 2026240362419916642339773)
                      ·
                        rfl

theorem cell23_3946089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 3].length) (baseStart_3946089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946089 prefixEnd_3946089 := by exact prefixLift 3946089
  have htrace : WordTrace (prefixWord ++ tailWord_3946089) baseStart_3946089 baseEnd_3946089 := by
    simpa [prefixWord, tailWord_3946089, baseEnd_3946089] using wordTrace_append hprefix tailTrace_3946089
  have hstable : (prefixWord ++ tailWord_3946089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946089).length < 2 ^ (prefixWord ++ tailWord_3946089).sum := by decide
  have hdescent : baseEnd_3946089 < baseStart_3946089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946149 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_3946149 : Nat := 118140960795 + 3946149 * 2 ^ 59
def prefixEnd_3946149 : Nat := 4983230072969 + 3 ^ 40 * 3946149 * 2
def baseEnd_3946149 : Nat := 2026271171259186407589497

theorem tailTrace_3946149 : CollatzResearch.WordTrace tailWord_3946149 prefixEnd_3946149 2026271171259186407589497 := by
  unfold tailWord_3946149
  simp only [CollatzResearch.WordTrace]
  refine ⟨143927878180783596438521501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95951918787189064292347667 143927878180783596438521501)
  ·
    refine ⟨53972954317793848664445563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143927878180783596438521501 53972954317793848664445563)
    ·
      refine ⟨80959431476690772996668345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53972954317793848664445563 80959431476690772996668345)
      ·
        refine ⟨60719573607518079747501259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80959431476690772996668345 60719573607518079747501259)
        ·
          refine ⟨91079360411277119621251889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60719573607518079747501259 91079360411277119621251889)
          ·
            refine ⟨68309520308457839715938917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91079360411277119621251889 68309520308457839715938917)
            ·
              refine ⟨12808035057835844946738547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68309520308457839715938917 12808035057835844946738547)
              ·
                refine ⟨19212052586753767420107821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12808035057835844946738547 19212052586753767420107821)
                ·
                  refine ⟨7204519720032662782540433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19212052586753767420107821 7204519720032662782540433)
                  ·
                    refine ⟨5403389790024497086905325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7204519720032662782540433 5403389790024497086905325)
                    ·
                      refine ⟨2026271171259186407589497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5403389790024497086905325 2026271171259186407589497)
                      ·
                        rfl

theorem cell23_3946149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_3946149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946149 prefixEnd_3946149 := by exact prefixLift 3946149
  have htrace : WordTrace (prefixWord ++ tailWord_3946149) baseStart_3946149 baseEnd_3946149 := by
    simpa [prefixWord, tailWord_3946149, baseEnd_3946149] using wordTrace_append hprefix tailTrace_3946149
  have hstable : (prefixWord ++ tailWord_3946149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946149).length < 2 ^ (prefixWord ++ tailWord_3946149).sum := by decide
  have hdescent : baseEnd_3946149 < baseStart_3946149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946180 : List Nat := [2, 3, 3, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_3946180 : Nat := 118140960795 + 3946180 * 2 ^ 59
def prefixEnd_3946180 : Nat := 4983230072969 + 3 ^ 40 * 3946180 * 2
def baseEnd_3946180 : Nat := 2026287089159475786301855

theorem tailTrace_3946180 : CollatzResearch.WordTrace tailWord_3946180 prefixEnd_3946180 2026287089159475786301855 := by
  unfold tailWord_3946180
  simp only [CollatzResearch.WordTrace]
  refine ⟨71964504421835644366449997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95952672562447525821933329 71964504421835644366449997)
  ·
    refine ⟨26986689158188366637418749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71964504421835644366449997 26986689158188366637418749)
    ·
      refine ⟨10120008434320637489032031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26986689158188366637418749 10120008434320637489032031)
      ·
        refine ⟨15180012651480956233548047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10120008434320637489032031 15180012651480956233548047)
        ·
          refine ⟨22770018977221434350322071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15180012651480956233548047 22770018977221434350322071)
          ·
            refine ⟨34155028465832151525483107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22770018977221434350322071 34155028465832151525483107)
            ·
              refine ⟨51232542698748227288224661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34155028465832151525483107 51232542698748227288224661)
              ·
                refine ⟨2401525439003823154135531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51232542698748227288224661 2401525439003823154135531)
                ·
                  refine ⟨3602288158505734731203297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401525439003823154135531 3602288158505734731203297)
                  ·
                    refine ⟨2701716118879301048402473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3602288158505734731203297 2701716118879301048402473)
                    ·
                      refine ⟨2026287089159475786301855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2701716118879301048402473 2026287089159475786301855)
                      ·
                        rfl

theorem cell23_3946180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_3946180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946180 prefixEnd_3946180 := by exact prefixLift 3946180
  have htrace : WordTrace (prefixWord ++ tailWord_3946180) baseStart_3946180 baseEnd_3946180 := by
    simpa [prefixWord, tailWord_3946180, baseEnd_3946180] using wordTrace_append hprefix tailTrace_3946180
  have hstable : (prefixWord ++ tailWord_3946180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946180).length < 2 ^ (prefixWord ++ tailWord_3946180).sum := by decide
  have hdescent : baseEnd_3946180 < baseStart_3946180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946232 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_3946232 : Nat := 118140960795 + 3946232 * 2 ^ 59
def prefixEnd_3946232 : Nat := 4983230072969 + 3 ^ 40 * 3946232 * 2
def baseEnd_3946232 : Nat := 2026313790153509582851615

theorem tailTrace_3946232 : CollatzResearch.WordTrace tailWord_3946232 prefixEnd_3946232 2026313790153509582851615 := by
  unfold tailWord_3946232
  simp only [CollatzResearch.WordTrace]
  refine ⟨71965452719741450806896475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95953936959655267742528633 71965452719741450806896475)
  ·
    refine ⟨107948179079612176210344713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71965452719741450806896475 107948179079612176210344713)
    ·
      refine ⟨80961134309709132157758535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107948179079612176210344713 80961134309709132157758535)
      ·
        refine ⟨121441701464563698236637803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80961134309709132157758535 121441701464563698236637803)
        ·
          refine ⟨182162552196845547354956705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121441701464563698236637803 182162552196845547354956705)
          ·
            refine ⟨136621914147634160516217529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182162552196845547354956705 136621914147634160516217529)
            ·
              refine ⟨102466435610725620387163147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136621914147634160516217529 102466435610725620387163147)
              ·
                refine ⟨153699653416088430580744721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102466435610725620387163147 153699653416088430580744721)
                ·
                  refine ⟨115274740062066322935558541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153699653416088430580744721 115274740062066322935558541)
                  ·
                    refine ⟨43228027523274871100834453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115274740062066322935558541 43228027523274871100834453)
                    ·
                      refine ⟨2026313790153509582851615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43228027523274871100834453 2026313790153509582851615)
                      ·
                        rfl

theorem cell23_3946232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_3946232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946232 prefixEnd_3946232 := by exact prefixLift 3946232
  have htrace : WordTrace (prefixWord ++ tailWord_3946232) baseStart_3946232 baseEnd_3946232 := by
    simpa [prefixWord, tailWord_3946232, baseEnd_3946232] using wordTrace_append hprefix tailTrace_3946232
  have hstable : (prefixWord ++ tailWord_3946232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946232).length < 2 ^ (prefixWord ++ tailWord_3946232).sum := by decide
  have hdescent : baseEnd_3946232 < baseStart_3946232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946247 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3946247 : Nat := 118140960795 + 3946247 * 2 ^ 59
def prefixEnd_3946247 : Nat := 4983230072969 + 3 ^ 40 * 3946247 * 2
def baseEnd_3946247 : Nat := 2026321492363327024164047

theorem tailTrace_3946247 : CollatzResearch.WordTrace tailWord_3946247 prefixEnd_3946247 2026321492363327024164047 := by
  unfold tailWord_3946247
  simp only [CollatzResearch.WordTrace]
  refine ⟨143931452534428559175588995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95954301689619039450392663 143931452534428559175588995)
  ·
    refine ⟨215897178801642838763383493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143931452534428559175588995 215897178801642838763383493)
    ·
      refine ⟨40480721025308032268134405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215897178801642838763383493 40480721025308032268134405)
      ·
        refine ⟨7590135192245256050275201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40480721025308032268134405 7590135192245256050275201)
        ·
          refine ⟨5692601394183942037706401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7590135192245256050275201 5692601394183942037706401)
          ·
            refine ⟨4269451045637956528279801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5692601394183942037706401 4269451045637956528279801)
            ·
              refine ⟨3202088284228467396209851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269451045637956528279801 3202088284228467396209851)
              ·
                refine ⟨4803132426342701094314777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202088284228467396209851 4803132426342701094314777)
                ·
                  refine ⟨3602349319757025820736083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4803132426342701094314777 3602349319757025820736083)
                  ·
                    refine ⟨5403523979635538731104125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3602349319757025820736083 5403523979635538731104125)
                    ·
                      refine ⟨2026321492363327024164047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5403523979635538731104125 2026321492363327024164047)
                      ·
                        rfl

theorem cell23_3946247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3946247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946247 prefixEnd_3946247 := by exact prefixLift 3946247
  have htrace : WordTrace (prefixWord ++ tailWord_3946247) baseStart_3946247 baseEnd_3946247 := by
    simpa [prefixWord, tailWord_3946247, baseEnd_3946247] using wordTrace_append hprefix tailTrace_3946247
  have hstable : (prefixWord ++ tailWord_3946247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946247).length < 2 ^ (prefixWord ++ tailWord_3946247).sum := by decide
  have hdescent : baseEnd_3946247 < baseStart_3946247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946293 : List Nat := [1, 3, 3, 1, 4, 1, 1, 4, 5]
def baseStart_3946293 : Nat := 118140960795 + 3946293 * 2 ^ 59
def prefixEnd_3946293 : Nat := 4983230072969 + 3 ^ 40 * 3946293 * 2
def baseEnd_3946293 : Nat := 225149456941492649354315

theorem tailTrace_3946293 : CollatzResearch.WordTrace tailWord_3946293 prefixEnd_3946293 225149456941492649354315 := by
  unfold tailWord_3946293
  simp only [CollatzResearch.WordTrace]
  refine ⟨143933130292261909031763533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95955420194841272687842355 143933130292261909031763533)
  ·
    refine ⟨53974923859598215886911325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143933130292261909031763533 53974923859598215886911325)
    ·
      refine ⟨20240596447349330957591747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53974923859598215886911325 20240596447349330957591747)
      ·
        refine ⟨30360894671023996436387621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20240596447349330957591747 30360894671023996436387621)
        ·
          refine ⟨5692667750816999331822679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30360894671023996436387621 5692667750816999331822679)
          ·
            refine ⟨8539001626225498997734019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692667750816999331822679 8539001626225498997734019)
            ·
              refine ⟨12808502439338248496601029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8539001626225498997734019 12808502439338248496601029)
              ·
                refine ⟨2401594207375921593112693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12808502439338248496601029 2401594207375921593112693)
                ·
                  refine ⟨225149456941492649354315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2401594207375921593112693 225149456941492649354315)
                  ·
                    rfl

theorem cell23_3946293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_3946293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946293 prefixEnd_3946293 := by exact prefixLift 3946293
  have htrace : WordTrace (prefixWord ++ tailWord_3946293) baseStart_3946293 baseEnd_3946293 := by
    simpa [prefixWord, tailWord_3946293, baseEnd_3946293] using wordTrace_append hprefix tailTrace_3946293
  have hstable : (prefixWord ++ tailWord_3946293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946293).length < 2 ^ (prefixWord ++ tailWord_3946293).sum := by decide
  have hdescent : baseEnd_3946293 < baseStart_3946293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946296 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 2, 5, 2]
def baseStart_3946296 : Nat := 118140960795 + 3946296 * 2 ^ 59
def prefixEnd_3946296 : Nat := 4983230072969 + 3 ^ 40 * 3946296 * 2
def baseEnd_3946296 : Nat := 2026346652915397332451321

theorem tailTrace_3946296 : CollatzResearch.WordTrace tailWord_3946296 prefixEnd_3946296 2026346652915397332451321 := by
  unfold tailWord_3946296
  simp only [CollatzResearch.WordTrace]
  refine ⟨71966619855625520272061371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95955493140834027029415161 71966619855625520272061371)
  ·
    refine ⟨107949929783438280408092057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71966619855625520272061371 107949929783438280408092057)
    ·
      refine ⟨80962447337578710306069043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107949929783438280408092057 80962447337578710306069043)
      ·
        refine ⟨121443671006368065459103565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80962447337578710306069043 121443671006368065459103565)
        ·
          refine ⟨45541376627388024547163837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121443671006368065459103565 45541376627388024547163837)
          ·
            refine ⟨17078016235270509205186439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45541376627388024547163837 17078016235270509205186439)
            ·
              refine ⟨25617024352905763807779659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17078016235270509205186439 25617024352905763807779659)
              ·
                refine ⟨38425536529358645711669489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25617024352905763807779659 38425536529358645711669489)
                ·
                  refine ⟨28819152397018984283752117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38425536529358645711669489 28819152397018984283752117)
                  ·
                    refine ⟨2701795537220529776601761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28819152397018984283752117 2701795537220529776601761)
                    ·
                      refine ⟨2026346652915397332451321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2701795537220529776601761 2026346652915397332451321)
                      ·
                        rfl

theorem cell23_3946296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_3946296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946296 prefixEnd_3946296 := by exact prefixLift 3946296
  have htrace : WordTrace (prefixWord ++ tailWord_3946296) baseStart_3946296 baseEnd_3946296 := by
    simpa [prefixWord, tailWord_3946296, baseEnd_3946296] using wordTrace_append hprefix tailTrace_3946296
  have hstable : (prefixWord ++ tailWord_3946296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946296).length < 2 ^ (prefixWord ++ tailWord_3946296).sum := by decide
  have hdescent : baseEnd_3946296 < baseStart_3946296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946309 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_3946309 : Nat := 118140960795 + 3946309 * 2 ^ 59
def prefixEnd_3946309 : Nat := 4983230072969 + 3 ^ 40 * 3946309 * 2
def baseEnd_3946309 : Nat := 2026353328163905781588761

theorem tailTrace_3946309 : CollatzResearch.WordTrace tailWord_3946309 prefixEnd_3946309 2026353328163905781588761 := by
  unfold tailWord_3946309
  simp only [CollatzResearch.WordTrace]
  refine ⟨143933713860203943764345981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95955809240135962509563987 143933713860203943764345981)
  ·
    refine ⟨53975142697576478911629743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143933713860203943764345981 53975142697576478911629743)
    ·
      refine ⟨80962714046364718367444615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53975142697576478911629743 80962714046364718367444615)
      ·
        refine ⟨121444071069547077551166923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80962714046364718367444615 121444071069547077551166923)
        ·
          refine ⟨182166106604320616326750385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121444071069547077551166923 182166106604320616326750385)
          ·
            refine ⟨136624579953240462245062789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182166106604320616326750385 136624579953240462245062789)
            ·
              refine ⟨25617108741232586670949273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136624579953240462245062789 25617108741232586670949273)
              ·
                refine ⟨19212831555924440003211955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25617108741232586670949273 19212831555924440003211955)
                ·
                  refine ⟨28819247333886660004817933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19212831555924440003211955 28819247333886660004817933)
                  ·
                    refine ⟨10807217750207497501806725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28819247333886660004817933 10807217750207497501806725)
                    ·
                      refine ⟨2026353328163905781588761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10807217750207497501806725 2026353328163905781588761)
                      ·
                        rfl

theorem cell23_3946309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_3946309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946309 prefixEnd_3946309 := by exact prefixLift 3946309
  have htrace : WordTrace (prefixWord ++ tailWord_3946309) baseStart_3946309 baseEnd_3946309 := by
    simpa [prefixWord, tailWord_3946309, baseEnd_3946309] using wordTrace_append hprefix tailTrace_3946309
  have hstable : (prefixWord ++ tailWord_3946309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946309).length < 2 ^ (prefixWord ++ tailWord_3946309).sum := by decide
  have hdescent : baseEnd_3946309 < baseStart_3946309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946353 : List Nat := [1, 2, 2, 2, 1, 3, 1, 6, 1, 4]
def baseStart_3946353 : Nat := 118140960795 + 3946353 * 2 ^ 59
def prefixEnd_3946353 : Nat := 4983230072969 + 3 ^ 40 * 3946353 * 2
def baseEnd_3946353 : Nat := 675458640437567869812853

theorem tailTrace_3946353 : CollatzResearch.WordTrace tailWord_3946353 prefixEnd_3946353 675458640437567869812853 := by
  unfold tailWord_3946353
  simp only [CollatzResearch.WordTrace]
  refine ⟨143935318672044539278947713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95956879114696359519298475 143935318672044539278947713)
  ·
    refine ⟨107951489004033404459210785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143935318672044539278947713 107951489004033404459210785)
    ·
      refine ⟨80963616753025053344408089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107951489004033404459210785 80963616753025053344408089)
      ·
        refine ⟨60722712564768790008306067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80963616753025053344408089 60722712564768790008306067)
        ·
          refine ⟨91084068847153185012459101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60722712564768790008306067 91084068847153185012459101)
          ·
            refine ⟨34156525817682444379672163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91084068847153185012459101 34156525817682444379672163)
            ·
              refine ⟨51234788726523666569508245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34156525817682444379672163 51234788726523666569508245)
              ·
                refine ⟨2401630721555796870445699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51234788726523666569508245 2401630721555796870445699)
                ·
                  refine ⟨3602446082333695305668549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401630721555796870445699 3602446082333695305668549)
                  ·
                    refine ⟨675458640437567869812853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3602446082333695305668549 675458640437567869812853)
                    ·
                      rfl

theorem cell23_3946353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_3946353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946353 prefixEnd_3946353 := by exact prefixLift 3946353
  have htrace : WordTrace (prefixWord ++ tailWord_3946353) baseStart_3946353 baseEnd_3946353 := by
    simpa [prefixWord, tailWord_3946353, baseEnd_3946353] using wordTrace_append hprefix tailTrace_3946353
  have hstable : (prefixWord ++ tailWord_3946353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946353).length < 2 ^ (prefixWord ++ tailWord_3946353).sum := by decide
  have hdescent : baseEnd_3946353 < baseStart_3946353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946409 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 5, 6]
def baseStart_3946409 : Nat := 118140960795 + 3946409 * 2 ^ 59
def prefixEnd_3946409 : Nat := 4983230072969 + 3 ^ 40 * 3946409 * 2
def baseEnd_3946409 : Nat := 675468225409785130112767

theorem tailTrace_3946409 : CollatzResearch.WordTrace tailWord_3946409 prefixEnd_3946409 675468225409785130112767 := by
  unfold tailWord_3946409
  simp only [CollatzResearch.WordTrace]
  refine ⟨143937361159841660842986281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95958240773227773895324187 143937361159841660842986281)
  ·
    refine ⟨107953020869881245632239711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143937361159841660842986281 107953020869881245632239711)
    ·
      refine ⟨161929531304821868448359567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107953020869881245632239711 161929531304821868448359567)
      ·
        refine ⟨242894296957232802672539351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161929531304821868448359567 242894296957232802672539351)
        ·
          refine ⟨364341445435849204008809027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242894296957232802672539351 364341445435849204008809027)
          ·
            refine ⟨546512168153773806013213541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364341445435849204008809027 546512168153773806013213541)
            ·
              refine ⟨102471031528832588627477539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 546512168153773806013213541 102471031528832588627477539)
              ·
                refine ⟨153706547293248882941216309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102471031528832588627477539 153706547293248882941216309)
                ·
                  refine ⟨14409988808742082775739029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153706547293248882941216309 14409988808742082775739029)
                  ·
                    refine ⟨675468225409785130112767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14409988808742082775739029 675468225409785130112767)
                    ·
                      rfl

theorem cell23_3946409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_3946409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946409 prefixEnd_3946409 := by exact prefixLift 3946409
  have htrace : WordTrace (prefixWord ++ tailWord_3946409) baseStart_3946409 baseEnd_3946409 := by
    simpa [prefixWord, tailWord_3946409, baseEnd_3946409] using wordTrace_append hprefix tailTrace_3946409
  have hstable : (prefixWord ++ tailWord_3946409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946409).length < 2 ^ (prefixWord ++ tailWord_3946409).sum := by decide
  have hdescent : baseEnd_3946409 < baseStart_3946409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946426 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_3946426 : Nat := 118140960795 + 3946426 * 2 ^ 59
def prefixEnd_3946426 : Nat := 4983230072969 + 3 ^ 40 * 3946426 * 2
def baseEnd_3946426 : Nat := 675471135133493941275241

theorem tailTrace_3946426 : CollatzResearch.WordTrace tailWord_3946426 prefixEnd_3946426 675471135133493941275241 := by
  unfold tailWord_3946426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35984495300195018186588783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95958654133853381830903421 35984495300195018186588783)
  ·
    refine ⟨53976742950292527279883175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35984495300195018186588783 53976742950292527279883175)
    ·
      refine ⟨80965114425438790919824763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53976742950292527279883175 80965114425438790919824763)
      ·
        refine ⟨121447671638158186379737145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80965114425438790919824763 121447671638158186379737145)
        ·
          refine ⟨91085753728618639784802859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121447671638158186379737145 91085753728618639784802859)
          ·
            refine ⟨136628630592927959677204289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91085753728618639784802859 136628630592927959677204289)
            ·
              refine ⟨102471472944695969757903217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136628630592927959677204289 102471472944695969757903217)
              ·
                refine ⟨76853604708521977318427413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102471472944695969757903217 76853604708521977318427413)
                ·
                  refine ⟨3602512720711967686801285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76853604708521977318427413 3602512720711967686801285)
                  ·
                    refine ⟨675471135133493941275241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3602512720711967686801285 675471135133493941275241)
                    ·
                      rfl

theorem cell23_3946426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_3946426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946426 prefixEnd_3946426 := by exact prefixLift 3946426
  have htrace : WordTrace (prefixWord ++ tailWord_3946426) baseStart_3946426 baseEnd_3946426 := by
    simpa [prefixWord, tailWord_3946426, baseEnd_3946426] using wordTrace_append hprefix tailTrace_3946426
  have hstable : (prefixWord ++ tailWord_3946426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946426).length < 2 ^ (prefixWord ++ tailWord_3946426).sum := by decide
  have hdescent : baseEnd_3946426 < baseStart_3946426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946430 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3946430 : Nat := 118140960795 + 3946430 * 2 ^ 59
def prefixEnd_3946430 : Nat := 4983230072969 + 3 ^ 40 * 3946430 * 2
def baseEnd_3946430 : Nat := 675471819774366602725235

theorem tailTrace_3946430 : CollatzResearch.WordTrace tailWord_3946430 prefixEnd_3946430 675471819774366602725235 := by
  unfold tailWord_3946430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17992265886595697678687593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95958751395177054286333829 17992265886595697678687593)
  ·
    refine ⟨13494199414946773259015695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17992265886595697678687593 13494199414946773259015695)
    ·
      refine ⟨20241299122420159888523543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13494199414946773259015695 20241299122420159888523543)
      ·
        refine ⟨30361948683630239832785315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20241299122420159888523543 30361948683630239832785315)
        ·
          refine ⟨45542923025445359749177973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30361948683630239832785315 45542923025445359749177973)
          ·
            refine ⟨4269649033635502476485435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45542923025445359749177973 4269649033635502476485435)
            ·
              refine ⟨6404473550453253714728153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269649033635502476485435 6404473550453253714728153)
              ·
                refine ⟨4803355162839940286046115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6404473550453253714728153 4803355162839940286046115)
                ·
                  refine ⟨7205032744259910429069173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803355162839940286046115 7205032744259910429069173)
                  ·
                    refine ⟨675471819774366602725235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7205032744259910429069173 675471819774366602725235)
                    ·
                      rfl

theorem cell23_3946430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3946430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946430 prefixEnd_3946430 := by exact prefixLift 3946430
  have htrace : WordTrace (prefixWord ++ tailWord_3946430) baseStart_3946430 baseEnd_3946430 := by
    simpa [prefixWord, tailWord_3946430, baseEnd_3946430] using wordTrace_append hprefix tailTrace_3946430
  have hstable : (prefixWord ++ tailWord_3946430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946430).length < 2 ^ (prefixWord ++ tailWord_3946430).sum := by decide
  have hdescent : baseEnd_3946430 < baseStart_3946430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946453 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3946453 : Nat := 118140960795 + 3946453 * 2 ^ 59
def prefixEnd_3946453 : Nat := 4983230072969 + 3 ^ 40 * 3946453 * 2
def baseEnd_3946453 : Nat := 2026427269378153218188099

theorem tailTrace_3946453 : CollatzResearch.WordTrace tailWord_3946453 prefixEnd_3946453 2026427269378153218188099 := by
  unfold tailWord_3946453
  simp only [CollatzResearch.WordTrace]
  refine ⟨143938965971682256357588013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95959310647788170905058675 143938965971682256357588013)
  ·
    refine ⟨53977112239380846134095505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143938965971682256357588013 53977112239380846134095505)
    ·
      refine ⟨40482834179535634600571629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53977112239380846134095505 40482834179535634600571629)
      ·
        refine ⟨15181062817325862975214361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40482834179535634600571629 15181062817325862975214361)
        ·
          refine ⟨11385797112994397231410771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15181062817325862975214361 11385797112994397231410771)
          ·
            refine ⟨17078695669491595847116157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11385797112994397231410771 17078695669491595847116157)
            ·
              refine ⟨6404510876059348442668559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17078695669491595847116157 6404510876059348442668559)
              ·
                refine ⟨9606766314089022664002839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6404510876059348442668559 9606766314089022664002839)
                ·
                  refine ⟨14410149471133533996004259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9606766314089022664002839 14410149471133533996004259)
                  ·
                    refine ⟨21615224206700300994006389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14410149471133533996004259 21615224206700300994006389)
                    ·
                      refine ⟨2026427269378153218188099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21615224206700300994006389 2026427269378153218188099)
                      ·
                        rfl

theorem cell23_3946453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3946453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946453 prefixEnd_3946453 := by exact prefixLift 3946453
  have htrace : WordTrace (prefixWord ++ tailWord_3946453) baseStart_3946453 baseEnd_3946453 := by
    simpa [prefixWord, tailWord_3946453, baseEnd_3946453] using wordTrace_append hprefix tailTrace_3946453
  have hstable : (prefixWord ++ tailWord_3946453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946453).length < 2 ^ (prefixWord ++ tailWord_3946453).sum := by decide
  have hdescent : baseEnd_3946453 < baseStart_3946453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946461 : List Nat := [1, 4, 3, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_3946461 : Nat := 118140960795 + 3946461 * 2 ^ 59
def prefixEnd_3946461 : Nat := 4983230072969 + 3 ^ 40 * 3946461 * 2
def baseEnd_3946461 : Nat := 2026431377223389186888063

theorem tailTrace_3946461 : CollatzResearch.WordTrace tailWord_3946461 prefixEnd_3946461 2026431377223389186888063 := by
  unfold tailWord_3946461
  simp only [CollatzResearch.WordTrace]
  refine ⟨143939257755653273723879237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95959505170435515815919491 143939257755653273723879237)
  ·
    refine ⟨26988610829184988823227357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143939257755653273723879237 26988610829184988823227357)
    ·
      refine ⟨10120729060944370808710259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26988610829184988823227357 10120729060944370808710259)
      ·
        refine ⟨15181093591416556213065389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10120729060944370808710259 15181093591416556213065389)
        ·
          refine ⟨5692910096781208579899521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15181093591416556213065389 5692910096781208579899521)
          ·
            refine ⟨4269682572585906434924641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5692910096781208579899521 4269682572585906434924641)
            ·
              refine ⟨3202261929439429826193481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269682572585906434924641 3202261929439429826193481)
              ·
                refine ⟨2401696447079572369645111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202261929439429826193481 2401696447079572369645111)
                ·
                  refine ⟨3602544670619358554467667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401696447079572369645111 3602544670619358554467667)
                  ·
                    refine ⟨5403817005929037831701501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3602544670619358554467667 5403817005929037831701501)
                    ·
                      refine ⟨2026431377223389186888063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5403817005929037831701501 2026431377223389186888063)
                      ·
                        rfl

theorem cell23_3946461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_3946461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946461 prefixEnd_3946461 := by exact prefixLift 3946461
  have htrace : WordTrace (prefixWord ++ tailWord_3946461) baseStart_3946461 baseEnd_3946461 := by
    simpa [prefixWord, tailWord_3946461, baseEnd_3946461] using wordTrace_append hprefix tailTrace_3946461
  have hstable : (prefixWord ++ tailWord_3946461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946461).length < 2 ^ (prefixWord ++ tailWord_3946461).sum := by decide
  have hdescent : baseEnd_3946461 < baseStart_3946461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946563 : List Nat := [1, 1, 1, 3, 1, 2, 2, 7, 5]
def baseStart_3946563 : Nat := 118140960795 + 3946563 * 2 ^ 59
def prefixEnd_3946563 : Nat := 4983230072969 + 3 ^ 40 * 3946563 * 2
def baseEnd_3946563 : Nat := 225164861361127531979177

theorem tailTrace_3946563 : CollatzResearch.WordTrace tailWord_3946563 prefixEnd_3946563 225164861361127531979177 := by
  unfold tailWord_3946563
  simp only [CollatzResearch.WordTrace]
  refine ⟨143942978001283745144092343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95961985334189163429394895 143942978001283745144092343)
  ·
    refine ⟨215914467001925617716138515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143942978001283745144092343 215914467001925617716138515)
    ·
      refine ⟨323871700502888426574207773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215914467001925617716138515 323871700502888426574207773)
      ·
        refine ⟨121451887688583159965327915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323871700502888426574207773 121451887688583159965327915)
        ·
          refine ⟨182177831532874739947991873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121451887688583159965327915 182177831532874739947991873)
          ·
            refine ⟨136633373649656054960993905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182177831532874739947991873 136633373649656054960993905)
            ·
              refine ⟨102475030237242041220745429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136633373649656054960993905 102475030237242041220745429)
              ·
                refine ⟨2401758521185360341111221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102475030237242041220745429 2401758521185360341111221)
                ·
                  refine ⟨225164861361127531979177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2401758521185360341111221 225164861361127531979177)
                  ·
                    rfl

theorem cell23_3946563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 5].length) (baseStart_3946563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946563 prefixEnd_3946563 := by exact prefixLift 3946563
  have htrace : WordTrace (prefixWord ++ tailWord_3946563) baseStart_3946563 baseEnd_3946563 := by
    simpa [prefixWord, tailWord_3946563, baseEnd_3946563] using wordTrace_append hprefix tailTrace_3946563
  have hstable : (prefixWord ++ tailWord_3946563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946563).length < 2 ^ (prefixWord ++ tailWord_3946563).sum := by decide
  have hdescent : baseEnd_3946563 < baseStart_3946563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946573 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3946573 : Nat := 118140960795 + 3946573 * 2 ^ 59
def prefixEnd_3946573 : Nat := 4983230072969 + 3 ^ 40 * 3946573 * 2
def baseEnd_3946573 : Nat := 2026488887056692748687547

theorem tailTrace_3946573 : CollatzResearch.WordTrace tailWord_3946573 prefixEnd_3946573 2026488887056692748687547 := by
  unfold tailWord_3946573
  simp only [CollatzResearch.WordTrace]
  refine ⟨143943342731247516851956373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95962228487498344567970915 143943342731247516851956373)
  ·
    refine ⟨6747344190527227352435455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143943342731247516851956373 6747344190527227352435455)
    ·
      refine ⟨10121016285790841028653183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6747344190527227352435455 10121016285790841028653183)
      ·
        refine ⟨15181524428686261542979775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10121016285790841028653183 15181524428686261542979775)
        ·
          refine ⟨22772286643029392314469663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15181524428686261542979775 22772286643029392314469663)
          ·
            refine ⟨34158429964544088471704495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22772286643029392314469663 34158429964544088471704495)
            ·
              refine ⟨51237644946816132707556743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34158429964544088471704495 51237644946816132707556743)
              ·
                refine ⟨76856467420224199061335115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51237644946816132707556743 76856467420224199061335115)
                ·
                  refine ⟨115284701130336298592002673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76856467420224199061335115 115284701130336298592002673)
                  ·
                    refine ⟨86463525847752223944002005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115284701130336298592002673 86463525847752223944002005)
                    ·
                      refine ⟨2026488887056692748687547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86463525847752223944002005 2026488887056692748687547)
                      ·
                        rfl

theorem cell23_3946573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3946573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946573 prefixEnd_3946573 := by exact prefixLift 3946573
  have htrace : WordTrace (prefixWord ++ tailWord_3946573) baseStart_3946573 baseEnd_3946573 := by
    simpa [prefixWord, tailWord_3946573, baseEnd_3946573] using wordTrace_append hprefix tailTrace_3946573
  have hstable : (prefixWord ++ tailWord_3946573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946573).length < 2 ^ (prefixWord ++ tailWord_3946573).sum := by decide
  have hdescent : baseEnd_3946573 < baseStart_3946573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946610 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_3946610 : Nat := 118140960795 + 3946610 * 2 ^ 59
def prefixEnd_3946610 : Nat := 4983230072969 + 3 ^ 40 * 3946610 * 2
def baseEnd_3946610 : Nat := 675502628613636367974959

theorem tailTrace_3946610 : CollatzResearch.WordTrace tailWord_3946610 prefixEnd_3946610 675502628613636367974959 := by
  unfold tailWord_3946610
  simp only [CollatzResearch.WordTrace]
  refine ⟨35986173058028368042763321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95963128154742314780702189 35986173058028368042763321)
  ·
    refine ⟨26989629793521276032072491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35986173058028368042763321 26989629793521276032072491)
    ·
      refine ⟨40484444690281914048108737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26989629793521276032072491 40484444690281914048108737)
      ·
        refine ⟨30363333517711435536081553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40484444690281914048108737 30363333517711435536081553)
        ·
          refine ⟨22772500138283576652061165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30363333517711435536081553 22772500138283576652061165)
          ·
            refine ⟨8539687551856341244522937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22772500138283576652061165 8539687551856341244522937)
            ·
              refine ⟨6404765663892255933392203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8539687551856341244522937 6404765663892255933392203)
              ·
                refine ⟨9607148495838383900088305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6404765663892255933392203 9607148495838383900088305)
                ·
                  refine ⟨7205361371878787925066229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9607148495838383900088305 7205361371878787925066229)
                  ·
                    refine ⟨675502628613636367974959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7205361371878787925066229 675502628613636367974959)
                    ·
                      rfl

theorem cell23_3946610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_3946610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946610 prefixEnd_3946610 := by exact prefixLift 3946610
  have htrace : WordTrace (prefixWord ++ tailWord_3946610) baseStart_3946610 baseEnd_3946610 := by
    simpa [prefixWord, tailWord_3946610, baseEnd_3946610] using wordTrace_append hprefix tailTrace_3946610
  have hstable : (prefixWord ++ tailWord_3946610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946610).length < 2 ^ (prefixWord ++ tailWord_3946610).sum := by decide
  have hdescent : baseEnd_3946610 < baseStart_3946610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946647 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 2, 4, 2]
def baseStart_3946647 : Nat := 118140960795 + 3946647 * 2 ^ 59
def prefixEnd_3946647 : Nat := 4983230072969 + 3 ^ 40 * 3946647 * 2
def baseEnd_3946647 : Nat := 2026526884625125459162207

theorem tailTrace_3946647 : CollatzResearch.WordTrace tailWord_3946647 prefixEnd_3946647 2026526884625125459162207 := by
  unfold tailWord_3946647
  simp only [CollatzResearch.WordTrace]
  refine ⟨143946041732979427490150195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95964027821986284993433463 143946041732979427490150195)
  ·
    refine ⟨215919062599469141235225293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143946041732979427490150195 215919062599469141235225293)
    ·
      refine ⟨80969648474800927963209485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215919062599469141235225293 80969648474800927963209485)
      ·
        refine ⟨30363618178050347986203557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80969648474800927963209485 30363618178050347986203557)
        ·
          refine ⟨5693178408384440247413167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30363618178050347986203557 5693178408384440247413167)
          ·
            refine ⟨8539767612576660371119751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693178408384440247413167 8539767612576660371119751)
            ·
              refine ⟨12809651418864990556679627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8539767612576660371119751 12809651418864990556679627)
              ·
                refine ⟨19214477128297485835019441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12809651418864990556679627 19214477128297485835019441)
                ·
                  refine ⟨14410857846223114376264581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19214477128297485835019441 14410857846223114376264581)
                  ·
                    refine ⟨2702035846166833945549609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14410857846223114376264581 2702035846166833945549609)
                    ·
                      refine ⟨2026526884625125459162207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702035846166833945549609 2026526884625125459162207)
                      ·
                        rfl

theorem cell23_3946647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_3946647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946647 prefixEnd_3946647 := by exact prefixLift 3946647
  have htrace : WordTrace (prefixWord ++ tailWord_3946647) baseStart_3946647 baseEnd_3946647 := by
    simpa [prefixWord, tailWord_3946647, baseEnd_3946647] using wordTrace_append hprefix tailTrace_3946647
  have hstable : (prefixWord ++ tailWord_3946647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946647).length < 2 ^ (prefixWord ++ tailWord_3946647).sum := by decide
  have hdescent : baseEnd_3946647 < baseStart_3946647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946680 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 5, 1, 3]
def baseStart_3946680 : Nat := 118140960795 + 3946680 * 2 ^ 59
def prefixEnd_3946680 : Nat := 4983230072969 + 3 ^ 40 * 3946680 * 2
def baseEnd_3946680 : Nat := 2026543829486723830049555

theorem tailTrace_3946680 : CollatzResearch.WordTrace tailWord_3946680 prefixEnd_3946680 2026543829486723830049555 := by
  unfold tailWord_3946680
  simp only [CollatzResearch.WordTrace]
  refine ⟨71973622670929937063050747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95964830227906582750734329 71973622670929937063050747)
  ·
    refine ⟨107960434006394905594576121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71973622670929937063050747 107960434006394905594576121)
    ·
      refine ⟨80970325504796179195932091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107960434006394905594576121 80970325504796179195932091)
      ·
        refine ⟨121455488257194268793898137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80970325504796179195932091 121455488257194268793898137)
        ·
          refine ⟨91091616192895701595423603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121455488257194268793898137 91091616192895701595423603)
          ·
            refine ⟨136637424289343552393135405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91091616192895701595423603 136637424289343552393135405)
            ·
              refine ⟨51239034108503832147425777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136637424289343552393135405 51239034108503832147425777)
              ·
                refine ⟨38429275581377874110569333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51239034108503832147425777 38429275581377874110569333)
                ·
                  refine ⟨3602744585754175697865875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38429275581377874110569333 3602744585754175697865875)
                  ·
                    refine ⟨5404116878631263546798813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3602744585754175697865875 5404116878631263546798813)
                    ·
                      refine ⟨2026543829486723830049555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5404116878631263546798813 2026543829486723830049555)
                      ·
                        rfl

theorem cell23_3946680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_3946680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946680 prefixEnd_3946680 := by exact prefixLift 3946680
  have htrace : WordTrace (prefixWord ++ tailWord_3946680) baseStart_3946680 baseEnd_3946680 := by
    simpa [prefixWord, tailWord_3946680, baseEnd_3946680] using wordTrace_append hprefix tailTrace_3946680
  have hstable : (prefixWord ++ tailWord_3946680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946680).length < 2 ^ (prefixWord ++ tailWord_3946680).sum := by decide
  have hdescent : baseEnd_3946680 < baseStart_3946680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946717 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3946717 : Nat := 118140960795 + 3946717 * 2 ^ 59
def prefixEnd_3946717 : Nat := 4983230072969 + 3 ^ 40 * 3946717 * 2
def baseEnd_3946717 : Nat := 675520942756980061762295

theorem tailTrace_3946717 : CollatzResearch.WordTrace tailWord_3946717 prefixEnd_3946717 675520942756980061762295 := by
  unfold tailWord_3946717
  simp only [CollatzResearch.WordTrace]
  refine ⟨143948594842725829445198405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95965729895150552963465603 143948594842725829445198405)
  ·
    refine ⟨26990361533011093020974701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143948594842725829445198405 26990361533011093020974701)
    ·
      refine ⟨10121385574879159882865513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26990361533011093020974701 10121385574879159882865513)
      ·
        refine ⟨7591039181159369912149135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10121385574879159882865513 7591039181159369912149135)
        ·
          refine ⟨11386558771739054868223703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591039181159369912149135 11386558771739054868223703)
          ·
            refine ⟨17079838157608582302335555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11386558771739054868223703 17079838157608582302335555)
            ·
              refine ⟨25619757236412873453503333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17079838157608582302335555 25619757236412873453503333)
              ·
                refine ⟨4803704481827413772531875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25619757236412873453503333 4803704481827413772531875)
                ·
                  refine ⟨7205556722741120658797813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803704481827413772531875 7205556722741120658797813)
                  ·
                    refine ⟨675520942756980061762295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7205556722741120658797813 675520942756980061762295)
                    ·
                      rfl

theorem cell23_3946717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3946717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946717 prefixEnd_3946717 := by exact prefixLift 3946717
  have htrace : WordTrace (prefixWord ++ tailWord_3946717) baseStart_3946717 baseEnd_3946717 := by
    simpa [prefixWord, tailWord_3946717, baseEnd_3946717] using wordTrace_append hprefix tailTrace_3946717
  have hstable : (prefixWord ++ tailWord_3946717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946717).length < 2 ^ (prefixWord ++ tailWord_3946717).sum := by decide
  have hdescent : baseEnd_3946717 < baseStart_3946717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946720 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 2, 6, 2]
def baseStart_3946720 : Nat := 118140960795 + 3946720 * 2 ^ 59
def prefixEnd_3946720 : Nat := 4983230072969 + 3 ^ 40 * 3946720 * 2
def baseEnd_3946720 : Nat := 2026564368712903673549371

theorem tailTrace_3946720 : CollatzResearch.WordTrace tailWord_3946720 prefixEnd_3946720 2026564368712903673549371 := by
  unfold tailWord_3946720
  simp only [CollatzResearch.WordTrace]
  refine ⟨71974352130857480478778807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95965802841143307305038409 71974352130857480478778807)
  ·
    refine ⟨107961528196286220718168211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71974352130857480478778807 107961528196286220718168211)
    ·
      refine ⟨161942292294429331077252317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107961528196286220718168211 161942292294429331077252317)
      ·
        refine ⟨60728359610410999153969619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161942292294429331077252317 60728359610410999153969619)
        ·
          refine ⟨91092539415616498730954429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60728359610410999153969619 91092539415616498730954429)
          ·
            refine ⟨34159702280856187024107911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91092539415616498730954429 34159702280856187024107911)
            ·
              refine ⟨51239553421284280536161867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34159702280856187024107911 51239553421284280536161867)
              ·
                refine ⟨76859330131926420804242801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51239553421284280536161867 76859330131926420804242801)
                ·
                  refine ⟨57644497598944815603182101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76859330131926420804242801 57644497598944815603182101)
                  ·
                    refine ⟨2702085824950538231399161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57644497598944815603182101 2702085824950538231399161)
                    ·
                      refine ⟨2026564368712903673549371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702085824950538231399161 2026564368712903673549371)
                      ·
                        rfl

theorem cell23_3946720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_3946720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946720 prefixEnd_3946720 := by exact prefixLift 3946720
  have htrace : WordTrace (prefixWord ++ tailWord_3946720) baseStart_3946720 baseEnd_3946720 := by
    simpa [prefixWord, tailWord_3946720, baseEnd_3946720] using wordTrace_append hprefix tailTrace_3946720
  have hstable : (prefixWord ++ tailWord_3946720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946720).length < 2 ^ (prefixWord ++ tailWord_3946720).sum := by decide
  have hdescent : baseEnd_3946720 < baseStart_3946720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946730 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_3946730 : Nat := 118140960795 + 3946730 * 2 ^ 59
def prefixEnd_3946730 : Nat := 4983230072969 + 3 ^ 40 * 3946730 * 2
def baseEnd_3946730 : Nat := 675523167839816211474775

theorem tailTrace_3946730 : CollatzResearch.WordTrace tailWord_3946730 prefixEnd_3946730 675523167839816211474775 := by
  unfold tailWord_3946730
  simp only [CollatzResearch.WordTrace]
  refine ⟨35987267247919683166355411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95966045994452488443614429 35987267247919683166355411)
  ·
    refine ⟨53980900871879524749533117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35987267247919683166355411 53980900871879524749533117)
    ·
      refine ⟨20242837826954821781074919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53980900871879524749533117 20242837826954821781074919)
      ·
        refine ⟨30364256740432232671612379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20242837826954821781074919 30364256740432232671612379)
        ·
          refine ⟨45546385110648349007418569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30364256740432232671612379 45546385110648349007418569)
          ·
            refine ⟨34159788832986261755563927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45546385110648349007418569 34159788832986261755563927)
            ·
              refine ⟨51239683249479392633345891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34159788832986261755563927 51239683249479392633345891)
              ·
                refine ⟨76859524874219088950018837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51239683249479392633345891 76859524874219088950018837)
                ·
                  refine ⟨3602790228479019794532133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76859524874219088950018837 3602790228479019794532133)
                  ·
                    refine ⟨675523167839816211474775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3602790228479019794532133 675523167839816211474775)
                    ·
                      rfl

theorem cell23_3946730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_3946730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946730 prefixEnd_3946730 := by exact prefixLift 3946730
  have htrace : WordTrace (prefixWord ++ tailWord_3946730) baseStart_3946730 baseEnd_3946730 := by
    simpa [prefixWord, tailWord_3946730, baseEnd_3946730] using wordTrace_append hprefix tailTrace_3946730
  have hstable : (prefixWord ++ tailWord_3946730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946730).length < 2 ^ (prefixWord ++ tailWord_3946730).sum := by decide
  have hdescent : baseEnd_3946730 < baseStart_3946730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946737 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 5, 2, 2]
def baseStart_3946737 : Nat := 118140960795 + 3946737 * 2 ^ 59
def prefixEnd_3946737 : Nat := 4983230072969 + 3 ^ 40 * 3946737 * 2
def baseEnd_3946737 : Nat := 2026573097884030107036793

theorem tailTrace_3946737 : CollatzResearch.WordTrace tailWord_3946737 prefixEnd_3946737 2026573097884030107036793 := by
  unfold tailWord_3946737
  simp only [CollatzResearch.WordTrace]
  refine ⟨143949324302653372860926465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95966216201768915240617643 143949324302653372860926465)
  ·
    refine ⟨107961993226990029645694849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143949324302653372860926465 107961993226990029645694849)
    ·
      refine ⟨80971494920242522234271137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107961993226990029645694849 80971494920242522234271137)
      ·
        refine ⟨60728621190181891675703353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80971494920242522234271137 60728621190181891675703353)
        ·
          refine ⟨45546465892636418756777515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60728621190181891675703353 45546465892636418756777515)
          ·
            refine ⟨68319698838954628135166273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45546465892636418756777515 68319698838954628135166273)
            ·
              refine ⟨51239774129215971101374705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68319698838954628135166273 51239774129215971101374705)
              ·
                refine ⟨38429830596911978326031029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51239774129215971101374705 38429830596911978326031029)
                ·
                  refine ⟨3602796618460497968065409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38429830596911978326031029 3602796618460497968065409)
                  ·
                    refine ⟨2702097463845373476049057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3602796618460497968065409 2702097463845373476049057)
                    ·
                      refine ⟨2026573097884030107036793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702097463845373476049057 2026573097884030107036793)
                      ·
                        rfl

theorem cell23_3946737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_3946737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946737 prefixEnd_3946737 := by exact prefixLift 3946737
  have htrace : WordTrace (prefixWord ++ tailWord_3946737) baseStart_3946737 baseEnd_3946737 := by
    simpa [prefixWord, tailWord_3946737, baseEnd_3946737] using wordTrace_append hprefix tailTrace_3946737
  have hstable : (prefixWord ++ tailWord_3946737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946737).length < 2 ^ (prefixWord ++ tailWord_3946737).sum := by decide
  have hdescent : baseEnd_3946737 < baseStart_3946737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946750 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3946750 : Nat := 118140960795 + 3946750 * 2 ^ 59
def prefixEnd_3946750 : Nat := 4983230072969 + 3 ^ 40 * 3946750 * 2
def baseEnd_3946750 : Nat := 2026579773132538556174233

theorem tailTrace_3946750 : CollatzResearch.WordTrace tailWord_3946750 prefixEnd_3946750 2026579773132538556174233 := by
  unfold tailWord_3946750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17993724806450784510143713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95966532301070850720766469 17993724806450784510143713)
  ·
    refine ⟨13495293604838088382607785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17993724806450784510143713 13495293604838088382607785)
    ·
      refine ⟨10121470203628566286955839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13495293604838088382607785 10121470203628566286955839)
      ·
        refine ⟨15182205305442849430433759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10121470203628566286955839 15182205305442849430433759)
        ·
          refine ⟨22773307958164274145650639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15182205305442849430433759 22773307958164274145650639)
          ·
            refine ⟨34159961937246411218475959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22773307958164274145650639 34159961937246411218475959)
            ·
              refine ⟨51239942905869616827713939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34159961937246411218475959 51239942905869616827713939)
              ·
                refine ⟨76859914358804425241570909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51239942905869616827713939 76859914358804425241570909)
                ·
                  refine ⟨28822467884551659465589091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76859914358804425241570909 28822467884551659465589091)
                  ·
                    refine ⟨43233701826827489198383637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28822467884551659465589091 43233701826827489198383637)
                    ·
                      refine ⟨2026579773132538556174233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43233701826827489198383637 2026579773132538556174233)
                      ·
                        rfl

theorem cell23_3946750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3946750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946750 prefixEnd_3946750 := by exact prefixLift 3946750
  have htrace : WordTrace (prefixWord ++ tailWord_3946750) baseStart_3946750 baseEnd_3946750 := by
    simpa [prefixWord, tailWord_3946750, baseEnd_3946750] using wordTrace_append hprefix tailTrace_3946750
  have hstable : (prefixWord ++ tailWord_3946750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946750).length < 2 ^ (prefixWord ++ tailWord_3946750).sum := by decide
  have hdescent : baseEnd_3946750 < baseStart_3946750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946760 : List Nat := [2, 1, 3, 2, 3, 2, 2, 8]
def baseStart_3946760 : Nat := 118140960795 + 3946760 * 2 ^ 59
def prefixEnd_3946760 : Nat := 4983230072969 + 3 ^ 40 * 3946760 * 2
def baseEnd_3946760 : Nat := 75058700294040130261081

theorem tailTrace_3946760 : CollatzResearch.WordTrace tailWord_3946760 prefixEnd_3946760 75058700294040130261081 := by
  unfold tailWord_3946760
  simp only [CollatzResearch.WordTrace]
  refine ⟨71975081590785023894506867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95966775454380031859342489 71975081590785023894506867)
  ·
    refine ⟨107962622386177535841760301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71975081590785023894506867 107962622386177535841760301)
    ·
      refine ⟨40485983394816575940660113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107962622386177535841760301 40485983394816575940660113)
      ·
        refine ⟨30364487546112431955495085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40485983394816575940660113 30364487546112431955495085)
        ·
          refine ⟨11386682829792161983310657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30364487546112431955495085 11386682829792161983310657)
          ·
            refine ⟨8540012122344121487482993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11386682829792161983310657 8540012122344121487482993)
            ·
              refine ⟨6405009091758091115612245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8540012122344121487482993 6405009091758091115612245)
              ·
                refine ⟨75058700294040130261081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6405009091758091115612245 75058700294040130261081)
                ·
                  rfl

theorem cell23_3946760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 8].length) (baseStart_3946760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946760 prefixEnd_3946760 := by exact prefixLift 3946760
  have htrace : WordTrace (prefixWord ++ tailWord_3946760) baseStart_3946760 baseEnd_3946760 := by
    simpa [prefixWord, tailWord_3946760, baseEnd_3946760] using wordTrace_append hprefix tailTrace_3946760
  have hstable : (prefixWord ++ tailWord_3946760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946760).length < 2 ^ (prefixWord ++ tailWord_3946760).sum := by decide
  have hdescent : baseEnd_3946760 < baseStart_3946760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946763 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 6]
def baseStart_3946763 : Nat := 118140960795 + 3946763 * 2 ^ 59
def prefixEnd_3946763 : Nat := 4983230072969 + 3 ^ 40 * 3946763 * 2
def baseEnd_3946763 : Nat := 2026586448381047005311673

theorem tailTrace_3946763 : CollatzResearch.WordTrace tailWord_3946763 prefixEnd_3946763 2026586448381047005311673 := by
  unfold tailWord_3946763
  simp only [CollatzResearch.WordTrace]
  refine ⟨143950272600559179301372943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95966848400372786200915295 143950272600559179301372943)
  ·
    refine ⟨215925408900838768952059415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143950272600559179301372943 215925408900838768952059415)
    ·
      refine ⟨323888113351258153428089123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215925408900838768952059415 323888113351258153428089123)
      ·
        refine ⟨485832170026887230142133685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323888113351258153428089123 485832170026887230142133685)
        ·
          refine ⟨45546765940020677825825033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 485832170026887230142133685 45546765940020677825825033)
          ·
            refine ⟨34160074455015508369368775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45546765940020677825825033 34160074455015508369368775)
            ·
              refine ⟨51240111682523262554053163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34160074455015508369368775 51240111682523262554053163)
              ·
                refine ⟨76860167523784893831079745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51240111682523262554053163 76860167523784893831079745)
                ·
                  refine ⟨57645125642838670373309809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76860167523784893831079745 57645125642838670373309809)
                  ·
                    refine ⟨43233844232129002779982357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57645125642838670373309809 43233844232129002779982357)
                    ·
                      refine ⟨2026586448381047005311673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43233844232129002779982357 2026586448381047005311673)
                      ·
                        rfl

theorem cell23_3946763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_3946763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946763 prefixEnd_3946763 := by exact prefixLift 3946763
  have htrace : WordTrace (prefixWord ++ tailWord_3946763) baseStart_3946763 baseEnd_3946763 := by
    simpa [prefixWord, tailWord_3946763, baseEnd_3946763] using wordTrace_append hprefix tailTrace_3946763
  have hstable : (prefixWord ++ tailWord_3946763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946763).length < 2 ^ (prefixWord ++ tailWord_3946763).sum := by decide
  have hdescent : baseEnd_3946763 < baseStart_3946763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946810 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_3946810 : Nat := 118140960795 + 3946810 * 2 ^ 59
def prefixEnd_3946810 : Nat := 4983230072969 + 3 ^ 40 * 3946810 * 2
def baseEnd_3946810 : Nat := 2026610581971808321423957

theorem tailTrace_3946810 : CollatzResearch.WordTrace tailWord_3946810 prefixEnd_3946810 2026610581971808321423957 := by
  unfold tailWord_3946810
  simp only [CollatzResearch.WordTrace]
  refine ⟨35987996707847226582083471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95967991220925937552222589 35987996707847226582083471)
  ·
    refine ⟨53981995061770839873125207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35987996707847226582083471 53981995061770839873125207)
    ·
      refine ⟨80972992592656259809687811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53981995061770839873125207 80972992592656259809687811)
      ·
        refine ⟨121459488888984389714531717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80972992592656259809687811 121459488888984389714531717)
        ·
          refine ⟨22773654166684573071474697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121459488888984389714531717 22773654166684573071474697)
          ·
            refine ⟨17080240625013429803606023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22773654166684573071474697 17080240625013429803606023)
            ·
              refine ⟨25620360937520144705409035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17080240625013429803606023 25620360937520144705409035)
              ·
                refine ⟨38430541406280217058113553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25620360937520144705409035 38430541406280217058113553)
                ·
                  refine ⟨28822906054710162793585165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38430541406280217058113553 28822906054710162793585165)
                  ·
                    refine ⟨10808589770516311047594437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28822906054710162793585165 10808589770516311047594437)
                    ·
                      refine ⟨2026610581971808321423957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10808589770516311047594437 2026610581971808321423957)
                      ·
                        rfl

theorem cell23_3946810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_3946810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946810 prefixEnd_3946810 := by exact prefixLift 3946810
  have htrace : WordTrace (prefixWord ++ tailWord_3946810) baseStart_3946810 baseEnd_3946810 := by
    simpa [prefixWord, tailWord_3946810, baseEnd_3946810] using wordTrace_append hprefix tailTrace_3946810
  have hstable : (prefixWord ++ tailWord_3946810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946810).length < 2 ^ (prefixWord ++ tailWord_3946810).sum := by decide
  have hdescent : baseEnd_3946810 < baseStart_3946810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946814 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_3946814 : Nat := 118140960795 + 3946814 * 2 ^ 59
def prefixEnd_3946814 : Nat := 4983230072969 + 3 ^ 40 * 3946814 * 2
def baseEnd_3946814 : Nat := 2026612635894426305773939

theorem tailTrace_3946814 : CollatzResearch.WordTrace tailWord_3946814 prefixEnd_3946814 2026612635894426305773939 := by
  unfold tailWord_3946814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17994016590421801876434937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95968088482249610007652997 17994016590421801876434937)
  ·
    refine ⟨13495512442816351407326203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17994016590421801876434937 13495512442816351407326203)
    ·
      refine ⟨20243268664224527110989305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13495512442816351407326203 20243268664224527110989305)
      ·
        refine ⟨15182451498168395333241979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20243268664224527110989305 15182451498168395333241979)
        ·
          refine ⟨22773677247252592999862969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15182451498168395333241979 22773677247252592999862969)
          ·
            refine ⟨17080257935439444749897227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22773677247252592999862969 17080257935439444749897227)
            ·
              refine ⟨25620386903159167124845841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17080257935439444749897227 25620386903159167124845841)
              ·
                refine ⟨19215290177369375343634381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25620386903159167124845841 19215290177369375343634381)
                ·
                  refine ⟨7205733816513515753862893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19215290177369375343634381 7205733816513515753862893)
                  ·
                    refine ⟨2702150181192568407698585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7205733816513515753862893 2702150181192568407698585)
                    ·
                      refine ⟨2026612635894426305773939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702150181192568407698585 2026612635894426305773939)
                      ·
                        rfl

theorem cell23_3946814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_3946814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946814 prefixEnd_3946814 := by exact prefixLift 3946814
  have htrace : WordTrace (prefixWord ++ tailWord_3946814) baseStart_3946814 baseEnd_3946814 := by
    simpa [prefixWord, tailWord_3946814, baseEnd_3946814] using wordTrace_append hprefix tailTrace_3946814
  have hstable : (prefixWord ++ tailWord_3946814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946814).length < 2 ^ (prefixWord ++ tailWord_3946814).sum := by decide
  have hdescent : baseEnd_3946814 < baseStart_3946814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946830 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_3946830 : Nat := 118140960795 + 3946830 * 2 ^ 59
def prefixEnd_3946830 : Nat := 4983230072969 + 3 ^ 40 * 3946830 * 2
def baseEnd_3946830 : Nat := 2026620851584898243173865

theorem tailTrace_3946830 : CollatzResearch.WordTrace tailWord_3946830 prefixEnd_3946830 2026620851584898243173865 := by
  unfold tailWord_3946830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17994089536414556218007743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95968477527544299829374629 17994089536414556218007743)
  ·
    refine ⟨26991134304621834327011615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17994089536414556218007743 26991134304621834327011615)
    ·
      refine ⟨40486701456932751490517423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26991134304621834327011615 40486701456932751490517423)
      ·
        refine ⟨60730052185399127235776135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40486701456932751490517423 60730052185399127235776135)
        ·
          refine ⟨91095078278098690853664203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60730052185399127235776135 91095078278098690853664203)
          ·
            refine ⟨136642617417148036280496305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91095078278098690853664203 136642617417148036280496305)
            ·
              refine ⟨102481963062861027210372229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136642617417148036280496305 102481963062861027210372229)
              ·
                refine ⟨19215368074286442601944793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102481963062861027210372229 19215368074286442601944793)
                ·
                  refine ⟨14411526055714831951458595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19215368074286442601944793 14411526055714831951458595)
                  ·
                    refine ⟨21617289083572247927187893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14411526055714831951458595 21617289083572247927187893)
                    ·
                      refine ⟨2026620851584898243173865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21617289083572247927187893 2026620851584898243173865)
                      ·
                        rfl

theorem cell23_3946830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_3946830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946830 prefixEnd_3946830 := by exact prefixLift 3946830
  have htrace : WordTrace (prefixWord ++ tailWord_3946830) baseStart_3946830 baseEnd_3946830 := by
    simpa [prefixWord, tailWord_3946830, baseEnd_3946830] using wordTrace_append hprefix tailTrace_3946830
  have hstable : (prefixWord ++ tailWord_3946830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946830).length < 2 ^ (prefixWord ++ tailWord_3946830).sum := by decide
  have hdescent : baseEnd_3946830 < baseStart_3946830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946848 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 1, 3, 2]
def baseStart_3946848 : Nat := 118140960795 + 3946848 * 2 ^ 59
def prefixEnd_3946848 : Nat := 4983230072969 + 3 ^ 40 * 3946848 * 2
def baseEnd_3946848 : Nat := 2026630094236679172748783

theorem tailTrace_3946848 : CollatzResearch.WordTrace tailWord_3946848 prefixEnd_3946848 2026630094236679172748783 := by
  unfold tailWord_3946848
  simp only [CollatzResearch.WordTrace]
  refine ⟨71976686402625619409108599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95968915203500825878811465 71976686402625619409108599)
  ·
    refine ⟨107965029603938429113662899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71976686402625619409108599 107965029603938429113662899)
    ·
      refine ⟨161947544405907643670494349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107965029603938429113662899 161947544405907643670494349)
      ·
        refine ⟨60730329152215366376435381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161947544405907643670494349 60730329152215366376435381)
        ·
          refine ⟨5693468358020190597790817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60730329152215366376435381 5693468358020190597790817)
          ·
            refine ⟨4270101268515142948343113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5693468358020190597790817 4270101268515142948343113)
            ·
              refine ⟨3202575951386357211257335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270101268515142948343113 3202575951386357211257335)
              ·
                refine ⟨4803863927079535816886003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202575951386357211257335 4803863927079535816886003)
                ·
                  refine ⟨7205795890619303725329005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803863927079535816886003 7205795890619303725329005)
                  ·
                    refine ⟨2702173458982238896998377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7205795890619303725329005 2702173458982238896998377)
                    ·
                      refine ⟨2026630094236679172748783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702173458982238896998377 2026630094236679172748783)
                      ·
                        rfl

theorem cell23_3946848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_3946848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946848 prefixEnd_3946848 := by exact prefixLift 3946848
  have htrace : WordTrace (prefixWord ++ tailWord_3946848) baseStart_3946848 baseEnd_3946848 := by
    simpa [prefixWord, tailWord_3946848, baseEnd_3946848] using wordTrace_append hprefix tailTrace_3946848
  have hstable : (prefixWord ++ tailWord_3946848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946848).length < 2 ^ (prefixWord ++ tailWord_3946848).sum := by decide
  have hdescent : baseEnd_3946848 < baseStart_3946848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946877 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_3946877 : Nat := 118140960795 + 3946877 * 2 ^ 59
def prefixEnd_3946877 : Nat := 4983230072969 + 3 ^ 40 * 3946877 * 2
def baseEnd_3946877 : Nat := 2026644985175659559286149

theorem tailTrace_3946877 : CollatzResearch.WordTrace tailWord_3946877 prefixEnd_3946877 2026644985175659559286149 := by
  unfold tailWord_3946877
  simp only [CollatzResearch.WordTrace]
  refine ⟨143954430522146176771022885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95969620348097451180681923 143954430522146176771022885)
  ·
    refine ⟨26991455722902408144566791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143954430522146176771022885 26991455722902408144566791)
    ·
      refine ⟨40487183584353612216850187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26991455722902408144566791 40487183584353612216850187)
      ·
        refine ⟨60730775376530418325275281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40487183584353612216850187 60730775376530418325275281)
        ·
          refine ⟨45548081532397813743956461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60730775376530418325275281 45548081532397813743956461)
          ·
            refine ⟨17080530574649180153983673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45548081532397813743956461 17080530574649180153983673)
            ·
              refine ⟨12810397930986885115487755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17080530574649180153983673 12810397930986885115487755)
              ·
                refine ⟨19215596896480327673231633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12810397930986885115487755 19215596896480327673231633)
                ·
                  refine ⟨14411697672360245754923725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19215596896480327673231633 14411697672360245754923725)
                  ·
                    refine ⟨5404386627135092158096397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14411697672360245754923725 5404386627135092158096397)
                    ·
                      refine ⟨2026644985175659559286149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5404386627135092158096397 2026644985175659559286149)
                      ·
                        rfl

theorem cell23_3946877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_3946877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946877 prefixEnd_3946877 := by exact prefixLift 3946877
  have htrace : WordTrace (prefixWord ++ tailWord_3946877) baseStart_3946877 baseEnd_3946877 := by
    simpa [prefixWord, tailWord_3946877, baseEnd_3946877] using wordTrace_append hprefix tailTrace_3946877
  have hstable : (prefixWord ++ tailWord_3946877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946877).length < 2 ^ (prefixWord ++ tailWord_3946877).sum := by decide
  have hdescent : baseEnd_3946877 < baseStart_3946877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946917 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_3946917 : Nat := 118140960795 + 3946917 * 2 ^ 59
def prefixEnd_3946917 : Nat := 4983230072969 + 3 ^ 40 * 3946917 * 2
def baseEnd_3946917 : Nat := 2026665524401839402785965

theorem tailTrace_3946917 : CollatzResearch.WordTrace tailWord_3946917 prefixEnd_3946917 2026665524401839402785965 := by
  unfold tailWord_3946917
  simp only [CollatzResearch.WordTrace]
  refine ⟨143955889442001263602479005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95970592961334175734986003 143955889442001263602479005)
  ·
    refine ⟨53983458540750473850929627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143955889442001263602479005 53983458540750473850929627)
    ·
      refine ⟨80975187811125710776394441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53983458540750473850929627 80975187811125710776394441)
      ·
        refine ⟨60731390858344283082295831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80975187811125710776394441 60731390858344283082295831)
        ·
          refine ⟨91097086287516424623443747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60731390858344283082295831 91097086287516424623443747)
          ·
            refine ⟨136645629431274636935165621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91097086287516424623443747 136645629431274636935165621)
            ·
              refine ⟨12810527759181997212671777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136645629431274636935165621 12810527759181997212671777)
              ·
                refine ⟨9607895819386497909503833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12810527759181997212671777 9607895819386497909503833)
                ·
                  refine ⟨7205921864539873432127875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9607895819386497909503833 7205921864539873432127875)
                  ·
                    refine ⟨10808882796809810148191813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7205921864539873432127875 10808882796809810148191813)
                    ·
                      refine ⟨2026665524401839402785965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10808882796809810148191813 2026665524401839402785965)
                      ·
                        rfl

theorem cell23_3946917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_3946917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946917 prefixEnd_3946917 := by exact prefixLift 3946917
  have htrace : WordTrace (prefixWord ++ tailWord_3946917) baseStart_3946917 baseEnd_3946917 := by
    simpa [prefixWord, tailWord_3946917, baseEnd_3946917] using wordTrace_append hprefix tailTrace_3946917
  have hstable : (prefixWord ++ tailWord_3946917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946917).length < 2 ^ (prefixWord ++ tailWord_3946917).sum := by decide
  have hdescent : baseEnd_3946917 < baseStart_3946917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3946954 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_3946954 : Nat := 118140960795 + 3946954 * 2 ^ 59
def prefixEnd_3946954 : Nat := 4983230072969 + 3 ^ 40 * 3946954 * 2
def baseEnd_3946954 : Nat := 2026684523186055758023295

theorem tailTrace_3946954 : CollatzResearch.WordTrace tailWord_3946954 prefixEnd_3946954 2026684523186055758023295 := by
  unfold tailWord_3946954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35989309735716804730393979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95971492628578145947717277 35989309735716804730393979)
  ·
    refine ⟨53983964603575207095590969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35989309735716804730393979 53983964603575207095590969)
    ·
      refine ⟨40487973452681405321693227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53983964603575207095590969 40487973452681405321693227)
      ·
        refine ⟨60731960179022107982539841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40487973452681405321693227 60731960179022107982539841)
        ·
          refine ⟨45548970134266580986904881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60731960179022107982539841 45548970134266580986904881)
          ·
            refine ⟨34161727600699935740178661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45548970134266580986904881 34161727600699935740178661)
            ·
              refine ⟨6405323925131237951283499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34161727600699935740178661 6405323925131237951283499)
              ·
                refine ⟨9607985887696856926925249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6405323925131237951283499 9607985887696856926925249)
                ·
                  refine ⟨7205989415772642695193937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9607985887696856926925249 7205989415772642695193937)
                  ·
                    refine ⟨5404492061829482021395453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7205989415772642695193937 5404492061829482021395453)
                    ·
                      refine ⟨2026684523186055758023295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5404492061829482021395453 2026684523186055758023295)
                      ·
                        rfl

theorem cell23_3946954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_3946954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3946954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3946954 prefixEnd_3946954 := by exact prefixLift 3946954
  have htrace : WordTrace (prefixWord ++ tailWord_3946954) baseStart_3946954 baseEnd_3946954 := by
    simpa [prefixWord, tailWord_3946954, baseEnd_3946954] using wordTrace_append hprefix tailTrace_3946954
  have hstable : (prefixWord ++ tailWord_3946954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3946954).length < 2 ^ (prefixWord ++ tailWord_3946954).sum := by decide
  have hdescent : baseEnd_3946954 < baseStart_3946954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3946954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947007 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_3947007 : Nat := 118140960795 + 3947007 * 2 ^ 59
def prefixEnd_3947007 : Nat := 4983230072969 + 3 ^ 40 * 3947007 * 2
def baseEnd_3947007 : Nat := 2026711737660744050660551

theorem tailTrace_3947007 : CollatzResearch.WordTrace tailWord_3947007 prefixEnd_3947007 2026711737660744050660551 := by
  unfold tailWord_3947007
  simp only [CollatzResearch.WordTrace]
  refine ⟨143959172011675208973255275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95972781341116805982170183 143959172011675208973255275)
  ·
    refine ⟨215938758017512813459882913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143959172011675208973255275 215938758017512813459882913)
    ·
      refine ⟨161954068513134610094912185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215938758017512813459882913 161954068513134610094912185)
      ·
        refine ⟨121465551384850957571184139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161954068513134610094912185 121465551384850957571184139)
        ·
          refine ⟨182198327077276436356776209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121465551384850957571184139 182198327077276436356776209)
          ·
            refine ⟨136648745307957327267582157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182198327077276436356776209 136648745307957327267582157)
            ·
              refine ⟨51243279490483997725343309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136648745307957327267582157 51243279490483997725343309)
              ·
                refine ⟨19216229808931499147003741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51243279490483997725343309 19216229808931499147003741)
                ·
                  refine ⟨7206086178349312180126403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19216229808931499147003741 7206086178349312180126403)
                  ·
                    refine ⟨10809129267523968270189605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7206086178349312180126403 10809129267523968270189605)
                    ·
                      refine ⟨2026711737660744050660551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10809129267523968270189605 2026711737660744050660551)
                      ·
                        rfl

theorem cell23_3947007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_3947007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947007 prefixEnd_3947007 := by exact prefixLift 3947007
  have htrace : WordTrace (prefixWord ++ tailWord_3947007) baseStart_3947007 baseEnd_3947007 := by
    simpa [prefixWord, tailWord_3947007, baseEnd_3947007] using wordTrace_append hprefix tailTrace_3947007
  have hstable : (prefixWord ++ tailWord_3947007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947007).length < 2 ^ (prefixWord ++ tailWord_3947007).sum := by decide
  have hdescent : baseEnd_3947007 < baseStart_3947007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947018 : List Nat := [3, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3]
def baseStart_3947018 : Nat := 118140960795 + 3947018 * 2 ^ 59
def prefixEnd_3947018 : Nat := 4983230072969 + 3 ^ 40 * 3947018 * 2
def baseEnd_3947018 : Nat := 2026717385947943507623001

theorem tailTrace_3947018 : CollatzResearch.WordTrace tailWord_3947018 prefixEnd_3947018 2026717385947943507623001 := by
  unfold tailWord_3947018
  simp only [CollatzResearch.WordTrace]
  refine ⟨35989893303658839462976427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95973048809756905234603805 35989893303658839462976427)
  ·
    refine ⟨53984839955488259194464641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35989893303658839462976427 53984839955488259194464641)
    ·
      refine ⟨40488629966616194395848481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53984839955488259194464641 40488629966616194395848481)
      ·
        refine ⟨30366472474962145796886361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40488629966616194395848481 30366472474962145796886361)
        ·
          refine ⟨22774854356221609347664771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30366472474962145796886361 22774854356221609347664771)
          ·
            refine ⟨34162281534332414021497157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22774854356221609347664771 34162281534332414021497157)
            ·
              refine ⟨6405427787687327629030717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34162281534332414021497157 6405427787687327629030717)
              ·
                refine ⟨2402035420382747860886519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6405427787687327629030717 2402035420382747860886519)
                ·
                  refine ⟨3603053130574121791329779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402035420382747860886519 3603053130574121791329779)
                  ·
                    refine ⟨5404579695861182686994669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3603053130574121791329779 5404579695861182686994669)
                    ·
                      refine ⟨2026717385947943507623001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5404579695861182686994669 2026717385947943507623001)
                      ·
                        rfl

theorem cell23_3947018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_3947018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947018 prefixEnd_3947018 := by exact prefixLift 3947018
  have htrace : WordTrace (prefixWord ++ tailWord_3947018) baseStart_3947018 baseEnd_3947018 := by
    simpa [prefixWord, tailWord_3947018, baseEnd_3947018] using wordTrace_append hprefix tailTrace_3947018
  have hstable : (prefixWord ++ tailWord_3947018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947018).length < 2 ^ (prefixWord ++ tailWord_3947018).sum := by decide
  have hdescent : baseEnd_3947018 < baseStart_3947018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947027 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 5]
def baseStart_3947027 : Nat := 118140960795 + 3947027 * 2 ^ 59
def prefixEnd_3947027 : Nat := 4983230072969 + 3 ^ 40 * 3947027 * 2
def baseEnd_3947027 : Nat := 2026722007273833972410459

theorem tailTrace_3947027 : CollatzResearch.WordTrace tailWord_3947027 prefixEnd_3947027 2026722007273833972410459 := by
  unfold tailWord_3947027
  simp only [CollatzResearch.WordTrace]
  refine ⟨143959901471602752388983335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95973267647735168259322223 143959901471602752388983335)
  ·
    refine ⟨215939852207404128583475003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143959901471602752388983335 215939852207404128583475003)
    ·
      refine ⟨323909778311106192875212505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215939852207404128583475003 323909778311106192875212505)
      ·
        refine ⟨242932333733329644656409379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323909778311106192875212505 242932333733329644656409379)
        ·
          refine ⟨364398500599994466984614069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242932333733329644656409379 364398500599994466984614069)
          ·
            refine ⟨34162359431249481279807569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 364398500599994466984614069 34162359431249481279807569)
            ·
              refine ⟨25621769573437110959855677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34162359431249481279807569 25621769573437110959855677)
              ·
                refine ⟨9608163590038916609945879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25621769573437110959855677 9608163590038916609945879)
                ·
                  refine ⟨14412245385058374914918819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9608163590038916609945879 14412245385058374914918819)
                  ·
                    refine ⟨21618368077587562372378229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14412245385058374914918819 21618368077587562372378229)
                    ·
                      refine ⟨2026722007273833972410459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21618368077587562372378229 2026722007273833972410459)
                      ·
                        rfl

theorem cell23_3947027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_3947027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947027 prefixEnd_3947027 := by exact prefixLift 3947027
  have htrace : WordTrace (prefixWord ++ tailWord_3947027) baseStart_3947027 baseEnd_3947027 := by
    simpa [prefixWord, tailWord_3947027, baseEnd_3947027] using wordTrace_append hprefix tailTrace_3947027
  have hstable : (prefixWord ++ tailWord_3947027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947027).length < 2 ^ (prefixWord ++ tailWord_3947027).sum := by decide
  have hdescent : baseEnd_3947027 < baseStart_3947027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947061 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_3947061 : Nat := 118140960795 + 3947061 * 2 ^ 59
def prefixEnd_3947061 : Nat := 4983230072969 + 3 ^ 40 * 3947061 * 2
def baseEnd_3947061 : Nat := 2026739465616086839385303

theorem tailTrace_3947061 : CollatzResearch.WordTrace tailWord_3947061 prefixEnd_3947061 2026739465616086839385303 := by
  unfold tailWord_3947061
  simp only [CollatzResearch.WordTrace]
  refine ⟨143961141553479576195721037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95974094368986384130480691 143961141553479576195721037)
  ·
    refine ⟨53985428082554841073395389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143961141553479576195721037 53985428082554841073395389)
    ·
      refine ⟨20244535530958065402523271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53985428082554841073395389 20244535530958065402523271)
      ·
        refine ⟨30366803296437098103784907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20244535530958065402523271 30366803296437098103784907)
        ·
          refine ⟨45550204944655647155677361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30366803296437098103784907 45550204944655647155677361)
          ·
            refine ⟨34162653708491735366758021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45550204944655647155677361 34162653708491735366758021)
            ·
              refine ⟨6405497570342200381267129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34162653708491735366758021 6405497570342200381267129)
              ·
                refine ⟨4804123177756650285950347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6405497570342200381267129 4804123177756650285950347)
                ·
                  refine ⟨7206184766634975428925521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4804123177756650285950347 7206184766634975428925521)
                  ·
                    refine ⟨5404638574976231571694141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7206184766634975428925521 5404638574976231571694141)
                    ·
                      refine ⟨2026739465616086839385303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5404638574976231571694141 2026739465616086839385303)
                      ·
                        rfl

theorem cell23_3947061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_3947061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947061 prefixEnd_3947061 := by exact prefixLift 3947061
  have htrace : WordTrace (prefixWord ++ tailWord_3947061) baseStart_3947061 baseEnd_3947061 := by
    simpa [prefixWord, tailWord_3947061, baseEnd_3947061] using wordTrace_append hprefix tailTrace_3947061
  have hstable : (prefixWord ++ tailWord_3947061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947061).length < 2 ^ (prefixWord ++ tailWord_3947061).sum := by decide
  have hdescent : baseEnd_3947061 < baseStart_3947061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947078 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3947078 : Nat := 118140960795 + 3947078 * 2 ^ 59
def prefixEnd_3947078 : Nat := 4983230072969 + 3 ^ 40 * 3947078 * 2
def baseEnd_3947078 : Nat := 2026748194787213272872725

theorem tailTrace_3947078 : CollatzResearch.WordTrace tailWord_3947078 prefixEnd_3947078 2026748194787213272872725 := by
  unfold tailWord_3947078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498805049825562128096559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95974507729611992066059925 4498805049825562128096559)
  ·
    refine ⟨6748207574738343192144839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4498805049825562128096559 6748207574738343192144839)
    ·
      refine ⟨10122311362107514788217259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748207574738343192144839 10122311362107514788217259)
      ·
        refine ⟨15183467043161272182325889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10122311362107514788217259 15183467043161272182325889)
        ·
          refine ⟨11387600282370954136744417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15183467043161272182325889 11387600282370954136744417)
          ·
            refine ⟨8540700211778215602558313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11387600282370954136744417 8540700211778215602558313)
            ·
              refine ⟨6405525158833661701918735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8540700211778215602558313 6405525158833661701918735)
              ·
                refine ⟨9608287738250492552878103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6405525158833661701918735 9608287738250492552878103)
                ·
                  refine ⟨14412431607375738829317155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9608287738250492552878103 14412431607375738829317155)
                  ·
                    refine ⟨21618647411063608243975733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14412431607375738829317155 21618647411063608243975733)
                    ·
                      refine ⟨2026748194787213272872725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21618647411063608243975733 2026748194787213272872725)
                      ·
                        rfl

theorem cell23_3947078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3947078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947078 prefixEnd_3947078 := by exact prefixLift 3947078
  have htrace : WordTrace (prefixWord ++ tailWord_3947078) baseStart_3947078 baseEnd_3947078 := by
    simpa [prefixWord, tailWord_3947078, baseEnd_3947078] using wordTrace_append hprefix tailTrace_3947078
  have hstable : (prefixWord ++ tailWord_3947078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947078).length < 2 ^ (prefixWord ++ tailWord_3947078).sum := by decide
  have hdescent : baseEnd_3947078 < baseStart_3947078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947092 : List Nat := [2, 4, 1, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_3947092 : Nat := 118140960795 + 3947092 * 2 ^ 59
def prefixEnd_3947092 : Nat := 4983230072969 + 3 ^ 40 * 3947092 * 2
def baseEnd_3947092 : Nat := 2026755383516376218097661

theorem tailTrace_3947092 : CollatzResearch.WordTrace tailWord_3947092 prefixEnd_3947092 2026755383516376218097661 := by
  unfold tailWord_3947092
  simp only [CollatzResearch.WordTrace]
  refine ⟨71981136108183634245049765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95974848144244845660066353 71981136108183634245049765)
  ·
    refine ⟨13496463020284431420946831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71981136108183634245049765 13496463020284431420946831)
    ·
      refine ⟨20244694530426647131420247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13496463020284431420946831 20244694530426647131420247)
      ·
        refine ⟨30367041795639970697130371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20244694530426647131420247 30367041795639970697130371)
        ·
          refine ⟨45550562693459956045695557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30367041795639970697130371 45550562693459956045695557)
          ·
            refine ⟨8540730505023741758567917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45550562693459956045695557 8540730505023741758567917)
            ·
              refine ⟨3202773939383903159462969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8540730505023741758567917 3202773939383903159462969)
              ·
                refine ⟨2402080454537927369597227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202773939383903159462969 2402080454537927369597227)
                ·
                  refine ⟨3603120681806891054395841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402080454537927369597227 3603120681806891054395841)
                  ·
                    refine ⟨2702340511355168290796881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3603120681806891054395841 2702340511355168290796881)
                    ·
                      refine ⟨2026755383516376218097661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702340511355168290796881 2026755383516376218097661)
                      ·
                        rfl

theorem cell23_3947092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_3947092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947092 prefixEnd_3947092 := by exact prefixLift 3947092
  have htrace : WordTrace (prefixWord ++ tailWord_3947092) baseStart_3947092 baseEnd_3947092 := by
    simpa [prefixWord, tailWord_3947092, baseEnd_3947092] using wordTrace_append hprefix tailTrace_3947092
  have hstable : (prefixWord ++ tailWord_3947092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947092).length < 2 ^ (prefixWord ++ tailWord_3947092).sum := by decide
  have hdescent : baseEnd_3947092 < baseStart_3947092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947102 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3947102 : Nat := 118140960795 + 3947102 * 2 ^ 59
def prefixEnd_3947102 : Nat := 4983230072969 + 3 ^ 40 * 3947102 * 2
def baseEnd_3947102 : Nat := 675586839440973726324205

theorem tailTrace_3947102 : CollatzResearch.WordTrace tailWord_3947102 prefixEnd_3947102 675586839440973726324205 := by
  unfold tailWord_3947102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17995329618291380024745445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95975091297554026798642373 17995329618291380024745445)
  ·
    refine ⟨3374124303429633754639771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17995329618291380024745445 3374124303429633754639771)
    ·
      refine ⟨5061186455144450631959657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3374124303429633754639771 5061186455144450631959657)
      ·
        refine ⟨3795889841358337973969743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5061186455144450631959657 3795889841358337973969743)
        ·
          refine ⟨5693834762037506960954615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795889841358337973969743 5693834762037506960954615)
          ·
            refine ⟨8540752143056260441431923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693834762037506960954615 8540752143056260441431923)
            ·
              refine ⟨12811128214584390662147885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8540752143056260441431923 12811128214584390662147885)
              ·
                refine ⟨4804173080469146498305457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12811128214584390662147885 4804173080469146498305457)
                ·
                  refine ⟨3603129810351859873729093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4804173080469146498305457 3603129810351859873729093)
                  ·
                    refine ⟨675586839440973726324205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3603129810351859873729093 675586839440973726324205)
                    ·
                      rfl

theorem cell23_3947102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3947102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947102 prefixEnd_3947102 := by exact prefixLift 3947102
  have htrace : WordTrace (prefixWord ++ tailWord_3947102) baseStart_3947102 baseEnd_3947102 := by
    simpa [prefixWord, tailWord_3947102, baseEnd_3947102] using wordTrace_append hprefix tailTrace_3947102
  have hstable : (prefixWord ++ tailWord_3947102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947102).length < 2 ^ (prefixWord ++ tailWord_3947102).sum := by decide
  have hdescent : baseEnd_3947102 < baseStart_3947102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947107 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 1, 8]
def baseStart_3947107 : Nat := 118140960795 + 3947107 * 2 ^ 59
def prefixEnd_3947107 : Nat := 4983230072969 + 3 ^ 40 * 3947107 * 2
def baseEnd_3947107 : Nat := 675587695242064553136697

theorem tailTrace_3947107 : CollatzResearch.WordTrace tailWord_3947107 prefixEnd_3947107 675587695242064553136697 := by
  unfold tailWord_3947107
  simp only [CollatzResearch.WordTrace]
  refine ⟨143962819311312926051895575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95975212874208617367930383 143962819311312926051895575)
  ·
    refine ⟨215944228966969389077843363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143962819311312926051895575 215944228966969389077843363)
    ·
      refine ⟨323916343450454083616765045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215944228966969389077843363 323916343450454083616765045)
      ·
        refine ⟨30367157198480070339071723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323916343450454083616765045 30367157198480070339071723)
        ·
          refine ⟨45550735797720105508607585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30367157198480070339071723 45550735797720105508607585)
          ·
            refine ⟨34163051848290079131455689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45550735797720105508607585 34163051848290079131455689)
            ·
              refine ⟨25622288886217559348591767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34163051848290079131455689 25622288886217559348591767)
              ·
                refine ⟨38433433329326339022887651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25622288886217559348591767 38433433329326339022887651)
                ·
                  refine ⟨57650149993989508534331477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38433433329326339022887651 57650149993989508534331477)
                  ·
                    refine ⟨675587695242064553136697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57650149993989508534331477 675587695242064553136697)
                    ·
                      rfl

theorem cell23_3947107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 8].length) (baseStart_3947107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947107 prefixEnd_3947107 := by exact prefixLift 3947107
  have htrace : WordTrace (prefixWord ++ tailWord_3947107) baseStart_3947107 baseEnd_3947107 := by
    simpa [prefixWord, tailWord_3947107, baseEnd_3947107] using wordTrace_append hprefix tailTrace_3947107
  have hstable : (prefixWord ++ tailWord_3947107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947107).length < 2 ^ (prefixWord ++ tailWord_3947107).sum := by decide
  have hdescent : baseEnd_3947107 < baseStart_3947107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947118 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_3947118 : Nat := 118140960795 + 3947118 * 2 ^ 59
def prefixEnd_3947118 : Nat := 4983230072969 + 3 ^ 40 * 3947118 * 2
def baseEnd_3947118 : Nat := 2026768734013393116372541

theorem tailTrace_3947118 : CollatzResearch.WordTrace tailWord_3947118 prefixEnd_3947118 2026768734013393116372541 := by
  unfold tailWord_3947118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17995402564284134366318251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95975480342848716620364005 17995402564284134366318251)
  ·
    refine ⟨26993103846426201549477377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17995402564284134366318251 26993103846426201549477377)
    ·
      refine ⟨20244827884819651162108033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26993103846426201549477377 20244827884819651162108033)
      ·
        refine ⟨15183620913614738371581025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20244827884819651162108033 15183620913614738371581025)
        ·
          refine ⟨11387715685211053778685769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15183620913614738371581025 11387715685211053778685769)
          ·
            refine ⟨8540786763908290334014327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11387715685211053778685769 8540786763908290334014327)
            ·
              refine ⟨12811180145862435501021491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8540786763908290334014327 12811180145862435501021491)
              ·
                refine ⟨19216770218793653251532237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12811180145862435501021491 19216770218793653251532237)
                ·
                  refine ⟨7206288832047619969324589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19216770218793653251532237 7206288832047619969324589)
                  ·
                    refine ⟨2702358312017857488496721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7206288832047619969324589 2702358312017857488496721)
                    ·
                      refine ⟨2026768734013393116372541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702358312017857488496721 2026768734013393116372541)
                      ·
                        rfl

theorem cell23_3947118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_3947118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947118 prefixEnd_3947118 := by exact prefixLift 3947118
  have htrace : WordTrace (prefixWord ++ tailWord_3947118) baseStart_3947118 baseEnd_3947118 := by
    simpa [prefixWord, tailWord_3947118, baseEnd_3947118] using wordTrace_append hprefix tailTrace_3947118
  have hstable : (prefixWord ++ tailWord_3947118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947118).length < 2 ^ (prefixWord ++ tailWord_3947118).sum := by decide
  have hdescent : baseEnd_3947118 < baseStart_3947118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947131 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 4, 2, 2]
def baseStart_3947131 : Nat := 118140960795 + 3947131 * 2 ^ 59
def prefixEnd_3947131 : Nat := 4983230072969 + 3 ^ 40 * 3947131 * 2
def baseEnd_3947131 : Nat := 2026775409261901565509981

theorem tailTrace_3947131 : CollatzResearch.WordTrace tailWord_3947131 prefixEnd_3947131 2026775409261901565509981 := by
  unfold tailWord_3947131
  simp only [CollatzResearch.WordTrace]
  refine ⟨143963694663225978150769247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95975796442150652100512831 143963694663225978150769247)
  ·
    refine ⟨215945541994838967226153871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143963694663225978150769247 215945541994838967226153871)
    ·
      refine ⟨323918312992258450839230807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215945541994838967226153871 323918312992258450839230807)
      ·
        refine ⟨485877469488387676258846211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323918312992258450839230807 485877469488387676258846211)
        ·
          refine ⟨728816204232581514388269317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485877469488387676258846211 728816204232581514388269317)
          ·
            refine ⟨136653038293609033947800497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 728816204232581514388269317 136653038293609033947800497)
            ·
              refine ⟨102489778720206775460850373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136653038293609033947800497 102489778720206775460850373)
              ·
                refine ⟨19216833510038770398909445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102489778720206775460850373 19216833510038770398909445)
                ·
                  refine ⟨3603156283132269449795521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19216833510038770398909445 3603156283132269449795521)
                  ·
                    refine ⟨2702367212349202087346641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3603156283132269449795521 2702367212349202087346641)
                    ·
                      refine ⟨2026775409261901565509981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702367212349202087346641 2026775409261901565509981)
                      ·
                        rfl

theorem cell23_3947131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 2, 2].length) (baseStart_3947131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947131 prefixEnd_3947131 := by exact prefixLift 3947131
  have htrace : WordTrace (prefixWord ++ tailWord_3947131) baseStart_3947131 baseEnd_3947131 := by
    simpa [prefixWord, tailWord_3947131, baseEnd_3947131] using wordTrace_append hprefix tailTrace_3947131
  have hstable : (prefixWord ++ tailWord_3947131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947131).length < 2 ^ (prefixWord ++ tailWord_3947131).sum := by decide
  have hdescent : baseEnd_3947131 < baseStart_3947131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947157 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3947157 : Nat := 118140960795 + 3947157 * 2 ^ 59
def prefixEnd_3947157 : Nat := 4983230072969 + 3 ^ 40 * 3947157 * 2
def baseEnd_3947157 : Nat := 2026788759758918463784861

theorem tailTrace_3947157 : CollatzResearch.WordTrace tailWord_3947157 prefixEnd_3947157 2026788759758918463784861 := by
  unfold tailWord_3947157
  simp only [CollatzResearch.WordTrace]
  refine ⟨143964642961131784591215725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95976428640754523060810483 143964642961131784591215725)
  ·
    refine ⟨53986741110424419221705897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143964642961131784591215725 53986741110424419221705897)
    ·
      refine ⟨40490055832818314416279423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53986741110424419221705897 40490055832818314416279423)
      ·
        refine ⟨60735083749227471624419135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40490055832818314416279423 60735083749227471624419135)
        ·
          refine ⟨91102625623841207436628703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60735083749227471624419135 91102625623841207436628703)
          ·
            refine ⟨136653938435761811154943055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91102625623841207436628703 136653938435761811154943055)
            ·
              refine ⟨204980907653642716732414583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136653938435761811154943055 204980907653642716732414583)
              ·
                refine ⟨307471361480464075098621875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204980907653642716732414583 307471361480464075098621875)
                ·
                  refine ⟨461207042220696112647932813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307471361480464075098621875 461207042220696112647932813)
                  ·
                    refine ⟨172952640832761042242974805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461207042220696112647932813 172952640832761042242974805)
                    ·
                      refine ⟨2026788759758918463784861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 172952640832761042242974805 2026788759758918463784861)
                      ·
                        rfl

theorem cell23_3947157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3947157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947157 prefixEnd_3947157 := by exact prefixLift 3947157
  have htrace : WordTrace (prefixWord ++ tailWord_3947157) baseStart_3947157 baseEnd_3947157 := by
    simpa [prefixWord, tailWord_3947157, baseEnd_3947157] using wordTrace_append hprefix tailTrace_3947157
  have hstable : (prefixWord ++ tailWord_3947157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947157).length < 2 ^ (prefixWord ++ tailWord_3947157).sum := by decide
  have hdescent : baseEnd_3947157 < baseStart_3947157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947177 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_3947177 : Nat := 118140960795 + 3947177 * 2 ^ 59
def prefixEnd_3947177 : Nat := 4983230072969 + 3 ^ 40 * 3947177 * 2
def baseEnd_3947177 : Nat := 2026799029372008385534769

theorem tailTrace_3947177 : CollatzResearch.WordTrace tailWord_3947177 prefixEnd_3947177 2026799029372008385534769 := by
  unfold tailWord_3947177
  simp only [CollatzResearch.WordTrace]
  refine ⟨143965372421059328006943785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95976914947372885337962523 143965372421059328006943785)
  ·
    refine ⟨107974029315794496005207839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143965372421059328006943785 107974029315794496005207839)
    ·
      refine ⟨161961043973691744007811759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107974029315794496005207839 161961043973691744007811759)
      ·
        refine ⟨242941565960537616011717639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161961043973691744007811759 242941565960537616011717639)
        ·
          refine ⟨364412348940806424017576459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242941565960537616011717639 364412348940806424017576459)
          ·
            refine ⟨546618523411209636026364689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364412348940806424017576459 546618523411209636026364689)
            ·
              refine ⟨409963892558407227019773517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546618523411209636026364689 409963892558407227019773517)
              ·
                refine ⟨153736459709402710132415069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409963892558407227019773517 153736459709402710132415069)
                ·
                  refine ⟨57651172391026016299655651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153736459709402710132415069 57651172391026016299655651)
                  ·
                    refine ⟨86476758586539024449483477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57651172391026016299655651 86476758586539024449483477)
                    ·
                      refine ⟨2026799029372008385534769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86476758586539024449483477 2026799029372008385534769)
                      ·
                        rfl

theorem cell23_3947177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_3947177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947177 prefixEnd_3947177 := by exact prefixLift 3947177
  have htrace : WordTrace (prefixWord ++ tailWord_3947177) baseStart_3947177 baseEnd_3947177 := by
    simpa [prefixWord, tailWord_3947177, baseEnd_3947177] using wordTrace_append hprefix tailTrace_3947177
  have hstable : (prefixWord ++ tailWord_3947177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947177).length < 2 ^ (prefixWord ++ tailWord_3947177).sum := by decide
  have hdescent : baseEnd_3947177 < baseStart_3947177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947231 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 3, 4]
def baseStart_3947231 : Nat := 118140960795 + 3947231 * 2 ^ 59
def prefixEnd_3947231 : Nat := 4983230072969 + 3 ^ 40 * 3947231 * 2
def baseEnd_3947231 : Nat := 675608919109117058086507

theorem tailTrace_3947231 : CollatzResearch.WordTrace tailWord_3947231 prefixEnd_3947231 675608919109117058086507 := by
  unfold tailWord_3947231
  simp only [CollatzResearch.WordTrace]
  refine ⟨143967341962863695229409547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95978227975242463486273031 143967341962863695229409547)
  ·
    refine ⟨215951012944295542844114321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143967341962863695229409547 215951012944295542844114321)
    ·
      refine ⟨161963259708221657133085741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215951012944295542844114321 161963259708221657133085741)
      ·
        refine ⟨60736222390583121424907153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161963259708221657133085741 60736222390583121424907153)
        ·
          refine ⟨45552166792937341068680365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60736222390583121424907153 45552166792937341068680365)
          ·
            refine ⟨17082062547351502900755137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45552166792937341068680365 17082062547351502900755137)
            ·
              refine ⟨12811546910513627175566353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17082062547351502900755137 12811546910513627175566353)
              ·
                refine ⟨9608660182885220381674765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12811546910513627175566353 9608660182885220381674765)
                ·
                  refine ⟨3603247568581957643128037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9608660182885220381674765 3603247568581957643128037)
                  ·
                    refine ⟨675608919109117058086507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3603247568581957643128037 675608919109117058086507)
                    ·
                      rfl

theorem cell23_3947231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 4].length) (baseStart_3947231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947231 prefixEnd_3947231 := by exact prefixLift 3947231
  have htrace : WordTrace (prefixWord ++ tailWord_3947231) baseStart_3947231 baseEnd_3947231 := by
    simpa [prefixWord, tailWord_3947231, baseEnd_3947231] using wordTrace_append hprefix tailTrace_3947231
  have hstable : (prefixWord ++ tailWord_3947231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947231).length < 2 ^ (prefixWord ++ tailWord_3947231).sum := by decide
  have hdescent : baseEnd_3947231 < baseStart_3947231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947281 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 3, 5, 2]
def baseStart_3947281 : Nat := 118140960795 + 3947281 * 2 ^ 59
def prefixEnd_3947281 : Nat := 4983230072969 + 3 ^ 40 * 3947281 * 2
def baseEnd_3947281 : Nat := 2026852431360075978634291

theorem tailTrace_3947281 : CollatzResearch.WordTrace tailWord_3947281 prefixEnd_3947281 2026852431360075978634291 := by
  unfold tailWord_3947281
  simp only [CollatzResearch.WordTrace]
  refine ⟨143969165612682553768729697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95979443741788369179153131 143969165612682553768729697)
  ·
    refine ⟨107976874209511915326547273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143969165612682553768729697 107976874209511915326547273)
    ·
      refine ⟨80982655657133936494910455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107976874209511915326547273 80982655657133936494910455)
      ·
        refine ⟨121473983485700904742365683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80982655657133936494910455 121473983485700904742365683)
        ·
          refine ⟨182210975228551357113548525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121473983485700904742365683 182210975228551357113548525)
          ·
            refine ⟨68329115710706758917580697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182210975228551357113548525 68329115710706758917580697)
            ·
              refine ⟨51246836783030069188185523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68329115710706758917580697 51246836783030069188185523)
              ·
                refine ⟨76870255174545103782278285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51246836783030069188185523 76870255174545103782278285)
                ·
                  refine ⟨28826345690454413918354357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76870255174545103782278285 28826345690454413918354357)
                  ·
                    refine ⟨2702469908480101304845721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28826345690454413918354357 2702469908480101304845721)
                    ·
                      refine ⟨2026852431360075978634291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702469908480101304845721 2026852431360075978634291)
                      ·
                        rfl

theorem cell23_3947281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_3947281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947281 prefixEnd_3947281 := by exact prefixLift 3947281
  have htrace : WordTrace (prefixWord ++ tailWord_3947281) baseStart_3947281 baseEnd_3947281 := by
    simpa [prefixWord, tailWord_3947281, baseEnd_3947281] using wordTrace_append hprefix tailTrace_3947281
  have hstable : (prefixWord ++ tailWord_3947281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947281).length < 2 ^ (prefixWord ++ tailWord_3947281).sum := by decide
  have hdescent : baseEnd_3947281 < baseStart_3947281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947308 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_3947308 : Nat := 118140960795 + 3947308 * 2 ^ 59
def prefixEnd_3947308 : Nat := 4983230072969 + 3 ^ 40 * 3947308 * 2
def baseEnd_3947308 : Nat := 675622098445915790998889

theorem tailTrace_3947308 : CollatzResearch.WordTrace tailWord_3947308 prefixEnd_3947308 675622098445915790998889 := by
  unfold tailWord_3947308
  simp only [CollatzResearch.WordTrace]
  refine ⟨71985075191792368689981289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95980100255723158253308385 71985075191792368689981289)
  ·
    refine ⟨53988806393844276517485967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71985075191792368689981289 53988806393844276517485967)
    ·
      refine ⟨80983209590766414776228951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53988806393844276517485967 80983209590766414776228951)
      ·
        refine ⟨121474814386149622164343427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80983209590766414776228951 121474814386149622164343427)
        ·
          refine ⟨182212221579224433246515141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121474814386149622164343427 182212221579224433246515141)
          ·
            refine ⟨34164791546104581233721589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182212221579224433246515141 34164791546104581233721589)
            ·
              refine ⟨3202949207447304490661399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34164791546104581233721589 3202949207447304490661399)
              ·
                refine ⟨4804423811170956735992099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202949207447304490661399 4804423811170956735992099)
                ·
                  refine ⟨7206635716756435103988149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4804423811170956735992099 7206635716756435103988149)
                  ·
                    refine ⟨675622098445915790998889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7206635716756435103988149 675622098445915790998889)
                    ·
                      rfl

theorem cell23_3947308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_3947308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947308 prefixEnd_3947308 := by exact prefixLift 3947308
  have htrace : WordTrace (prefixWord ++ tailWord_3947308) baseStart_3947308 baseEnd_3947308 := by
    simpa [prefixWord, tailWord_3947308, baseEnd_3947308] using wordTrace_append hprefix tailTrace_3947308
  have hstable : (prefixWord ++ tailWord_3947308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947308).length < 2 ^ (prefixWord ++ tailWord_3947308).sum := by decide
  have hdescent : baseEnd_3947308 < baseStart_3947308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947316 : List Nat := [2, 5, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_3947316 : Nat := 118140960795 + 3947316 * 2 ^ 59
def prefixEnd_3947316 : Nat := 4983230072969 + 3 ^ 40 * 3947316 * 2
def baseEnd_3947316 : Nat := 675623467727661113898877

theorem tailTrace_3947316 : CollatzResearch.WordTrace tailWord_3947316 prefixEnd_3947316 675623467727661113898877 := by
  unfold tailWord_3947316
  simp only [CollatzResearch.WordTrace]
  refine ⟨71985221083777877373126901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95980294778370503164169201 71985221083777877373126901)
  ·
    refine ⟨6748614476604176003730647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71985221083777877373126901 6748614476604176003730647)
    ·
      refine ⟨10122921714906264005595971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748614476604176003730647 10122921714906264005595971)
      ·
        refine ⟨15184382572359396008393957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10122921714906264005595971 15184382572359396008393957)
        ·
          refine ⟨2847071732317386751573867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15184382572359396008393957 2847071732317386751573867)
          ·
            refine ⟨4270607598476080127360801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847071732317386751573867 4270607598476080127360801)
            ·
              refine ⟨3202955698857060095520601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270607598476080127360801 3202955698857060095520601)
              ·
                refine ⟨2402216774142795071640451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202955698857060095520601 2402216774142795071640451)
                ·
                  refine ⟨3603325161214192607460677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402216774142795071640451 3603325161214192607460677)
                  ·
                    refine ⟨675623467727661113898877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3603325161214192607460677 675623467727661113898877)
                    ·
                      rfl

theorem cell23_3947316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_3947316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947316 prefixEnd_3947316 := by exact prefixLift 3947316
  have htrace : WordTrace (prefixWord ++ tailWord_3947316) baseStart_3947316 baseEnd_3947316 := by
    simpa [prefixWord, tailWord_3947316, baseEnd_3947316] using wordTrace_append hprefix tailTrace_3947316
  have hstable : (prefixWord ++ tailWord_3947316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947316).length < 2 ^ (prefixWord ++ tailWord_3947316).sum := by decide
  have hdescent : baseEnd_3947316 < baseStart_3947316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947322 : List Nat := [3, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3]
def baseStart_3947322 : Nat := 118140960795 + 3947322 * 2 ^ 59
def prefixEnd_3947322 : Nat := 4983230072969 + 3 ^ 40 * 3947322 * 2
def baseEnd_3947322 : Nat := 2026873484066910318221603

theorem tailTrace_3947322 : CollatzResearch.WordTrace tailWord_3947322 prefixEnd_3947322 2026873484066910318221603 := by
  unfold tailWord_3947322
  simp only [CollatzResearch.WordTrace]
  refine ⟨35992665251383504442743055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95980440670356011847314813 35992665251383504442743055)
  ·
    refine ⟨53988997877075256664114583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35992665251383504442743055 53988997877075256664114583)
    ·
      refine ⟨80983496815612884996171875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53988997877075256664114583 80983496815612884996171875)
      ·
        refine ⟨121475245223419327494257813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80983496815612884996171875 121475245223419327494257813)
        ·
          refine ⟨5694152119847780976293335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121475245223419327494257813 5694152119847780976293335)
          ·
            refine ⟨8541228179771671464440003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694152119847780976293335 8541228179771671464440003)
            ·
              refine ⟨12811842269657507196660005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541228179771671464440003 12811842269657507196660005)
              ·
                refine ⟨2402220425560782599373751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12811842269657507196660005 2402220425560782599373751)
                ·
                  refine ⟨3603330638341173899060627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402220425560782599373751 3603330638341173899060627)
                  ·
                    refine ⟨5404995957511760848590941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3603330638341173899060627 5404995957511760848590941)
                    ·
                      refine ⟨2026873484066910318221603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5404995957511760848590941 2026873484066910318221603)
                      ·
                        rfl

theorem cell23_3947322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3].length) (baseStart_3947322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947322 prefixEnd_3947322 := by exact prefixLift 3947322
  have htrace : WordTrace (prefixWord ++ tailWord_3947322) baseStart_3947322 baseEnd_3947322 := by
    simpa [prefixWord, tailWord_3947322, baseEnd_3947322] using wordTrace_append hprefix tailTrace_3947322
  have hstable : (prefixWord ++ tailWord_3947322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947322).length < 2 ^ (prefixWord ++ tailWord_3947322).sum := by decide
  have hdescent : baseEnd_3947322 < baseStart_3947322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947328 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 7, 2, 2]
def baseStart_3947328 : Nat := 118140960795 + 3947328 * 2 ^ 59
def prefixEnd_3947328 : Nat := 4983230072969 + 3 ^ 40 * 3947328 * 2
def baseEnd_3947328 : Nat := 2026876564950837294746575

theorem tailTrace_3947328 : CollatzResearch.WordTrace tailWord_3947328 prefixEnd_3947328 2026876564950837294746575 := by
  unfold tailWord_3947328
  simp only [CollatzResearch.WordTrace]
  refine ⟨71985439921756140397845319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95980586562341520530460425 71985439921756140397845319)
  ·
    refine ⟨107978159882634210596767979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71985439921756140397845319 107978159882634210596767979)
    ·
      refine ⟨161967239823951315895151969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107978159882634210596767979 161967239823951315895151969)
      ·
        refine ⟨121475429867963486921363977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161967239823951315895151969 121475429867963486921363977)
        ·
          refine ⟨91106572400972615191022983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121475429867963486921363977 91106572400972615191022983)
          ·
            refine ⟨136659858601458922786534475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91106572400972615191022983 136659858601458922786534475)
            ·
              refine ⟨204989787902188384179801713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136659858601458922786534475 204989787902188384179801713)
              ·
                refine ⟨153742340926641288134851285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204989787902188384179801713 153742340926641288134851285)
                ·
                  refine ⟨3603336115468155190660577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 153742340926641288134851285 3603336115468155190660577)
                  ·
                    refine ⟨2702502086601116392995433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3603336115468155190660577 2702502086601116392995433)
                    ·
                      refine ⟨2026876564950837294746575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702502086601116392995433 2026876564950837294746575)
                      ·
                        rfl

theorem cell23_3947328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_3947328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947328 prefixEnd_3947328 := by exact prefixLift 3947328
  have htrace : WordTrace (prefixWord ++ tailWord_3947328) baseStart_3947328 baseEnd_3947328 := by
    simpa [prefixWord, tailWord_3947328, baseEnd_3947328] using wordTrace_append hprefix tailTrace_3947328
  have hstable : (prefixWord ++ tailWord_3947328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947328).length < 2 ^ (prefixWord ++ tailWord_3947328).sum := by decide
  have hdescent : baseEnd_3947328 < baseStart_3947328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947331 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 3]
def baseStart_3947331 : Nat := 118140960795 + 3947331 * 2 ^ 59
def prefixEnd_3947331 : Nat := 4983230072969 + 3 ^ 40 * 3947331 * 2
def baseEnd_3947331 : Nat := 2026878105392800783009061

theorem tailTrace_3947331 : CollatzResearch.WordTrace tailWord_3947331 prefixEnd_3947331 2026878105392800783009061 := by
  unfold tailWord_3947331
  simp only [CollatzResearch.WordTrace]
  refine ⟨143970989262501412308049847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95980659508334274872033231 143970989262501412308049847)
  ·
    refine ⟨215956483893752118462074771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143970989262501412308049847 215956483893752118462074771)
    ·
      refine ⟨323934725840628177693112157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215956483893752118462074771 323934725840628177693112157)
      ·
        refine ⟨121475522190235566634917059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323934725840628177693112157 121475522190235566634917059)
        ·
          refine ⟨182213283285353349952375589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121475522190235566634917059 182213283285353349952375589)
          ·
            refine ⟨34164990616003753116070423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182213283285353349952375589 34164990616003753116070423)
            ·
              refine ⟨51247485924005629674105635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34164990616003753116070423 51247485924005629674105635)
              ·
                refine ⟨76871228886008444511158453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51247485924005629674105635 76871228886008444511158453)
                ·
                  refine ⟨7206677708063291672921105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76871228886008444511158453 7206677708063291672921105)
                  ·
                    refine ⟨5405008281047468754690829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7206677708063291672921105 5405008281047468754690829)
                    ·
                      refine ⟨2026878105392800783009061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5405008281047468754690829 2026878105392800783009061)
                      ·
                        rfl

theorem cell23_3947331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_3947331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947331 prefixEnd_3947331 := by exact prefixLift 3947331
  have htrace : WordTrace (prefixWord ++ tailWord_3947331) baseStart_3947331 baseEnd_3947331 := by
    simpa [prefixWord, tailWord_3947331, baseEnd_3947331] using wordTrace_append hprefix tailTrace_3947331
  have hstable : (prefixWord ++ tailWord_3947331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947331).length < 2 ^ (prefixWord ++ tailWord_3947331).sum := by decide
  have hdescent : baseEnd_3947331 < baseStart_3947331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947361 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_3947361 : Nat := 118140960795 + 3947361 * 2 ^ 59
def prefixEnd_3947361 : Nat := 4983230072969 + 3 ^ 40 * 3947361 * 2
def baseEnd_3947361 : Nat := 2026893509812435665633923

theorem tailTrace_3947361 : CollatzResearch.WordTrace tailWord_3947361 prefixEnd_3947361 2026893509812435665633923 := by
  unfold tailWord_3947361
  simp only [CollatzResearch.WordTrace]
  refine ⟨143972083452392727431641937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95981388968261818287761291 143972083452392727431641937)
  ·
    refine ⟨107979062589294545573731453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143972083452392727431641937 107979062589294545573731453)
    ·
      refine ⟨40492148470985454590149295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107979062589294545573731453 40492148470985454590149295)
      ·
        refine ⟨60738222706478181885223943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40492148470985454590149295 60738222706478181885223943)
        ·
          refine ⟨91107334059717272827835915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60738222706478181885223943 91107334059717272827835915)
          ·
            refine ⟨136661001089575909241753873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91107334059717272827835915 136661001089575909241753873)
            ·
              refine ⟨102495750817181931931315405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136661001089575909241753873 102495750817181931931315405)
              ·
                refine ⟨38435906556443224474243277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102495750817181931931315405 38435906556443224474243277)
                ·
                  refine ⟨14413464958666209177841229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38435906556443224474243277 14413464958666209177841229)
                  ·
                    refine ⟨5405049359499828441690461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14413464958666209177841229 5405049359499828441690461)
                    ·
                      refine ⟨2026893509812435665633923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5405049359499828441690461 2026893509812435665633923)
                      ·
                        rfl

theorem cell23_3947361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_3947361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947361 prefixEnd_3947361 := by exact prefixLift 3947361
  have htrace : WordTrace (prefixWord ++ tailWord_3947361) baseStart_3947361 baseEnd_3947361 := by
    simpa [prefixWord, tailWord_3947361, baseEnd_3947361] using wordTrace_append hprefix tailTrace_3947361
  have hstable : (prefixWord ++ tailWord_3947361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947361).length < 2 ^ (prefixWord ++ tailWord_3947361).sum := by decide
  have hdescent : baseEnd_3947361 < baseStart_3947361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947365 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 1, 2, 3]
def baseStart_3947365 : Nat := 118140960795 + 3947365 * 2 ^ 59
def prefixEnd_3947365 : Nat := 4983230072969 + 3 ^ 40 * 3947365 * 2
def baseEnd_3947365 : Nat := 2026895563735053649983905

theorem tailTrace_3947365 : CollatzResearch.WordTrace tailWord_3947365 prefixEnd_3947365 2026895563735053649983905 := by
  unfold tailWord_3947365
  simp only [CollatzResearch.WordTrace]
  refine ⟨143972229344378236114787549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95981486229585490743191699 143972229344378236114787549)
  ·
    refine ⟨53989586004141838543045331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143972229344378236114787549 53989586004141838543045331)
    ·
      refine ⟨80984379006212757814567997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53989586004141838543045331 80984379006212757814567997)
      ·
        refine ⟨30369142127329784180462999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80984379006212757814567997 30369142127329784180462999)
        ·
          refine ⟨45553713190994676270694499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30369142127329784180462999 45553713190994676270694499)
          ·
            refine ⟨68330569786492014406041749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45553713190994676270694499 68330569786492014406041749)
            ·
              refine ⟨3202995458741813175283207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68330569786492014406041749 3202995458741813175283207)
              ·
                refine ⟨4804493188112719762924811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202995458741813175283207 4804493188112719762924811)
                ·
                  refine ⟨7206739782169079644387217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4804493188112719762924811 7206739782169079644387217)
                  ·
                    refine ⟨5405054836626809733290413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7206739782169079644387217 5405054836626809733290413)
                    ·
                      refine ⟨2026895563735053649983905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5405054836626809733290413 2026895563735053649983905)
                      ·
                        rfl

theorem cell23_3947365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_3947365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947365 prefixEnd_3947365 := by exact prefixLift 3947365
  have htrace : WordTrace (prefixWord ++ tailWord_3947365) baseStart_3947365 baseEnd_3947365 := by
    simpa [prefixWord, tailWord_3947365, baseEnd_3947365] using wordTrace_append hprefix tailTrace_3947365
  have hstable : (prefixWord ++ tailWord_3947365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947365).length < 2 ^ (prefixWord ++ tailWord_3947365).sum := by decide
  have hdescent : baseEnd_3947365 < baseStart_3947365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947388 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_3947388 : Nat := 118140960795 + 3947388 * 2 ^ 59
def prefixEnd_3947388 : Nat := 4983230072969 + 3 ^ 40 * 3947388 * 2
def baseEnd_3947388 : Nat := 2026907373790107059996299

theorem tailTrace_3947388 : CollatzResearch.WordTrace tailWord_3947388 prefixEnd_3947388 2026907373790107059996299 := by
  unfold tailWord_3947388
  simp only [CollatzResearch.WordTrace]
  refine ⟨71986534111647455521437409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95982045482196607361916545 71986534111647455521437409)
  ·
    refine ⟨53989900583735591641078057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71986534111647455521437409 53989900583735591641078057)
    ·
      refine ⟨40492425437801693730808543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53989900583735591641078057 40492425437801693730808543)
      ·
        refine ⟨60738638156702540596212815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40492425437801693730808543 60738638156702540596212815)
        ·
          refine ⟨91107957235053810894319223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60738638156702540596212815 91107957235053810894319223)
          ·
            refine ⟨136661935852580716341478835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91107957235053810894319223 136661935852580716341478835)
            ·
              refine ⟨204992903778871074512218253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136661935852580716341478835 204992903778871074512218253)
              ·
                refine ⟨76872338917076652942081845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204992903778871074512218253 76872338917076652942081845)
                ·
                  refine ⟨7206781773475936213320173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76872338917076652942081845 7206781773475936213320173)
                  ·
                    refine ⟨2702543165053476079995065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7206781773475936213320173 2702543165053476079995065)
                    ·
                      refine ⟨2026907373790107059996299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702543165053476079995065 2026907373790107059996299)
                      ·
                        rfl

theorem cell23_3947388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_3947388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947388 prefixEnd_3947388 := by exact prefixLift 3947388
  have htrace : WordTrace (prefixWord ++ tailWord_3947388) baseStart_3947388 baseEnd_3947388 := by
    simpa [prefixWord, tailWord_3947388, baseEnd_3947388] using wordTrace_append hprefix tailTrace_3947388
  have hstable : (prefixWord ++ tailWord_3947388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947388).length < 2 ^ (prefixWord ++ tailWord_3947388).sum := by decide
  have hdescent : baseEnd_3947388 < baseStart_3947388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947495 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_3947495 : Nat := 118140960795 + 3947495 * 2 ^ 59
def prefixEnd_3947495 : Nat := 4983230072969 + 3 ^ 40 * 3947495 * 2
def baseEnd_3947495 : Nat := 2026962316220138141358307

theorem tailTrace_3947495 : CollatzResearch.WordTrace tailWord_3947495 prefixEnd_3947495 2026962316220138141358307 := by
  unfold tailWord_3947495
  simp only [CollatzResearch.WordTrace]
  refine ⟨143976970833907268317019939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95984647222604845544679959 143976970833907268317019939)
  ·
    refine ⟨215965456250860902475529909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143976970833907268317019939 215965456250860902475529909)
    ·
      refine ⟨20246761523518209607080929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215965456250860902475529909 20246761523518209607080929)
      ·
        refine ⟨15185071142638657205310697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20246761523518209607080929 15185071142638657205310697)
        ·
          refine ⟨11388803356978992903983023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15185071142638657205310697 11388803356978992903983023)
          ·
            refine ⟨17083205035468489355974535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11388803356978992903983023 17083205035468489355974535)
            ·
              refine ⟨25624807553202734033961803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17083205035468489355974535 25624807553202734033961803)
              ·
                refine ⟨38437211329804101050942705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25624807553202734033961803 38437211329804101050942705)
                ·
                  refine ⟨28827908497353075788207029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38437211329804101050942705 28827908497353075788207029)
                  ·
                    refine ⟨2702616421626850855144409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28827908497353075788207029 2702616421626850855144409)
                    ·
                      refine ⟨2026962316220138141358307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702616421626850855144409 2026962316220138141358307)
                      ·
                        rfl

theorem cell23_3947495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_3947495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947495 prefixEnd_3947495 := by exact prefixLift 3947495
  have htrace : WordTrace (prefixWord ++ tailWord_3947495) baseStart_3947495 baseEnd_3947495 := by
    simpa [prefixWord, tailWord_3947495, baseEnd_3947495] using wordTrace_append hprefix tailTrace_3947495
  have hstable : (prefixWord ++ tailWord_3947495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947495).length < 2 ^ (prefixWord ++ tailWord_3947495).sum := by decide
  have hdescent : baseEnd_3947495 < baseStart_3947495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947498 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_3947498 : Nat := 118140960795 + 3947498 * 2 ^ 59
def prefixEnd_3947498 : Nat := 4983230072969 + 3 ^ 40 * 3947498 * 2
def baseEnd_3947498 : Nat := 2026963856662101629620793

theorem tailTrace_3947498 : CollatzResearch.WordTrace tailWord_3947498 prefixEnd_3947498 2026963856662101629620793 := by
  unfold tailWord_3947498
  simp only [CollatzResearch.WordTrace]
  refine ⟨35994270063224099957344787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95984720168597599886252765 35994270063224099957344787)
  ·
    refine ⟨53991405094836149936017181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35994270063224099957344787 53991405094836149936017181)
    ·
      refine ⟨20246776910563556226006443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53991405094836149936017181 20246776910563556226006443)
      ·
        refine ⟨30370165365845334339009665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20246776910563556226006443 30370165365845334339009665)
        ·
          refine ⟨22777624024384000754257249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30370165365845334339009665 22777624024384000754257249)
          ·
            refine ⟨17083218018288000565692937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22777624024384000754257249 17083218018288000565692937)
            ·
              refine ⟨12812413513716000424269703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17083218018288000565692937 12812413513716000424269703)
              ·
                refine ⟨19218620270574000636404555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12812413513716000424269703 19218620270574000636404555)
                ·
                  refine ⟨28827930405861000954606833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19218620270574000636404555 28827930405861000954606833)
                  ·
                    refine ⟨21620947804395750715955125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28827930405861000954606833 21620947804395750715955125)
                    ·
                      refine ⟨2026963856662101629620793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21620947804395750715955125 2026963856662101629620793)
                      ·
                        rfl

theorem cell23_3947498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_3947498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947498 prefixEnd_3947498 := by exact prefixLift 3947498
  have htrace : WordTrace (prefixWord ++ tailWord_3947498) baseStart_3947498 baseEnd_3947498 := by
    simpa [prefixWord, tailWord_3947498, baseEnd_3947498] using wordTrace_append hprefix tailTrace_3947498
  have hstable : (prefixWord ++ tailWord_3947498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947498).length < 2 ^ (prefixWord ++ tailWord_3947498).sum := by decide
  have hdescent : baseEnd_3947498 < baseStart_3947498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947522 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_3947522 : Nat := 118140960795 + 3947522 * 2 ^ 59
def prefixEnd_3947522 : Nat := 4983230072969 + 3 ^ 40 * 3947522 * 2
def baseEnd_3947522 : Nat := 675658726732603178573561

theorem tailTrace_3947522 : CollatzResearch.WordTrace tailWord_3947522 prefixEnd_3947522 675658726732603178573561 := by
  unfold tailWord_3947522
  simp only [CollatzResearch.WordTrace]
  refine ⟨35994488901202362982063205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95985303736539634618835213 35994488901202362982063205)
  ·
    refine ⟨6748966668975443059136851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35994488901202362982063205 6748966668975443059136851)
    ·
      refine ⟨10123450003463164588705277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748966668975443059136851 10123450003463164588705277)
      ·
        refine ⟨3796293751298686720764479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10123450003463164588705277 3796293751298686720764479)
        ·
          refine ⟨5694440626948030081146719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796293751298686720764479 5694440626948030081146719)
          ·
            refine ⟨8541660940422045121720079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694440626948030081146719 8541660940422045121720079)
            ·
              refine ⟨12812491410633067682580119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541660940422045121720079 12812491410633067682580119)
              ·
                refine ⟨19218737115949601523870179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12812491410633067682580119 19218737115949601523870179)
                ·
                  refine ⟨28828105673924402285805269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19218737115949601523870179 28828105673924402285805269)
                  ·
                    refine ⟨675658726732603178573561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28828105673924402285805269 675658726732603178573561)
                    ·
                      rfl

theorem cell23_3947522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_3947522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947522 prefixEnd_3947522 := by exact prefixLift 3947522
  have htrace : WordTrace (prefixWord ++ tailWord_3947522) baseStart_3947522 baseEnd_3947522 := by
    simpa [prefixWord, tailWord_3947522, baseEnd_3947522] using wordTrace_append hprefix tailTrace_3947522
  have hstable : (prefixWord ++ tailWord_3947522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947522).length < 2 ^ (prefixWord ++ tailWord_3947522).sum := by decide
  have hdescent : baseEnd_3947522 < baseStart_3947522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947578 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_3947578 : Nat := 118140960795 + 3947578 * 2 ^ 59
def prefixEnd_3947578 : Nat := 4983230072969 + 3 ^ 40 * 3947578 * 2
def baseEnd_3947578 : Nat := 675668311704820438873475

theorem tailTrace_3947578 : CollatzResearch.WordTrace tailWord_3947578 prefixEnd_3947578 675668311704820438873475 := by
  unfold tailWord_3947578
  simp only [CollatzResearch.WordTrace]
  refine ⟨35994999523151643373072847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95986665395071048994860925 35994999523151643373072847)
  ·
    refine ⟨53992499284727465059609271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35994999523151643373072847 53992499284727465059609271)
    ·
      refine ⟨80988748927091197589413907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53992499284727465059609271 80988748927091197589413907)
      ·
        refine ⟨121483123390636796384120861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80988748927091197589413907 121483123390636796384120861)
        ·
          refine ⟨45556171271488798644045323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121483123390636796384120861 45556171271488798644045323)
          ·
            refine ⟨68334256907233197966067985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45556171271488798644045323 68334256907233197966067985)
            ·
              refine ⟨51250692680424898474550989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68334256907233197966067985 51250692680424898474550989)
              ·
                refine ⟨19219009755159336927956621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51250692680424898474550989 19219009755159336927956621)
                ·
                  refine ⟨7207128658184751347983733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19219009755159336927956621 7207128658184751347983733)
                  ·
                    refine ⟨675668311704820438873475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7207128658184751347983733 675668311704820438873475)
                    ·
                      rfl

theorem cell23_3947578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_3947578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947578 prefixEnd_3947578 := by exact prefixLift 3947578
  have htrace : WordTrace (prefixWord ++ tailWord_3947578) baseStart_3947578 baseEnd_3947578 := by
    simpa [prefixWord, tailWord_3947578, baseEnd_3947578] using wordTrace_append hprefix tailTrace_3947578
  have hstable : (prefixWord ++ tailWord_3947578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947578).length < 2 ^ (prefixWord ++ tailWord_3947578).sum := by decide
  have hdescent : baseEnd_3947578 < baseStart_3947578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947602 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_3947602 : Nat := 118140960795 + 3947602 * 2 ^ 59
def prefixEnd_3947602 : Nat := 4983230072969 + 3 ^ 40 * 3947602 * 2
def baseEnd_3947602 : Nat := 2027017258650169222720315

theorem tailTrace_3947602 : CollatzResearch.WordTrace tailWord_3947602 prefixEnd_3947602 2027017258650169222720315 := by
  unfold tailWord_3947602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35995218361129906397791265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95987248963013083727443373 35995218361129906397791265)
  ·
    refine ⟨26996413770847429798343449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35995218361129906397791265 26996413770847429798343449)
    ·
      refine ⟨20247310328135572348757587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26996413770847429798343449 20247310328135572348757587)
      ·
        refine ⟨30370965492203358523136381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20247310328135572348757587 30370965492203358523136381)
        ·
          refine ⟨11389112059576259446176143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30370965492203358523136381 11389112059576259446176143)
          ·
            refine ⟨17083668089364389169264215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11389112059576259446176143 17083668089364389169264215)
            ·
              refine ⟨25625502134046583753896323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17083668089364389169264215 25625502134046583753896323)
              ·
                refine ⟨38438253201069875630844485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25625502134046583753896323 38438253201069875630844485)
                ·
                  refine ⟨7207172475200601680783341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38438253201069875630844485 7207172475200601680783341)
                  ·
                    refine ⟨2702689678200225630293753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7207172475200601680783341 2702689678200225630293753)
                    ·
                      refine ⟨2027017258650169222720315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702689678200225630293753 2027017258650169222720315)
                      ·
                        rfl

theorem cell23_3947602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_3947602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947602 prefixEnd_3947602 := by exact prefixLift 3947602
  have htrace : WordTrace (prefixWord ++ tailWord_3947602) baseStart_3947602 baseEnd_3947602 := by
    simpa [prefixWord, tailWord_3947602, baseEnd_3947602] using wordTrace_append hprefix tailTrace_3947602
  have hstable : (prefixWord ++ tailWord_3947602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947602).length < 2 ^ (prefixWord ++ tailWord_3947602).sum := by decide
  have hdescent : baseEnd_3947602 < baseStart_3947602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947628 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_3947628 : Nat := 118140960795 + 3947628 * 2 ^ 59
def prefixEnd_3947628 : Nat := 4983230072969 + 3 ^ 40 * 3947628 * 2
def baseEnd_3947628 : Nat := 2027030609147186120995195

theorem tailTrace_3947628 : CollatzResearch.WordTrace tailWord_3947628 prefixEnd_3947628 2027030609147186120995195 := by
  unfold tailWord_3947628
  simp only [CollatzResearch.WordTrace]
  refine ⟨71990910871212716015805769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95987881161616954687741025 71990910871212716015805769)
  ·
    refine ⟨53993183153409537011854327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71990910871212716015805769 53993183153409537011854327)
    ·
      refine ⟨80989774730114305517781491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53993183153409537011854327 80989774730114305517781491)
      ·
        refine ⟨121484662095171458276672237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80989774730114305517781491 121484662095171458276672237)
        ·
          refine ⟨45556748285689296853752089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121484662095171458276672237 45556748285689296853752089)
          ·
            refine ⟨34167561214266972640314067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45556748285689296853752089 34167561214266972640314067)
            ·
              refine ⟨51251341821400458960471101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34167561214266972640314067 51251341821400458960471101)
              ·
                refine ⟨19219253183025172110176663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51251341821400458960471101 19219253183025172110176663)
                ·
                  refine ⟨28828879774537758165264995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19219253183025172110176663 28828879774537758165264995)
                  ·
                    refine ⟨43243319661806637247897493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28828879774537758165264995 43243319661806637247897493)
                    ·
                      refine ⟨2027030609147186120995195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43243319661806637247897493 2027030609147186120995195)
                      ·
                        rfl

theorem cell23_3947628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_3947628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947628 prefixEnd_3947628 := by exact prefixLift 3947628
  have htrace : WordTrace (prefixWord ++ tailWord_3947628) baseStart_3947628 baseEnd_3947628 := by
    simpa [prefixWord, tailWord_3947628, baseEnd_3947628] using wordTrace_append hprefix tailTrace_3947628
  have hstable : (prefixWord ++ tailWord_3947628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947628).length < 2 ^ (prefixWord ++ tailWord_3947628).sum := by decide
  have hdescent : baseEnd_3947628 < baseStart_3947628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947632 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 5, 2, 2]
def baseStart_3947632 : Nat := 118140960795 + 3947632 * 2 ^ 59
def prefixEnd_3947632 : Nat := 4983230072969 + 3 ^ 40 * 3947632 * 2
def baseEnd_3947632 : Nat := 2027032663069804105345177

theorem tailTrace_3947632 : CollatzResearch.WordTrace tailWord_3947632 prefixEnd_3947632 2027032663069804105345177 := by
  unfold tailWord_3947632
  simp only [CollatzResearch.WordTrace]
  refine ⟨71990983817205470357378575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95987978422940627143171433 71990983817205470357378575)
  ·
    refine ⟨107986475725808205536067863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71990983817205470357378575 107986475725808205536067863)
    ·
      refine ⟨161979713588712308304101795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107986475725808205536067863 161979713588712308304101795)
      ·
        refine ⟨242969570383068462456152693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161979713588712308304101795 242969570383068462456152693)
        ·
          refine ⟨22778397223412668355264315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242969570383068462456152693 22778397223412668355264315)
          ·
            refine ⟨34167595835119002532896473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22778397223412668355264315 34167595835119002532896473)
            ·
              refine ⟨25625696876339251899672355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34167595835119002532896473 25625696876339251899672355)
              ·
                refine ⟨38438545314508877849508533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25625696876339251899672355 38438545314508877849508533)
                ·
                  refine ⟨3603613623235207298391425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38438545314508877849508533 3603613623235207298391425)
                  ·
                    refine ⟨2702710217426405473793569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3603613623235207298391425 2702710217426405473793569)
                    ·
                      refine ⟨2027032663069804105345177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702710217426405473793569 2027032663069804105345177)
                      ·
                        rfl

theorem cell23_3947632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 2, 2].length) (baseStart_3947632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947632 prefixEnd_3947632 := by exact prefixLift 3947632
  have htrace : WordTrace (prefixWord ++ tailWord_3947632) baseStart_3947632 baseEnd_3947632 := by
    simpa [prefixWord, tailWord_3947632, baseEnd_3947632] using wordTrace_append hprefix tailTrace_3947632
  have hstable : (prefixWord ++ tailWord_3947632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947632).length < 2 ^ (prefixWord ++ tailWord_3947632).sum := by decide
  have hdescent : baseEnd_3947632 < baseStart_3947632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947645 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_3947645 : Nat := 118140960795 + 3947645 * 2 ^ 59
def prefixEnd_3947645 : Nat := 4983230072969 + 3 ^ 40 * 3947645 * 2
def baseEnd_3947645 : Nat := 2027039338318312554482617

theorem tailTrace_3947645 : CollatzResearch.WordTrace tailWord_3947645 prefixEnd_3947645 2027039338318312554482617 := by
  unfold tailWord_3947645
  simp only [CollatzResearch.WordTrace]
  refine ⟨143982441783363843934980389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95988294522242562623320259 143982441783363843934980389)
  ·
    refine ⟨26996707834380720737808823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143982441783363843934980389 26996707834380720737808823)
    ·
      refine ⟨40495061751571081106713235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26996707834380720737808823 40495061751571081106713235)
      ·
        refine ⟨60742592627356621660069853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40495061751571081106713235 60742592627356621660069853)
        ·
          refine ⟨22778472235258733122526195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60742592627356621660069853 22778472235258733122526195)
          ·
            refine ⟨34167708352888099683789293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22778472235258733122526195 34167708352888099683789293)
            ·
              refine ⟨12812890632333037381420985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34167708352888099683789293 12812890632333037381420985)
              ·
                refine ⟨9609667974249778036065739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12812890632333037381420985 9609667974249778036065739)
                ·
                  refine ⟨14414501961374667054098609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9609667974249778036065739 14414501961374667054098609)
                  ·
                    refine ⟨10810876471031000290573957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14414501961374667054098609 10810876471031000290573957)
                    ·
                      refine ⟨2027039338318312554482617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10810876471031000290573957 2027039338318312554482617)
                      ·
                        rfl

theorem cell23_3947645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_3947645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947645 prefixEnd_3947645 := by exact prefixLift 3947645
  have htrace : WordTrace (prefixWord ++ tailWord_3947645) baseStart_3947645 baseEnd_3947645 := by
    simpa [prefixWord, tailWord_3947645, baseEnd_3947645] using wordTrace_append hprefix tailTrace_3947645
  have hstable : (prefixWord ++ tailWord_3947645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947645).length < 2 ^ (prefixWord ++ tailWord_3947645).sum := by decide
  have hdescent : baseEnd_3947645 < baseStart_3947645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947649 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_3947649 : Nat := 118140960795 + 3947649 * 2 ^ 59
def prefixEnd_3947649 : Nat := 4983230072969 + 3 ^ 40 * 3947649 * 2
def baseEnd_3947649 : Nat := 2027041392240930538832599

theorem tailTrace_3947649 : CollatzResearch.WordTrace tailWord_3947649 prefixEnd_3947649 2027041392240930538832599 := by
  unfold tailWord_3947649
  simp only [CollatzResearch.WordTrace]
  refine ⟨143982587675349352618126001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95988391783566235078750667 143982587675349352618126001)
  ·
    refine ⟨107986940756512014463594501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143982587675349352618126001 107986940756512014463594501)
    ·
      refine ⟨20247551391846002711923969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107986940756512014463594501 20247551391846002711923969)
      ·
        refine ⟨15185663543884502033942977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20247551391846002711923969 15185663543884502033942977)
        ·
          refine ⟨11389247657913376525457233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15185663543884502033942977 11389247657913376525457233)
          ·
            refine ⟨8541935743435032394092925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11389247657913376525457233 8541935743435032394092925)
            ·
              refine ⟨3203225903788137147784847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8541935743435032394092925 3203225903788137147784847)
              ·
                refine ⟨4804838855682205721677271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203225903788137147784847 4804838855682205721677271)
                ·
                  refine ⟨7207258283523308582515907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4804838855682205721677271 7207258283523308582515907)
                  ·
                    refine ⟨10810887425284962873773861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7207258283523308582515907 10810887425284962873773861)
                    ·
                      refine ⟨2027041392240930538832599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10810887425284962873773861 2027041392240930538832599)
                      ·
                        rfl

theorem cell23_3947649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_3947649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947649 prefixEnd_3947649 := by exact prefixLift 3947649
  have htrace : WordTrace (prefixWord ++ tailWord_3947649) baseStart_3947649 baseEnd_3947649 := by
    simpa [prefixWord, tailWord_3947649, baseEnd_3947649] using wordTrace_append hprefix tailTrace_3947649
  have hstable : (prefixWord ++ tailWord_3947649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947649).length < 2 ^ (prefixWord ++ tailWord_3947649).sum := by decide
  have hdescent : baseEnd_3947649 < baseStart_3947649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947652 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_3947652 : Nat := 118140960795 + 3947652 * 2 ^ 59
def prefixEnd_3947652 : Nat := 4983230072969 + 3 ^ 40 * 3947652 * 2
def baseEnd_3947652 : Nat := 2027042932682894027095085

theorem tailTrace_3947652 : CollatzResearch.WordTrace tailWord_3947652 prefixEnd_3947652 2027042932682894027095085 := by
  unfold tailWord_3947652
  simp only [CollatzResearch.WordTrace]
  refine ⟨71991348547169242065242605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95988464729558989420323473 71991348547169242065242605)
  ·
    refine ⟨26996755705188465774465977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71991348547169242065242605 26996755705188465774465977)
    ·
      refine ⟨20247566778891349330849483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26996755705188465774465977 20247566778891349330849483)
      ·
        refine ⟨30371350168337023996274225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20247566778891349330849483 30371350168337023996274225)
        ·
          refine ⟨22778512626252767997205669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30371350168337023996274225 22778512626252767997205669)
          ·
            refine ⟨4270971117422393999476063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22778512626252767997205669 4270971117422393999476063)
            ·
              refine ⟨6406456676133590999214095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4270971117422393999476063 6406456676133590999214095)
              ·
                refine ⟨9609685014200386498821143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6406456676133590999214095 9609685014200386498821143)
                ·
                  refine ⟨14414527521300579748231715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9609685014200386498821143 14414527521300579748231715)
                  ·
                    refine ⟨21621791281950869622347573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14414527521300579748231715 21621791281950869622347573)
                    ·
                      refine ⟨2027042932682894027095085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21621791281950869622347573 2027042932682894027095085)
                      ·
                        rfl

theorem cell23_3947652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_3947652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947652 prefixEnd_3947652 := by exact prefixLift 3947652
  have htrace : WordTrace (prefixWord ++ tailWord_3947652) baseStart_3947652 baseEnd_3947652 := by
    simpa [prefixWord, tailWord_3947652, baseEnd_3947652] using wordTrace_append hprefix tailTrace_3947652
  have hstable : (prefixWord ++ tailWord_3947652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947652).length < 2 ^ (prefixWord ++ tailWord_3947652).sum := by decide
  have hdescent : baseEnd_3947652 < baseStart_3947652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947735 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_3947735 : Nat := 118140960795 + 3947735 * 2 ^ 59
def prefixEnd_3947735 : Nat := 4983230072969 + 3 ^ 40 * 3947735 * 2
def baseEnd_3947735 : Nat := 2027085551577217202357203

theorem tailTrace_3947735 : CollatzResearch.WordTrace tailWord_3947735 prefixEnd_3947735 2027085551577217202357203 := by
  unfold tailWord_3947735
  simp only [CollatzResearch.WordTrace]
  refine ⟨143985724353037789305756659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95990482902025192870504439 143985724353037789305756659)
  ·
    refine ⟨215978586529556683958634989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143985724353037789305756659 215978586529556683958634989)
    ·
      refine ⟨80991969948583756484488121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215978586529556683958634989 80991969948583756484488121)
      ·
        refine ⟨60743977461437817363366091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80991969948583756484488121 60743977461437817363366091)
        ·
          refine ⟨91115966192156726045049137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60743977461437817363366091 91115966192156726045049137)
          ·
            refine ⟨68336974644117544533786853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91115966192156726045049137 68336974644117544533786853)
            ·
              refine ⟨12813182745772039600085035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68336974644117544533786853 12813182745772039600085035)
              ·
                refine ⟨19219774118658059400127553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12813182745772039600085035 19219774118658059400127553)
                ·
                  refine ⟨14414830588993544550095665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19219774118658059400127553 14414830588993544550095665)
                  ·
                    refine ⟨10811122941745158412571749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14414830588993544550095665 10811122941745158412571749)
                    ·
                      refine ⟨2027085551577217202357203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10811122941745158412571749 2027085551577217202357203)
                      ·
                        rfl

theorem cell23_3947735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_3947735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947735 prefixEnd_3947735 := by exact prefixLift 3947735
  have htrace : WordTrace (prefixWord ++ tailWord_3947735) baseStart_3947735 baseEnd_3947735 := by
    simpa [prefixWord, tailWord_3947735, baseEnd_3947735] using wordTrace_append hprefix tailTrace_3947735
  have hstable : (prefixWord ++ tailWord_3947735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947735).length < 2 ^ (prefixWord ++ tailWord_3947735).sum := by decide
  have hdescent : baseEnd_3947735 < baseStart_3947735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947745 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 7]
def baseStart_3947745 : Nat := 118140960795 + 3947745 * 2 ^ 59
def prefixEnd_3947745 : Nat := 4983230072969 + 3 ^ 40 * 3947745 * 2
def baseEnd_3947745 : Nat := 225232298487084684803573

theorem tailTrace_3947745 : CollatzResearch.WordTrace tailWord_3947745 prefixEnd_3947745 225232298487084684803573 := by
  unfold tailWord_3947745
  simp only [CollatzResearch.WordTrace]
  refine ⟨143986089083001561013620689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95990726055334374009080459 143986089083001561013620689)
  ·
    refine ⟨107989566812251170760215517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143986089083001561013620689 107989566812251170760215517)
    ·
      refine ⟨40496087554594189035080819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107989566812251170760215517 40496087554594189035080819)
      ·
        refine ⟨60744131331891283552621229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40496087554594189035080819 60744131331891283552621229)
        ·
          refine ⟨22779049249459231332232961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60744131331891283552621229 22779049249459231332232961)
          ·
            refine ⟨17084286937094423499174721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22779049249459231332232961 17084286937094423499174721)
            ·
              refine ⟨12813215202820817624381041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17084286937094423499174721 12813215202820817624381041)
              ·
                refine ⟨9609911402115613218285781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12813215202820817624381041 9609911402115613218285781)
                ·
                  refine ⟨225232298487084684803573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9609911402115613218285781 225232298487084684803573)
                  ·
                    rfl

theorem cell23_3947745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 7].length) (baseStart_3947745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947745 prefixEnd_3947745 := by exact prefixLift 3947745
  have htrace : WordTrace (prefixWord ++ tailWord_3947745) baseStart_3947745 baseEnd_3947745 := by
    simpa [prefixWord, tailWord_3947745, baseEnd_3947745] using wordTrace_append hprefix tailTrace_3947745
  have hstable : (prefixWord ++ tailWord_3947745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947745).length < 2 ^ (prefixWord ++ tailWord_3947745).sum := by decide
  have hdescent : baseEnd_3947745 < baseStart_3947745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947775 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 4, 5]
def baseStart_3947775 : Nat := 118140960795 + 3947775 * 2 ^ 59
def prefixEnd_3947775 : Nat := 4983230072969 + 3 ^ 40 * 3947775 * 2
def baseEnd_3947775 : Nat := 675702030267799015285673

theorem tailTrace_3947775 : CollatzResearch.WordTrace tailWord_3947775 prefixEnd_3947775 675702030267799015285673 := by
  unfold tailWord_3947775
  simp only [CollatzResearch.WordTrace]
  refine ⟨143987183272892876137212779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95991455515261917424808519 143987183272892876137212779)
  ·
    refine ⟨215980774909339314205819169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143987183272892876137212779 215980774909339314205819169)
    ·
      refine ⟨161985581182004485654364377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215980774909339314205819169 161985581182004485654364377)
      ·
        refine ⟨121489185886503364240773283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161985581182004485654364377 121489185886503364240773283)
        ·
          refine ⟨182233778829755046361159925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121489185886503364240773283 182233778829755046361159925)
          ·
            refine ⟨17084416765289535596358743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182233778829755046361159925 17084416765289535596358743)
            ·
              refine ⟨25626625147934303394538115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17084416765289535596358743 25626625147934303394538115)
              ·
                refine ⟨38439937721901455091807173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25626625147934303394538115 38439937721901455091807173)
                ·
                  refine ⟨7207488322856522829713845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38439937721901455091807173 7207488322856522829713845)
                  ·
                    refine ⟨675702030267799015285673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7207488322856522829713845 675702030267799015285673)
                    ·
                      rfl

theorem cell23_3947775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_3947775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947775 prefixEnd_3947775 := by exact prefixLift 3947775
  have htrace : WordTrace (prefixWord ++ tailWord_3947775) baseStart_3947775 baseEnd_3947775 := by
    simpa [prefixWord, tailWord_3947775, baseEnd_3947775] using wordTrace_append hprefix tailTrace_3947775
  have hstable : (prefixWord ++ tailWord_3947775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947775).length < 2 ^ (prefixWord ++ tailWord_3947775).sum := by decide
  have hdescent : baseEnd_3947775 < baseStart_3947775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947779 : List Nat := [1, 1, 1, 3, 2, 5, 3, 2, 5]
def baseStart_3947779 : Nat := 118140960795 + 3947779 * 2 ^ 59
def prefixEnd_3947779 : Nat := 4983230072969 + 3 ^ 40 * 3947779 * 2
def baseEnd_3947779 : Nat := 225234238302890558911889

theorem tailTrace_3947779 : CollatzResearch.WordTrace tailWord_3947779 prefixEnd_3947779 225234238302890558911889 := by
  unfold tailWord_3947779
  simp only [CollatzResearch.WordTrace]
  refine ⟨143987329164878384820358391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95991552776585589880238927 143987329164878384820358391)
  ·
    refine ⟨215980993747317577230537587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143987329164878384820358391 215980993747317577230537587)
    ·
      refine ⟨323971490620976365845806381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215980993747317577230537587 323971490620976365845806381)
      ·
        refine ⟨121489308982866137192177393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323971490620976365845806381 121489308982866137192177393)
        ·
          refine ⟨91116981737149602894133045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121489308982866137192177393 91116981737149602894133045)
          ·
            refine ⟨8542217037857775271324973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91116981737149602894133045 8542217037857775271324973)
            ·
              refine ⟨3203331389196665726746865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8542217037857775271324973 3203331389196665726746865)
              ·
                refine ⟨2402498541897499295060149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203331389196665726746865 2402498541897499295060149)
                ·
                  refine ⟨225234238302890558911889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2402498541897499295060149 225234238302890558911889)
                  ·
                    rfl

theorem cell23_3947779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 5].length) (baseStart_3947779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947779 prefixEnd_3947779 := by exact prefixLift 3947779
  have htrace : WordTrace (prefixWord ++ tailWord_3947779) baseStart_3947779 baseEnd_3947779 := by
    simpa [prefixWord, tailWord_3947779, baseEnd_3947779] using wordTrace_append hprefix tailTrace_3947779
  have hstable : (prefixWord ++ tailWord_3947779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947779).length < 2 ^ (prefixWord ++ tailWord_3947779).sum := by decide
  have hdescent : baseEnd_3947779 < baseStart_3947779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947785 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_3947785 : Nat := 118140960795 + 3947785 * 2 ^ 59
def prefixEnd_3947785 : Nat := 4983230072969 + 3 ^ 40 * 3947785 * 2
def baseEnd_3947785 : Nat := 2027111225609942006731973

theorem tailTrace_3947785 : CollatzResearch.WordTrace tailWord_3947785 prefixEnd_3947785 2027111225609942006731973 := by
  unfold tailWord_3947785
  simp only [CollatzResearch.WordTrace]
  refine ⟨143987548002856647845076809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95991698668571098563384539 143987548002856647845076809)
  ·
    refine ⟨107990661002142485883807607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143987548002856647845076809 107990661002142485883807607)
    ·
      refine ⟨161985991503213728825711411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107990661002142485883807607 161985991503213728825711411)
      ·
        refine ⟨242978987254820593238567117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161985991503213728825711411 242978987254820593238567117)
        ·
          refine ⟨91117120220557722464462669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242978987254820593238567117 91117120220557722464462669)
          ·
            refine ⟨34168920082709145924173501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91117120220557722464462669 34168920082709145924173501)
            ·
              refine ⟨12813345031015929721565063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34168920082709145924173501 12813345031015929721565063)
              ·
                refine ⟨19220017546523894582347595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12813345031015929721565063 19220017546523894582347595)
                ·
                  refine ⟨28830026319785841873521393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19220017546523894582347595 28830026319785841873521393)
                  ·
                    refine ⟨21622519739839381405141045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28830026319785841873521393 21622519739839381405141045)
                    ·
                      refine ⟨2027111225609942006731973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21622519739839381405141045 2027111225609942006731973)
                      ·
                        rfl

theorem cell23_3947785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_3947785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947785 prefixEnd_3947785 := by exact prefixLift 3947785
  have htrace : WordTrace (prefixWord ++ tailWord_3947785) baseStart_3947785 baseEnd_3947785 := by
    simpa [prefixWord, tailWord_3947785, baseEnd_3947785] using wordTrace_append hprefix tailTrace_3947785
  have hstable : (prefixWord ++ tailWord_3947785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947785).length < 2 ^ (prefixWord ++ tailWord_3947785).sum := by decide
  have hdescent : baseEnd_3947785 < baseStart_3947785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947830 : List Nat := [5, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_3947830 : Nat := 118140960795 + 3947830 * 2 ^ 59
def prefixEnd_3947830 : Nat := 4983230072969 + 3 ^ 40 * 3947830 * 2
def baseEnd_3947830 : Nat := 225237148026599370074363

theorem tailTrace_3947830 : CollatzResearch.WordTrace tailWord_3947830 prefixEnd_3947830 225237148026599370074363 := by
  unfold tailWord_3947830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999324330480851283154059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95992792858462413686976629 8999324330480851283154059)
  ·
    refine ⟨13498986495721276924731089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8999324330480851283154059 13498986495721276924731089)
    ·
      refine ⟨10124239871790957693548317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13498986495721276924731089 10124239871790957693548317)
      ·
        refine ⟨3796589951921609135080619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10124239871790957693548317 3796589951921609135080619)
        ·
          refine ⟨5694884927882413702620929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796589951921609135080619 5694884927882413702620929)
          ·
            refine ⟨4271163695911810276965697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5694884927882413702620929 4271163695911810276965697)
            ·
              refine ⟨3203372771933857707724273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271163695911810276965697 3203372771933857707724273)
              ·
                refine ⟨2402529578950393280793205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203372771933857707724273 2402529578950393280793205)
                ·
                  refine ⟨225237148026599370074363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2402529578950393280793205 225237148026599370074363)
                  ·
                    rfl

theorem cell23_3947830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_3947830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947830 prefixEnd_3947830 := by exact prefixLift 3947830
  have htrace : WordTrace (prefixWord ++ tailWord_3947830) baseStart_3947830 baseEnd_3947830 := by
    simpa [prefixWord, tailWord_3947830, baseEnd_3947830] using wordTrace_append hprefix tailTrace_3947830
  have hstable : (prefixWord ++ tailWord_3947830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947830).length < 2 ^ (prefixWord ++ tailWord_3947830).sum := by decide
  have hdescent : baseEnd_3947830 < baseStart_3947830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947852 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 6]
def baseStart_3947852 : Nat := 118140960795 + 3947852 * 2 ^ 59
def prefixEnd_3947852 : Nat := 4983230072969 + 3 ^ 40 * 3947852 * 2
def baseEnd_3947852 : Nat := 225238403201532582732685

theorem tailTrace_3947852 : CollatzResearch.WordTrace tailWord_3947852 prefixEnd_3947852 225238403201532582732685 := by
  unfold tailWord_3947852
  simp only [CollatzResearch.WordTrace]
  refine ⟨71994995846806959143882905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95993327795742612191843873 71994995846806959143882905)
  ·
    refine ⟨53996246885105219357912179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71994995846806959143882905 53996246885105219357912179)
    ·
      refine ⟨80994370327657829036868269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53996246885105219357912179 80994370327657829036868269)
      ·
        refine ⟨30372888872871685888825601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80994370327657829036868269 30372888872871685888825601)
        ·
          refine ⟨22779666654653764416619201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30372888872871685888825601 22779666654653764416619201)
          ·
            refine ⟨17084749990990323312464401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22779666654653764416619201 17084749990990323312464401)
            ·
              refine ⟨12813562493242742484348301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17084749990990323312464401 12813562493242742484348301)
              ·
                refine ⟨4805085934966028431630613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12813562493242742484348301 4805085934966028431630613)
                ·
                  refine ⟨225238403201532582732685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4805085934966028431630613 225238403201532582732685)
                  ·
                    rfl

theorem cell23_3947852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_3947852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947852 prefixEnd_3947852 := by exact prefixLift 3947852
  have htrace : WordTrace (prefixWord ++ tailWord_3947852) baseStart_3947852 baseEnd_3947852 := by
    simpa [prefixWord, tailWord_3947852, baseEnd_3947852] using wordTrace_append hprefix tailTrace_3947852
  have hstable : (prefixWord ++ tailWord_3947852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947852).length < 2 ^ (prefixWord ++ tailWord_3947852).sum := by decide
  have hdescent : baseEnd_3947852 < baseStart_3947852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947889 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 2, 3, 2]
def baseStart_3947889 : Nat := 118140960795 + 3947889 * 2 ^ 59
def prefixEnd_3947889 : Nat := 4983230072969 + 3 ^ 40 * 3947889 * 2
def baseEnd_3947889 : Nat := 2027164627598009599831495

theorem tailTrace_3947889 : CollatzResearch.WordTrace tailWord_3947889 prefixEnd_3947889 2027164627598009599831495 := by
  unfold tailWord_3947889
  simp only [CollatzResearch.WordTrace]
  refine ⟨143991341194479873606862721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95994227462986582404575147 143991341194479873606862721)
  ·
    refine ⟨107993505895859905205147041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143991341194479873606862721 107993505895859905205147041)
    ·
      refine ⟨80995129421894928903860281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107993505895859905205147041 80995129421894928903860281)
      ·
        refine ⟨60746347066421196677895211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80995129421894928903860281 60746347066421196677895211)
        ·
          refine ⟨91119520599631795016842817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60746347066421196677895211 91119520599631795016842817)
          ·
            refine ⟨68339640449723846262632113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91119520599631795016842817 68339640449723846262632113)
            ·
              refine ⟨51254730337292884696974085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68339640449723846262632113 51254730337292884696974085)
              ·
                refine ⟨9610261938242415880682641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51254730337292884696974085 9610261938242415880682641)
                ·
                  refine ⟨7207696453681811910511981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9610261938242415880682641 7207696453681811910511981)
                  ·
                    refine ⟨2702886170130679466441993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7207696453681811910511981 2702886170130679466441993)
                    ·
                      refine ⟨2027164627598009599831495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702886170130679466441993 2027164627598009599831495)
                      ·
                        rfl

theorem cell23_3947889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_3947889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947889 prefixEnd_3947889 := by exact prefixLift 3947889
  have htrace : WordTrace (prefixWord ++ tailWord_3947889) baseStart_3947889 baseEnd_3947889 := by
    simpa [prefixWord, tailWord_3947889, baseEnd_3947889] using wordTrace_append hprefix tailTrace_3947889
  have hstable : (prefixWord ++ tailWord_3947889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947889).length < 2 ^ (prefixWord ++ tailWord_3947889).sum := by decide
  have hdescent : baseEnd_3947889 < baseStart_3947889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947939 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 3]
def baseStart_3947939 : Nat := 118140960795 + 3947939 * 2 ^ 59
def prefixEnd_3947939 : Nat := 4983230072969 + 3 ^ 40 * 3947939 * 2
def baseEnd_3947939 : Nat := 2027190301630734404206265

theorem tailTrace_3947939 : CollatzResearch.WordTrace tailWord_3947939 prefixEnd_3947939 2027190301630734404206265 := by
  unfold tailWord_3947939
  simp only [CollatzResearch.WordTrace]
  refine ⟨143993164844298732146182871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95995443229532488097455247 143993164844298732146182871)
  ·
    refine ⟨215989747266448098219274307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143993164844298732146182871 215989747266448098219274307)
    ·
      refine ⟨323984620899672147328911461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215989747266448098219274307 323984620899672147328911461)
      ·
        refine ⟨60747116418688527624170899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323984620899672147328911461 60747116418688527624170899)
        ·
          refine ⟨91120674628032791436256349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60747116418688527624170899 91120674628032791436256349)
          ·
            refine ⟨34170252985512296788596131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91120674628032791436256349 34170252985512296788596131)
            ·
              refine ⟨51255379478268445182894197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34170252985512296788596131 51255379478268445182894197)
              ·
                refine ⟨4805191826087666735896331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51255379478268445182894197 4805191826087666735896331)
                ·
                  refine ⟨7207787739131500103844497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805191826087666735896331 7207787739131500103844497)
                  ·
                    refine ⟨5405840804348625077883373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7207787739131500103844497 5405840804348625077883373)
                    ·
                      refine ⟨2027190301630734404206265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5405840804348625077883373 2027190301630734404206265)
                      ·
                        rfl

theorem cell23_3947939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_3947939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947939 prefixEnd_3947939 := by exact prefixLift 3947939
  have htrace : WordTrace (prefixWord ++ tailWord_3947939) baseStart_3947939 baseEnd_3947939 := by
    simpa [prefixWord, tailWord_3947939, baseEnd_3947939] using wordTrace_append hprefix tailTrace_3947939
  have hstable : (prefixWord ++ tailWord_3947939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947939).length < 2 ^ (prefixWord ++ tailWord_3947939).sum := by decide
  have hdescent : baseEnd_3947939 < baseStart_3947939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947949 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3947949 : Nat := 118140960795 + 3947949 * 2 ^ 59
def prefixEnd_3947949 : Nat := 4983230072969 + 3 ^ 40 * 3947949 * 2
def baseEnd_3947949 : Nat := 2027195436437279365081219

theorem tailTrace_3947949 : CollatzResearch.WordTrace tailWord_3947949 prefixEnd_3947949 2027195436437279365081219 := by
  unfold tailWord_3947949
  simp only [CollatzResearch.WordTrace]
  refine ⟨143993529574262503854046901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95995686382841669236031267 143993529574262503854046901)
  ·
    refine ⟨13499393397587109736316897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143993529574262503854046901 13499393397587109736316897)
    ·
      refine ⟨10124545048190332302237673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13499393397587109736316897 10124545048190332302237673)
      ·
        refine ⟨7593408786142749226678255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10124545048190332302237673 7593408786142749226678255)
        ·
          refine ⟨11390113179214123840017383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7593408786142749226678255 11390113179214123840017383)
          ·
            refine ⟨17085169768821185760026075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11390113179214123840017383 17085169768821185760026075)
            ·
              refine ⟨25627754653231778640039113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17085169768821185760026075 25627754653231778640039113)
              ·
                refine ⟨19220815989923833980029335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25627754653231778640039113 19220815989923833980029335)
                ·
                  refine ⟨28831223984885750970044003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19220815989923833980029335 28831223984885750970044003)
                  ·
                    refine ⟨43246835977328626455066005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28831223984885750970044003 43246835977328626455066005)
                    ·
                      refine ⟨2027195436437279365081219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43246835977328626455066005 2027195436437279365081219)
                      ·
                        rfl

theorem cell23_3947949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3947949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947949 prefixEnd_3947949 := by exact prefixLift 3947949
  have htrace : WordTrace (prefixWord ++ tailWord_3947949) baseStart_3947949 baseEnd_3947949 := by
    simpa [prefixWord, tailWord_3947949, baseEnd_3947949] using wordTrace_append hprefix tailTrace_3947949
  have hstable : (prefixWord ++ tailWord_3947949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947949).length < 2 ^ (prefixWord ++ tailWord_3947949).sum := by decide
  have hdescent : baseEnd_3947949 < baseStart_3947949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947952 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 3]
def baseStart_3947952 : Nat := 118140960795 + 3947952 * 2 ^ 59
def prefixEnd_3947952 : Nat := 4983230072969 + 3 ^ 40 * 3947952 * 2
def baseEnd_3947952 : Nat := 2027196976879242853343705

theorem tailTrace_3947952 : CollatzResearch.WordTrace tailWord_3947952 prefixEnd_3947952 2027196976879242853343705 := by
  unfold tailWord_3947952
  simp only [CollatzResearch.WordTrace]
  refine ⟨71996819496625817683203055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95995759328834423577604073 71996819496625817683203055)
  ·
    refine ⟨107995229244938726524804583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71996819496625817683203055 107995229244938726524804583)
    ·
      refine ⟨161992843867408089787206875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107995229244938726524804583 161992843867408089787206875)
      ·
        refine ⟨242989265801112134680810313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161992843867408089787206875 242989265801112134680810313)
        ·
          refine ⟨182241949350834101010607735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242989265801112134680810313 182241949350834101010607735)
          ·
            refine ⟨273362924026251151515911603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182241949350834101010607735 273362924026251151515911603)
            ·
              refine ⟨410044386039376727273867405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273362924026251151515911603 410044386039376727273867405)
              ·
                refine ⟨153766644764766272727700277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410044386039376727273867405 153766644764766272727700277)
                ·
                  refine ⟨14415622946696838068221901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153766644764766272727700277 14415622946696838068221901)
                  ·
                    refine ⟨5405858605011314275583213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14415622946696838068221901 5405858605011314275583213)
                    ·
                      refine ⟨2027196976879242853343705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5405858605011314275583213 2027196976879242853343705)
                      ·
                        rfl

theorem cell23_3947952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_3947952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947952 prefixEnd_3947952 := by exact prefixLift 3947952
  have htrace : WordTrace (prefixWord ++ tailWord_3947952) baseStart_3947952 baseEnd_3947952 := by
    simpa [prefixWord, tailWord_3947952, baseEnd_3947952] using wordTrace_append hprefix tailTrace_3947952
  have hstable : (prefixWord ++ tailWord_3947952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947952).length < 2 ^ (prefixWord ++ tailWord_3947952).sum := by decide
  have hdescent : baseEnd_3947952 < baseStart_3947952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947982 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_3947982 : Nat := 118140960795 + 3947982 * 2 ^ 59
def prefixEnd_3947982 : Nat := 4983230072969 + 3 ^ 40 * 3947982 * 2
def baseEnd_3947982 : Nat := 2027212381298877735968567

theorem tailTrace_3947982 : CollatzResearch.WordTrace tailWord_3947982 prefixEnd_3947982 2027212381298877735968567 := by
  unfold tailWord_3947982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17999341647892868811249775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95996488788761966993332133 17999341647892868811249775)
  ·
    refine ⟨26999012471839303216874663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17999341647892868811249775 26999012471839303216874663)
    ·
      refine ⟨40498518707758954825311995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26999012471839303216874663 40498518707758954825311995)
      ·
        refine ⟨60747778061638432237967993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40498518707758954825311995 60747778061638432237967993)
        ·
          refine ⟨45560833546228824178475995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60747778061638432237967993 45560833546228824178475995)
          ·
            refine ⟨68341250319343236267713993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45560833546228824178475995 68341250319343236267713993)
            ·
              refine ⟨51255937739507427200785495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68341250319343236267713993 51255937739507427200785495)
              ·
                refine ⟨76883906609261140801178243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51255937739507427200785495 76883906609261140801178243)
                ·
                  refine ⟨115325859913891711201767365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76883906609261140801178243 115325859913891711201767365)
                  ·
                    refine ⟨21623598733854695850331381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115325859913891711201767365 21623598733854695850331381)
                    ·
                      refine ⟨2027212381298877735968567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21623598733854695850331381 2027212381298877735968567)
                      ·
                        rfl

theorem cell23_3947982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_3947982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947982 prefixEnd_3947982 := by exact prefixLift 3947982
  have htrace : WordTrace (prefixWord ++ tailWord_3947982) baseStart_3947982 baseEnd_3947982 := by
    simpa [prefixWord, tailWord_3947982, baseEnd_3947982] using wordTrace_append hprefix tailTrace_3947982
  have hstable : (prefixWord ++ tailWord_3947982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947982).length < 2 ^ (prefixWord ++ tailWord_3947982).sum := by decide
  have hdescent : baseEnd_3947982 < baseStart_3947982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3947990 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_3947990 : Nat := 118140960795 + 3947990 * 2 ^ 59
def prefixEnd_3947990 : Nat := 4983230072969 + 3 ^ 40 * 3947990 * 2
def baseEnd_3947990 : Nat := 2027216489144113704668531

theorem tailTrace_3947990 : CollatzResearch.WordTrace tailWord_3947990 prefixEnd_3947990 2027216489144113704668531 := by
  unfold tailWord_3947990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999689060444622991018089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95996683311409311904192949 8999689060444622991018089)
  ·
    refine ⟨6749766795333467243263567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8999689060444622991018089 6749766795333467243263567)
    ·
      refine ⟨10124650193000200864895351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6749766795333467243263567 10124650193000200864895351)
      ·
        refine ⟨15186975289500301297343027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10124650193000200864895351 15186975289500301297343027)
        ·
          refine ⟨22780462934250451946014541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15186975289500301297343027 22780462934250451946014541)
          ·
            refine ⟨8542673600343919479755453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22780462934250451946014541 8542673600343919479755453)
            ·
              refine ⟨3203502600128969804908295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8542673600343919479755453 3203502600128969804908295)
              ·
                refine ⟨4805253900193454707362443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203502600128969804908295 4805253900193454707362443)
                ·
                  refine ⟨7207880850290182061043665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805253900193454707362443 7207880850290182061043665)
                  ·
                    refine ⟨5405910637717636545782749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7207880850290182061043665 5405910637717636545782749)
                    ·
                      refine ⟨2027216489144113704668531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5405910637717636545782749 2027216489144113704668531)
                      ·
                        rfl

theorem cell23_3947990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_3947990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3947990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3947990 prefixEnd_3947990 := by exact prefixLift 3947990
  have htrace : WordTrace (prefixWord ++ tailWord_3947990) baseStart_3947990 baseEnd_3947990 := by
    simpa [prefixWord, tailWord_3947990, baseEnd_3947990] using wordTrace_append hprefix tailTrace_3947990
  have hstable : (prefixWord ++ tailWord_3947990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3947990).length < 2 ^ (prefixWord ++ tailWord_3947990).sum := by decide
  have hdescent : baseEnd_3947990 < baseStart_3947990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3947990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948003 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3948003 : Nat := 118140960795 + 3948003 * 2 ^ 59
def prefixEnd_3948003 : Nat := 4983230072969 + 3 ^ 40 * 3948003 * 2
def baseEnd_3948003 : Nat := 2027223164392622153805971

theorem tailTrace_3948003 : CollatzResearch.WordTrace tailWord_3948003 prefixEnd_3948003 2027223164392622153805971 := by
  unfold tailWord_3948003
  simp only [CollatzResearch.WordTrace]
  refine ⟨143995499116066871076512663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95996999410711247384341775 143995499116066871076512663)
  ·
    refine ⟨215993248674100306614768995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143995499116066871076512663 215993248674100306614768995)
    ·
      refine ⟨323989873011150459922153493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215993248674100306614768995 323989873011150459922153493)
      ·
        refine ⟨15187025297397677808850945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 323989873011150459922153493 15187025297397677808850945)
        ·
          refine ⟨11390268973048258356638209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15187025297397677808850945 11390268973048258356638209)
          ·
            refine ⟨8542701729786193767478657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11390268973048258356638209 8542701729786193767478657)
            ·
              refine ⟨6407026297339645325608993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8542701729786193767478657 6407026297339645325608993)
              ·
                refine ⟨4805269723004733994206745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6407026297339645325608993 4805269723004733994206745)
                ·
                  refine ⟨3603952292253550495655059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4805269723004733994206745 3603952292253550495655059)
                  ·
                    refine ⟨5405928438380325743482589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3603952292253550495655059 5405928438380325743482589)
                    ·
                      refine ⟨2027223164392622153805971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5405928438380325743482589 2027223164392622153805971)
                      ·
                        rfl

theorem cell23_3948003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3948003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948003 prefixEnd_3948003 := by exact prefixLift 3948003
  have htrace : WordTrace (prefixWord ++ tailWord_3948003) baseStart_3948003 baseEnd_3948003 := by
    simpa [prefixWord, tailWord_3948003, baseEnd_3948003] using wordTrace_append hprefix tailTrace_3948003
  have hstable : (prefixWord ++ tailWord_3948003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948003).length < 2 ^ (prefixWord ++ tailWord_3948003).sum := by decide
  have hdescent : baseEnd_3948003 < baseStart_3948003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948012 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_3948012 : Nat := 118140960795 + 3948012 * 2 ^ 59
def prefixEnd_3948012 : Nat := 4983230072969 + 3 ^ 40 * 3948012 * 2
def baseEnd_3948012 : Nat := 2027227785718512618593429

theorem tailTrace_3948012 : CollatzResearch.WordTrace tailWord_3948012 prefixEnd_3948012 2027227785718512618593429 := by
  unfold tailWord_3948012
  simp only [CollatzResearch.WordTrace]
  refine ⟨71997913686517132806795145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95997218248689510409060193 71997913686517132806795145)
  ·
    refine ⟨53998435264887849605096359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71997913686517132806795145 53998435264887849605096359)
    ·
      refine ⟨80997652897331774407644539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53998435264887849605096359 80997652897331774407644539)
      ·
        refine ⟨121496479345997661611466809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80997652897331774407644539 121496479345997661611466809)
        ·
          refine ⟨91122359509498246208600107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121496479345997661611466809 91122359509498246208600107)
          ·
            refine ⟨136683539264247369312900161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91122359509498246208600107 136683539264247369312900161)
            ·
              refine ⟨102512654448185526984675121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136683539264247369312900161 102512654448185526984675121)
              ·
                refine ⟨76884490836139145238506341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102512654448185526984675121 76884490836139145238506341)
                ·
                  refine ⟨14415842031776089732219939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76884490836139145238506341 14415842031776089732219939)
                  ·
                    refine ⟨21623763047664134598329909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14415842031776089732219939 21623763047664134598329909)
                    ·
                      refine ⟨2027227785718512618593429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21623763047664134598329909 2027227785718512618593429)
                      ·
                        rfl

theorem cell23_3948012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_3948012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948012 prefixEnd_3948012 := by exact prefixLift 3948012
  have htrace : WordTrace (prefixWord ++ tailWord_3948012) baseStart_3948012 baseEnd_3948012 := by
    simpa [prefixWord, tailWord_3948012, baseEnd_3948012] using wordTrace_append hprefix tailTrace_3948012
  have hstable : (prefixWord ++ tailWord_3948012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948012).length < 2 ^ (prefixWord ++ tailWord_3948012).sum := by decide
  have hdescent : baseEnd_3948012 < baseStart_3948012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948026 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2]
def baseStart_3948026 : Nat := 118140960795 + 3948026 * 2 ^ 59
def prefixEnd_3948026 : Nat := 4983230072969 + 3 ^ 40 * 3948026 * 2
def baseEnd_3948026 : Nat := 2027234974447675563818365

theorem tailTrace_3948026 : CollatzResearch.WordTrace tailWord_3948026 prefixEnd_3948026 2027234974447675563818365 := by
  unfold tailWord_3948026
  simp only [CollatzResearch.WordTrace]
  refine ⟨35999084498745886501149983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95997558663322364003066621 35999084498745886501149983)
  ·
    refine ⟨53998626748118829751724975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35999084498745886501149983 53998626748118829751724975)
    ·
      refine ⟨80997940122178244627587463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53998626748118829751724975 80997940122178244627587463)
      ·
        refine ⟨121496910183267366941381195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80997940122178244627587463 121496910183267366941381195)
        ·
          refine ⟨182245365274901050412071793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121496910183267366941381195 182245365274901050412071793)
          ·
            refine ⟨136684023956175787809053845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182245365274901050412071793 136684023956175787809053845)
            ·
              refine ⟨6407063622945740053549399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136684023956175787809053845 6407063622945740053549399)
              ·
                refine ⟨9610595434418610080324099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6407063622945740053549399 9610595434418610080324099)
                ·
                  refine ⟨14415893151627915120486149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9610595434418610080324099 14415893151627915120486149)
                  ·
                    refine ⟨2702979965930234085091153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14415893151627915120486149 2702979965930234085091153)
                    ·
                      refine ⟨2027234974447675563818365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2702979965930234085091153 2027234974447675563818365)
                      ·
                        rfl

theorem cell23_3948026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_3948026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948026 prefixEnd_3948026 := by exact prefixLift 3948026
  have htrace : WordTrace (prefixWord ++ tailWord_3948026) baseStart_3948026 baseEnd_3948026 := by
    simpa [prefixWord, tailWord_3948026, baseEnd_3948026] using wordTrace_append hprefix tailTrace_3948026
  have hstable : (prefixWord ++ tailWord_3948026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948026).length < 2 ^ (prefixWord ++ tailWord_3948026).sum := by decide
  have hdescent : baseEnd_3948026 < baseStart_3948026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948066 : List Nat := [3, 3, 1, 1, 1, 1, 4, 4, 5]
def baseStart_3948066 : Nat := 118140960795 + 3948066 * 2 ^ 59
def prefixEnd_3948066 : Nat := 4983230072969 + 3 ^ 40 * 3948066 * 2
def baseEnd_3948066 : Nat := 225250612630428378590909

theorem tailTrace_3948066 : CollatzResearch.WordTrace tailWord_3948066 prefixEnd_3948066 225250612630428378590909 := by
  unfold tailWord_3948066
  simp only [CollatzResearch.WordTrace]
  refine ⟨35999449228709658209014013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95998531276559088557370701 35999449228709658209014013)
  ·
    refine ⟨13499793460766121828380255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35999449228709658209014013 13499793460766121828380255)
    ·
      refine ⟨20249690191149182742570383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13499793460766121828380255 20249690191149182742570383)
      ·
        refine ⟨30374535286723774113855575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20249690191149182742570383 30374535286723774113855575)
        ·
          refine ⟨45561802930085661170783363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30374535286723774113855575 45561802930085661170783363)
          ·
            refine ⟨68342704395128491756175045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45561802930085661170783363 68342704395128491756175045)
            ·
              refine ⟨12814257074086592204282821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68342704395128491756175045 12814257074086592204282821)
              ·
                refine ⟨2402673201391236038303029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12814257074086592204282821 2402673201391236038303029)
                ·
                  refine ⟨225250612630428378590909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2402673201391236038303029 225250612630428378590909)
                  ·
                    rfl

theorem cell23_3948066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_3948066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948066 prefixEnd_3948066 := by exact prefixLift 3948066
  have htrace : WordTrace (prefixWord ++ tailWord_3948066) baseStart_3948066 baseEnd_3948066 := by
    simpa [prefixWord, tailWord_3948066, baseEnd_3948066] using wordTrace_append hprefix tailTrace_3948066
  have hstable : (prefixWord ++ tailWord_3948066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948066).length < 2 ^ (prefixWord ++ tailWord_3948066).sum := by decide
  have hdescent : baseEnd_3948066 < baseStart_3948066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948116 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3948116 : Nat := 118140960795 + 3948116 * 2 ^ 59
def prefixEnd_3948116 : Nat := 4983230072969 + 3 ^ 40 * 3948116 * 2
def baseEnd_3948116 : Nat := 2027281187706580211692951

theorem tailTrace_3948116 : CollatzResearch.WordTrace tailWord_3948116 prefixEnd_3948116 2027281187706580211692951 := by
  unfold tailWord_3948116
  simp only [CollatzResearch.WordTrace]
  refine ⟨71999810282328745687688101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95999747043104994250250801 71999810282328745687688101)
  ·
    refine ⟨13499964427936639816441519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71999810282328745687688101 13499964427936639816441519)
    ·
      refine ⟨20249946641904959724662279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13499964427936639816441519 20249946641904959724662279)
      ·
        refine ⟨30374919962857439586993419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20249946641904959724662279 30374919962857439586993419)
        ·
          refine ⟨45562379944286159380490129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30374919962857439586993419 45562379944286159380490129)
          ·
            refine ⟨34171784958214619535367597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45562379944286159380490129 34171784958214619535367597)
            ·
              refine ⟨12814419359330482325762849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34171784958214619535367597 12814419359330482325762849)
              ·
                refine ⟨9610814519497861744322137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12814419359330482325762849 9610814519497861744322137)
                ·
                  refine ⟨7208110889623396308241603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9610814519497861744322137 7208110889623396308241603)
                  ·
                    refine ⟨10812166334435094462362405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7208110889623396308241603 10812166334435094462362405)
                    ·
                      refine ⟨2027281187706580211692951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10812166334435094462362405 2027281187706580211692951)
                      ·
                        rfl

theorem cell23_3948116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3948116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948116 prefixEnd_3948116 := by exact prefixLift 3948116
  have htrace : WordTrace (prefixWord ++ tailWord_3948116) baseStart_3948116 baseEnd_3948116 := by
    simpa [prefixWord, tailWord_3948116, baseEnd_3948116] using wordTrace_append hprefix tailTrace_3948116
  have hstable : (prefixWord ++ tailWord_3948116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948116).length < 2 ^ (prefixWord ++ tailWord_3948116).sum := by decide
  have hdescent : baseEnd_3948116 < baseStart_3948116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948220 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_3948220 : Nat := 118140960795 + 3948220 * 2 ^ 59
def prefixEnd_3948220 : Nat := 4983230072969 + 3 ^ 40 * 3948220 * 2
def baseEnd_3948220 : Nat := 675778196564882601597491

theorem tailTrace_3948220 : CollatzResearch.WordTrace tailWord_3948220 prefixEnd_3948220 675778196564882601597491 := by
  unfold tailWord_3948220
  simp only [CollatzResearch.WordTrace]
  refine ⟨72001706878140358568581057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96002275837520478091441409 72001706878140358568581057)
  ·
    refine ⟨54001280158605268926435793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72001706878140358568581057 54001280158605268926435793)
    ·
      refine ⟨40500960118953951694826845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54001280158605268926435793 40500960118953951694826845)
      ·
        refine ⟨15187860044607731885560067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40500960118953951694826845 15187860044607731885560067)
        ·
          refine ⟨22781790066911597828340101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15187860044607731885560067 22781790066911597828340101)
          ·
            refine ⟨4271585637545924592813769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22781790066911597828340101 4271585637545924592813769)
            ·
              refine ⟨3203689228159443444610327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271585637545924592813769 3203689228159443444610327)
              ·
                refine ⟨4805533842239165166915491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203689228159443444610327 4805533842239165166915491)
                ·
                  refine ⟨7208300763358747750373237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805533842239165166915491 7208300763358747750373237)
                  ·
                    refine ⟨675778196564882601597491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7208300763358747750373237 675778196564882601597491)
                    ·
                      rfl

theorem cell23_3948220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_3948220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948220 prefixEnd_3948220 := by exact prefixLift 3948220
  have htrace : WordTrace (prefixWord ++ tailWord_3948220) baseStart_3948220 baseEnd_3948220 := by
    simpa [prefixWord, tailWord_3948220, baseEnd_3948220] using wordTrace_append hprefix tailTrace_3948220
  have hstable : (prefixWord ++ tailWord_3948220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948220).length < 2 ^ (prefixWord ++ tailWord_3948220).sum := by decide
  have hdescent : baseEnd_3948220 < baseStart_3948220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948223 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 5, 2, 2]
def baseStart_3948223 : Nat := 118140960795 + 3948223 * 2 ^ 59
def prefixEnd_3948223 : Nat := 4983230072969 + 3 ^ 40 * 3948223 * 2
def baseEnd_3948223 : Nat := 2027336130136611293054959

theorem tailTrace_3948223 : CollatzResearch.WordTrace tailWord_3948223 prefixEnd_3948223 2027336130136611293054959 := by
  unfold tailWord_3948223
  simp only [CollatzResearch.WordTrace]
  refine ⟨144003523175269848649521323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96002348783513232433014215 144003523175269848649521323)
  ·
    refine ⟨216005284762904772974281985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144003523175269848649521323 216005284762904772974281985)
    ·
      refine ⟨162003963572178579730711489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216005284762904772974281985 162003963572178579730711489)
      ·
        refine ⟨121502972679133934798033617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162003963572178579730711489 121502972679133934798033617)
        ·
          refine ⟨91127229509350451098525213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121502972679133934798033617 91127229509350451098525213)
          ·
            refine ⟨34172711066006419161946955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91127229509350451098525213 34172711066006419161946955)
            ·
              refine ⟨51259066599009628742920433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34172711066006419161946955 51259066599009628742920433)
              ·
                refine ⟨38444299949257221557190325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51259066599009628742920433 38444299949257221557190325)
                ·
                  refine ⟨3604153120242864520986593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38444299949257221557190325 3604153120242864520986593)
                  ·
                    refine ⟨2703114840182148390739945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3604153120242864520986593 2703114840182148390739945)
                    ·
                      refine ⟨2027336130136611293054959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703114840182148390739945 2027336130136611293054959)
                      ·
                        rfl

theorem cell23_3948223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_3948223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948223 prefixEnd_3948223 := by exact prefixLift 3948223
  have htrace : WordTrace (prefixWord ++ tailWord_3948223) baseStart_3948223 baseEnd_3948223 := by
    simpa [prefixWord, tailWord_3948223, baseEnd_3948223] using wordTrace_append hprefix tailTrace_3948223
  have hstable : (prefixWord ++ tailWord_3948223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948223).length < 2 ^ (prefixWord ++ tailWord_3948223).sum := by decide
  have hdescent : baseEnd_3948223 < baseStart_3948223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948250 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_3948250 : Nat := 118140960795 + 3948250 * 2 ^ 59
def prefixEnd_3948250 : Nat := 4983230072969 + 3 ^ 40 * 3948250 * 2
def baseEnd_3948250 : Nat := 675783331371427562472445

theorem tailTrace_3948250 : CollatzResearch.WordTrace tailWord_3948250 prefixEnd_3948250 675783331371427562472445 := by
  unfold tailWord_3948250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36001126986543008065188551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96003005297448021507169469 36001126986543008065188551)
  ·
    refine ⟨54001690479814512097782827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36001126986543008065188551 54001690479814512097782827)
    ·
      refine ⟨81002535719721768146674241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54001690479814512097782827 81002535719721768146674241)
      ·
        refine ⟨60751901789791326110005681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81002535719721768146674241 60751901789791326110005681)
        ·
          refine ⟨45563926342343494582504261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60751901789791326110005681 45563926342343494582504261)
          ·
            refine ⟨8543236189189405234219549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45563926342343494582504261 8543236189189405234219549)
            ·
              refine ⟨3203713570946026962832331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8543236189189405234219549 3203713570946026962832331)
              ·
                refine ⟨4805570356419040444248497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203713570946026962832331 4805570356419040444248497)
                ·
                  refine ⟨3604177767314280333186373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4805570356419040444248497 3604177767314280333186373)
                  ·
                    refine ⟨675783331371427562472445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3604177767314280333186373 675783331371427562472445)
                    ·
                      rfl

theorem cell23_3948250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_3948250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948250 prefixEnd_3948250 := by exact prefixLift 3948250
  have htrace : WordTrace (prefixWord ++ tailWord_3948250) baseStart_3948250 baseEnd_3948250 := by
    simpa [prefixWord, tailWord_3948250, baseEnd_3948250] using wordTrace_append hprefix tailTrace_3948250
  have hstable : (prefixWord ++ tailWord_3948250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948250).length < 2 ^ (prefixWord ++ tailWord_3948250).sum := by decide
  have hdescent : baseEnd_3948250 < baseStart_3948250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948263 : List Nat := [1, 1, 5, 4, 1, 1, 1, 9]
def baseStart_3948263 : Nat := 118140960795 + 3948263 * 2 ^ 59
def prefixEnd_3948263 : Nat := 4983230072969 + 3 ^ 40 * 3948263 * 2
def baseEnd_3948263 : Nat := 75087284050473745798325

theorem tailTrace_3948263 : CollatzResearch.WordTrace tailWord_3948263 prefixEnd_3948263 75087284050473745798325 := by
  unfold tailWord_3948263
  simp only [CollatzResearch.WordTrace]
  refine ⟨144004982095124935480977443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96003321396749956987318295 144004982095124935480977443)
  ·
    refine ⟨216007473142687403221466165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144004982095124935480977443 216007473142687403221466165)
    ·
      refine ⟨20250700607126944052012453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216007473142687403221466165 20250700607126944052012453)
      ·
        refine ⟨3797006363836302009752335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20250700607126944052012453 3797006363836302009752335)
        ·
          refine ⟨5695509545754453014628503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3797006363836302009752335 5695509545754453014628503)
          ·
            refine ⟨8543264318631679521942755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695509545754453014628503 8543264318631679521942755)
            ·
              refine ⟨12814896477947519282914133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8543264318631679521942755 12814896477947519282914133)
              ·
                refine ⟨75087284050473745798325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12814896477947519282914133 75087284050473745798325)
                ·
                  rfl

theorem cell23_3948263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 9].length) (baseStart_3948263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948263 prefixEnd_3948263 := by exact prefixLift 3948263
  have htrace : WordTrace (prefixWord ++ tailWord_3948263) baseStart_3948263 baseEnd_3948263 := by
    simpa [prefixWord, tailWord_3948263, baseEnd_3948263] using wordTrace_append hprefix tailTrace_3948263
  have hstable : (prefixWord ++ tailWord_3948263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948263).length < 2 ^ (prefixWord ++ tailWord_3948263).sum := by decide
  have hdescent : baseEnd_3948263 < baseStart_3948263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948273 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 3]
def baseStart_3948273 : Nat := 118140960795 + 3948273 * 2 ^ 59
def prefixEnd_3948273 : Nat := 4983230072969 + 3 ^ 40 * 3948273 * 2
def baseEnd_3948273 : Nat := 2027361804169336097429729

theorem tailTrace_3948273 : CollatzResearch.WordTrace tailWord_3948273 prefixEnd_3948273 2027361804169336097429729 := by
  unfold tailWord_3948273
  simp only [CollatzResearch.WordTrace]
  refine ⟨144005346825088707188841473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96003564550059138125894315 144005346825088707188841473)
  ·
    refine ⟨108004010118816530391631105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144005346825088707188841473 108004010118816530391631105)
    ·
      refine ⟨81003007589112397793723329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108004010118816530391631105 81003007589112397793723329)
      ·
        refine ⟨60752255691834298345292497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81003007589112397793723329 60752255691834298345292497)
        ·
          refine ⟨45564191768875723758969373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60752255691834298345292497 45564191768875723758969373)
          ·
            refine ⟨17086571913328396409613515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45564191768875723758969373 17086571913328396409613515)
            ·
              refine ⟨25629857869992594614420273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17086571913328396409613515 25629857869992594614420273)
              ·
                refine ⟨19222393402494445960815205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25629857869992594614420273 19222393402494445960815205)
                ·
                  refine ⟨3604198762967708617652851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19222393402494445960815205 3604198762967708617652851)
                  ·
                    refine ⟨5406298144451562926479277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3604198762967708617652851 5406298144451562926479277)
                    ·
                      refine ⟨2027361804169336097429729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5406298144451562926479277 2027361804169336097429729)
                      ·
                        rfl

theorem cell23_3948273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_3948273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948273 prefixEnd_3948273 := by exact prefixLift 3948273
  have htrace : WordTrace (prefixWord ++ tailWord_3948273) baseStart_3948273 baseEnd_3948273 := by
    simpa [prefixWord, tailWord_3948273, baseEnd_3948273] using wordTrace_append hprefix tailTrace_3948273
  have hstable : (prefixWord ++ tailWord_3948273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948273).length < 2 ^ (prefixWord ++ tailWord_3948273).sum := by decide
  have hdescent : baseEnd_3948273 < baseStart_3948273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948290 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_3948290 : Nat := 118140960795 + 3948290 * 2 ^ 59
def prefixEnd_3948290 : Nat := 4983230072969 + 3 ^ 40 * 3948290 * 2
def baseEnd_3948290 : Nat := 2027370533340462530917151

theorem tailTrace_3948290 : CollatzResearch.WordTrace tailWord_3948290 prefixEnd_3948290 2027370533340462530917151 := by
  unfold tailWord_3948290
  simp only [CollatzResearch.WordTrace]
  refine ⟨36001491716506779773052581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96003977910684746061473549 36001491716506779773052581)
  ·
    refine ⟨6750279696845021207447359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36001491716506779773052581 6750279696845021207447359)
    ·
      refine ⟨10125419545267531811171039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6750279696845021207447359 10125419545267531811171039)
      ·
        refine ⟨15188129317901297716756559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10125419545267531811171039 15188129317901297716756559)
        ·
          refine ⟨22782193976851946575134839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15188129317901297716756559 22782193976851946575134839)
          ·
            refine ⟨34173290965277919862702259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22782193976851946575134839 34173290965277919862702259)
            ·
              refine ⟨51259936447916879794053389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34173290965277919862702259 51259936447916879794053389)
              ·
                refine ⟨19222476167968829922770021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51259936447916879794053389 19222476167968829922770021)
                ·
                  refine ⟨3604214281494155610519379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19222476167968829922770021 3604214281494155610519379)
                  ·
                    refine ⟨5406321422241233415779069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3604214281494155610519379 5406321422241233415779069)
                    ·
                      refine ⟨2027370533340462530917151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5406321422241233415779069 2027370533340462530917151)
                      ·
                        rfl

theorem cell23_3948290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_3948290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948290 prefixEnd_3948290 := by exact prefixLift 3948290
  have htrace : WordTrace (prefixWord ++ tailWord_3948290) baseStart_3948290 baseEnd_3948290 := by
    simpa [prefixWord, tailWord_3948290, baseEnd_3948290] using wordTrace_append hprefix tailTrace_3948290
  have hstable : (prefixWord ++ tailWord_3948290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948290).length < 2 ^ (prefixWord ++ tailWord_3948290).sum := by decide
  have hdescent : baseEnd_3948290 < baseStart_3948290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948296 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3948296 : Nat := 118140960795 + 3948296 * 2 ^ 59
def prefixEnd_3948296 : Nat := 4983230072969 + 3 ^ 40 * 3948296 * 2
def baseEnd_3948296 : Nat := 2027373614224389507442123

theorem tailTrace_3948296 : CollatzResearch.WordTrace tailWord_3948296 prefixEnd_3948296 2027373614224389507442123 := by
  unfold tailWord_3948296
  simp only [CollatzResearch.WordTrace]
  refine ⟨72003092852002691058464371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96004123802670254744619161 72003092852002691058464371)
  ·
    refine ⟨108004639278004036587696557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72003092852002691058464371 108004639278004036587696557)
    ·
      refine ⟨40501739729251513720386209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108004639278004036587696557 40501739729251513720386209)
      ·
        refine ⟨30376304796938635290289657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40501739729251513720386209 30376304796938635290289657)
        ·
          refine ⟨22782228597703976467717243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30376304796938635290289657 22782228597703976467717243)
          ·
            refine ⟨34173342896555964701575865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22782228597703976467717243 34173342896555964701575865)
            ·
              refine ⟨25630007172416973526181899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34173342896555964701575865 25630007172416973526181899)
              ·
                refine ⟨38445010758625460289272849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25630007172416973526181899 38445010758625460289272849)
                ·
                  refine ⟨28833758068969095216954637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38445010758625460289272849 28833758068969095216954637)
                  ·
                    refine ⟨10812659275863410706357989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28833758068969095216954637 10812659275863410706357989)
                    ·
                      refine ⟨2027373614224389507442123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10812659275863410706357989 2027373614224389507442123)
                      ·
                        rfl

theorem cell23_3948296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3948296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948296 prefixEnd_3948296 := by exact prefixLift 3948296
  have htrace : WordTrace (prefixWord ++ tailWord_3948296) baseStart_3948296 baseEnd_3948296 := by
    simpa [prefixWord, tailWord_3948296, baseEnd_3948296] using wordTrace_append hprefix tailTrace_3948296
  have hstable : (prefixWord ++ tailWord_3948296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948296).length < 2 ^ (prefixWord ++ tailWord_3948296).sum := by decide
  have hdescent : baseEnd_3948296 < baseStart_3948296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948301 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3948301 : Nat := 118140960795 + 3948301 * 2 ^ 59
def prefixEnd_3948301 : Nat := 4983230072969 + 3 ^ 40 * 3948301 * 2
def baseEnd_3948301 : Nat := 675792060542553995959867

theorem tailTrace_3948301 : CollatzResearch.WordTrace tailWord_3948301 prefixEnd_3948301 675792060542553995959867 := by
  unfold tailWord_3948301
  simp only [CollatzResearch.WordTrace]
  refine ⟨144006368068987267970860757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96004245379324845313907171 144006368068987267970860757)
  ·
    refine ⟨3375149251616889093067049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 144006368068987267970860757 3375149251616889093067049)
    ·
      refine ⟨2531361938712666819800287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3375149251616889093067049 2531361938712666819800287)
      ·
        refine ⟨3797042908069000229700431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531361938712666819800287 3797042908069000229700431)
        ·
          refine ⟨5695564362103500344550647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3797042908069000229700431 5695564362103500344550647)
          ·
            refine ⟨8543346543155250516825971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695564362103500344550647 8543346543155250516825971)
            ·
              refine ⟨12815019814732875775238957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8543346543155250516825971 12815019814732875775238957)
              ·
                refine ⟨4805632430524828415714609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12815019814732875775238957 4805632430524828415714609)
                ·
                  refine ⟨3604224322893621311785957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4805632430524828415714609 3604224322893621311785957)
                  ·
                    refine ⟨675792060542553995959867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3604224322893621311785957 675792060542553995959867)
                    ·
                      rfl

theorem cell23_3948301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3948301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948301 prefixEnd_3948301 := by exact prefixLift 3948301
  have htrace : WordTrace (prefixWord ++ tailWord_3948301) baseStart_3948301 baseEnd_3948301 := by
    simpa [prefixWord, tailWord_3948301, baseEnd_3948301] using wordTrace_append hprefix tailTrace_3948301
  have hstable : (prefixWord ++ tailWord_3948301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948301).length < 2 ^ (prefixWord ++ tailWord_3948301).sum := by decide
  have hdescent : baseEnd_3948301 < baseStart_3948301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948316 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3948316 : Nat := 118140960795 + 3948316 * 2 ^ 59
def prefixEnd_3948316 : Nat := 4983230072969 + 3 ^ 40 * 3948316 * 2
def baseEnd_3948316 : Nat := 2027383883837479429192031

theorem tailTrace_3948316 : CollatzResearch.WordTrace tailWord_3948316 prefixEnd_3948316 2027383883837479429192031 := by
  unfold tailWord_3948316
  simp only [CollatzResearch.WordTrace]
  refine ⟨72003457581966462766328401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96004610109288617021771201 72003457581966462766328401)
  ·
    refine ⟨54002593186474847074746301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72003457581966462766328401 54002593186474847074746301)
    ·
      refine ⟨20250972444928067653029863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54002593186474847074746301 20250972444928067653029863)
      ·
        refine ⟨30376458667392101479544795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20250972444928067653029863 30376458667392101479544795)
        ·
          refine ⟨45564688001088152219317193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30376458667392101479544795 45564688001088152219317193)
          ·
            refine ⟨34173516000816114164487895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45564688001088152219317193 34173516000816114164487895)
            ·
              refine ⟨51260274001224171246731843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34173516000816114164487895 51260274001224171246731843)
              ·
                refine ⟨76890411001836256870097765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51260274001224171246731843 76890411001836256870097765)
                ·
                  refine ⟨14416952062844298163143331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76890411001836256870097765 14416952062844298163143331)
                  ·
                    refine ⟨21625428094266447244714997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14416952062844298163143331 21625428094266447244714997)
                    ·
                      refine ⟨2027383883837479429192031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21625428094266447244714997 2027383883837479429192031)
                      ·
                        rfl

theorem cell23_3948316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3948316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948316 prefixEnd_3948316 := by exact prefixLift 3948316
  have htrace : WordTrace (prefixWord ++ tailWord_3948316) baseStart_3948316 baseEnd_3948316 := by
    simpa [prefixWord, tailWord_3948316, baseEnd_3948316] using wordTrace_append hprefix tailTrace_3948316
  have hstable : (prefixWord ++ tailWord_3948316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948316).length < 2 ^ (prefixWord ++ tailWord_3948316).sum := by decide
  have hdescent : baseEnd_3948316 < baseStart_3948316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948383 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 2, 5]
def baseStart_3948383 : Nat := 118140960795 + 3948383 * 2 ^ 59
def prefixEnd_3948383 : Nat := 4983230072969 + 3 ^ 40 * 3948383 * 2
def baseEnd_3948383 : Nat := 675806095680443555684741

theorem tailTrace_3948383 : CollatzResearch.WordTrace tailWord_3948383 prefixEnd_3948383 675806095680443555684741 := by
  unfold tailWord_3948383
  simp only [CollatzResearch.WordTrace]
  refine ⟨144009358854690195975345803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96006239236460130650230535 144009358854690195975345803)
  ·
    refine ⟨216014038282035293963018705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144009358854690195975345803 216014038282035293963018705)
    ·
      refine ⟨162010528711526470472264029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216014038282035293963018705 162010528711526470472264029)
      ·
        refine ⟨60753948266822426427099011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162010528711526470472264029 60753948266822426427099011)
        ·
          refine ⟨91130922400233639640648517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60753948266822426427099011 91130922400233639640648517)
          ·
            refine ⟨17087047950043807432621597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91130922400233639640648517 17087047950043807432621597)
            ·
              refine ⟨6407642981266427787233099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17087047950043807432621597 6407642981266427787233099)
              ·
                refine ⟨9611464471899641680849649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6407642981266427787233099 9611464471899641680849649)
                ·
                  refine ⟨7208598353924731260637237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9611464471899641680849649 7208598353924731260637237)
                  ·
                    refine ⟨675806095680443555684741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7208598353924731260637237 675806095680443555684741)
                    ·
                      rfl

theorem cell23_3948383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_3948383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948383 prefixEnd_3948383 := by exact prefixLift 3948383
  have htrace : WordTrace (prefixWord ++ tailWord_3948383) baseStart_3948383 baseEnd_3948383 := by
    simpa [prefixWord, tailWord_3948383, baseEnd_3948383] using wordTrace_append hprefix tailTrace_3948383
  have hstable : (prefixWord ++ tailWord_3948383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948383).length < 2 ^ (prefixWord ++ tailWord_3948383).sum := by decide
  have hdescent : baseEnd_3948383 < baseStart_3948383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948416 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_3948416 : Nat := 118140960795 + 3948416 * 2 ^ 59
def prefixEnd_3948416 : Nat := 4983230072969 + 3 ^ 40 * 3948416 * 2
def baseEnd_3948416 : Nat := 2027435231902929037941571

theorem tailTrace_3948416 : CollatzResearch.WordTrace tailWord_3948416 prefixEnd_3948416 2027435231902929037941571 := by
  unfold tailWord_3948416
  simp only [CollatzResearch.WordTrace]
  refine ⟨72005281231785321305648551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96007041642380428407531401 72005281231785321305648551)
  ·
    refine ⟨108007921847677981958472827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72005281231785321305648551 108007921847677981958472827)
    ·
      refine ⟨162011882771516972937709241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108007921847677981958472827 162011882771516972937709241)
      ·
        refine ⟨121508912078637729703281931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162011882771516972937709241 121508912078637729703281931)
        ·
          refine ⟨182263368117956594554922897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121508912078637729703281931 182263368117956594554922897)
          ·
            refine ⟨136697526088467445916192173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182263368117956594554922897 136697526088467445916192173)
            ·
              refine ⟨51261572283175292218572065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136697526088467445916192173 51261572283175292218572065)
              ·
                refine ⟨38446179212381469163929049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51261572283175292218572065 38446179212381469163929049)
                ·
                  refine ⟨28834634409286101872946787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38446179212381469163929049 28834634409286101872946787)
                  ·
                    refine ⟨43251951613929152809420181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28834634409286101872946787 43251951613929152809420181)
                    ·
                      refine ⟨2027435231902929037941571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43251951613929152809420181 2027435231902929037941571)
                      ·
                        rfl

theorem cell23_3948416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_3948416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948416 prefixEnd_3948416 := by exact prefixLift 3948416
  have htrace : WordTrace (prefixWord ++ tailWord_3948416) baseStart_3948416 baseEnd_3948416 := by
    simpa [prefixWord, tailWord_3948416, baseEnd_3948416] using wordTrace_append hprefix tailTrace_3948416
  have hstable : (prefixWord ++ tailWord_3948416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948416).length < 2 ^ (prefixWord ++ tailWord_3948416).sum := by decide
  have hdescent : baseEnd_3948416 < baseStart_3948416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948420 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_3948420 : Nat := 118140960795 + 3948420 * 2 ^ 59
def prefixEnd_3948420 : Nat := 4983230072969 + 3 ^ 40 * 3948420 * 2
def baseEnd_3948420 : Nat := 2027437285825547022291553

theorem tailTrace_3948420 : CollatzResearch.WordTrace tailWord_3948420 prefixEnd_3948420 2027437285825547022291553 := by
  unfold tailWord_3948420
  simp only [CollatzResearch.WordTrace]
  refine ⟨72005354177778075647221357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96007138903704100862961809 72005354177778075647221357)
  ·
    refine ⟨27002007816666778367708009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72005354177778075647221357 27002007816666778367708009)
    ·
      refine ⟨20251505862500083775781007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27002007816666778367708009 20251505862500083775781007)
      ·
        refine ⟨30377258793750125663671511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20251505862500083775781007 30377258793750125663671511)
        ·
          refine ⟨45565888190625188495507267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30377258793750125663671511 45565888190625188495507267)
          ·
            refine ⟨68348832285937782743260901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45565888190625188495507267 68348832285937782743260901)
            ·
              refine ⟨12815406053613334264361419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68348832285937782743260901 12815406053613334264361419)
              ·
                refine ⟨19223109080420001396542129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12815406053613334264361419 19223109080420001396542129)
                ·
                  refine ⟨14417331810315001047406597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19223109080420001396542129 14417331810315001047406597)
                  ·
                    refine ⟨2703249714434062696388737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14417331810315001047406597 2703249714434062696388737)
                    ·
                      refine ⟨2027437285825547022291553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703249714434062696388737 2027437285825547022291553)
                      ·
                        rfl

theorem cell23_3948420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_3948420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948420 prefixEnd_3948420 := by exact prefixLift 3948420
  have htrace : WordTrace (prefixWord ++ tailWord_3948420) baseStart_3948420 baseEnd_3948420 := by
    simpa [prefixWord, tailWord_3948420, baseEnd_3948420] using wordTrace_append hprefix tailTrace_3948420
  have hstable : (prefixWord ++ tailWord_3948420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948420).length < 2 ^ (prefixWord ++ tailWord_3948420).sum := by decide
  have hdescent : baseEnd_3948420 < baseStart_3948420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948438 : List Nat := [5, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3948438 : Nat := 118140960795 + 3948438 * 2 ^ 59
def prefixEnd_3948438 : Nat := 4983230072969 + 3 ^ 40 * 3948438 * 2
def baseEnd_3948438 : Nat := 225271836497480883540719

theorem tailTrace_3948438 : CollatzResearch.WordTrace tailWord_3948438 prefixEnd_3948438 225271836497480883540719 := by
  unfold tailWord_3948438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000710304343183773037373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96007576579660626912398645 9000710304343183773037373)
  ·
    refine ⟨3375266364128693914889015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9000710304343183773037373 3375266364128693914889015)
    ·
      refine ⟨5062899546193040872333523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375266364128693914889015 5062899546193040872333523)
      ·
        refine ⟨7594349319289561308500285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5062899546193040872333523 7594349319289561308500285)
        ·
          refine ⟨2847880994733585490687607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7594349319289561308500285 2847880994733585490687607)
          ·
            refine ⟨4271821492100378236031411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847880994733585490687607 4271821492100378236031411)
            ·
              refine ⟨6407732238150567354047117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271821492100378236031411 6407732238150567354047117)
              ·
                refine ⟨2402899589306462757767669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6407732238150567354047117 2402899589306462757767669)
                ·
                  refine ⟨225271836497480883540719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2402899589306462757767669 225271836497480883540719)
                  ·
                    rfl

theorem cell23_3948438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3948438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948438 prefixEnd_3948438 := by exact prefixLift 3948438
  have htrace : WordTrace (prefixWord ++ tailWord_3948438) baseStart_3948438 baseEnd_3948438 := by
    simpa [prefixWord, tailWord_3948438, baseEnd_3948438] using wordTrace_append hprefix tailTrace_3948438
  have hstable : (prefixWord ++ tailWord_3948438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948438).length < 2 ^ (prefixWord ++ tailWord_3948438).sum := by decide
  have hdescent : baseEnd_3948438 < baseStart_3948438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948473 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 3, 5]
def baseStart_3948473 : Nat := 118140960795 + 3948473 * 2 ^ 59
def prefixEnd_3948473 : Nat := 4983230072969 + 3 ^ 40 * 3948473 * 2
def baseEnd_3948473 : Nat := 675821500100078438309603

theorem tailTrace_3948473 : CollatzResearch.WordTrace tailWord_3948473 prefixEnd_3948473 675821500100078438309603 := by
  unfold tailWord_3948473
  simp only [CollatzResearch.WordTrace]
  refine ⟨144012641424364141346122073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96008427616242760897414715 144012641424364141346122073)
  ·
    refine ⟨108009481068273106009591555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144012641424364141346122073 108009481068273106009591555)
    ·
      refine ⟨162014221602409659014387333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108009481068273106009591555 162014221602409659014387333)
      ·
        refine ⟨30377666550451811065197625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162014221602409659014387333 30377666550451811065197625)
        ·
          refine ⟨22783249912838858298898219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30377666550451811065197625 22783249912838858298898219)
          ·
            refine ⟨34174874869258287448347329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22783249912838858298898219 34174874869258287448347329)
            ·
              refine ⟨25631156151943715586260497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34174874869258287448347329 25631156151943715586260497)
              ·
                refine ⟨19223367113957786689695373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25631156151943715586260497 19223367113957786689695373)
                ·
                  refine ⟨7208762667734170008635765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19223367113957786689695373 7208762667734170008635765)
                  ·
                    refine ⟨675821500100078438309603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7208762667734170008635765 675821500100078438309603)
                    ·
                      rfl

theorem cell23_3948473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_3948473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948473 prefixEnd_3948473 := by exact prefixLift 3948473
  have htrace : WordTrace (prefixWord ++ tailWord_3948473) baseStart_3948473 baseEnd_3948473 := by
    simpa [prefixWord, tailWord_3948473, baseEnd_3948473] using wordTrace_append hprefix tailTrace_3948473
  have hstable : (prefixWord ++ tailWord_3948473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948473).length < 2 ^ (prefixWord ++ tailWord_3948473).sum := by decide
  have hdescent : baseEnd_3948473 < baseStart_3948473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948477 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 6]
def baseStart_3948477 : Nat := 118140960795 + 3948477 * 2 ^ 59
def prefixEnd_3948477 : Nat := 4983230072969 + 3 ^ 40 * 3948477 * 2
def baseEnd_3948477 : Nat := 225274061580317033253199

theorem tailTrace_3948477 : CollatzResearch.WordTrace tailWord_3948477 prefixEnd_3948477 225274061580317033253199 := by
  unfold tailWord_3948477
  simp only [CollatzResearch.WordTrace]
  refine ⟨144012787316349650029267685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96008524877566433352845123 144012787316349650029267685)
  ·
    refine ⟨27002397621815559380487691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144012787316349650029267685 27002397621815559380487691)
    ·
      refine ⟨40503596432723339070731537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27002397621815559380487691 40503596432723339070731537)
      ·
        refine ⟨30377697324542504303048653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40503596432723339070731537 30377697324542504303048653)
        ·
          refine ⟨11391636496703439113643245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30377697324542504303048653 11391636496703439113643245)
          ·
            refine ⟨4271863686263789667616217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11391636496703439113643245 4271863686263789667616217)
            ·
              refine ⟨3203897764697842250712163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271863686263789667616217 3203897764697842250712163)
              ·
                refine ⟨4805846647046763376068245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203897764697842250712163 4805846647046763376068245)
                ·
                  refine ⟨225274061580317033253199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4805846647046763376068245 225274061580317033253199)
                  ·
                    rfl

theorem cell23_3948477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_3948477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948477 prefixEnd_3948477 := by exact prefixLift 3948477
  have htrace : WordTrace (prefixWord ++ tailWord_3948477) baseStart_3948477 baseEnd_3948477 := by
    simpa [prefixWord, tailWord_3948477, baseEnd_3948477] using wordTrace_append hprefix tailTrace_3948477
  have hstable : (prefixWord ++ tailWord_3948477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948477).length < 2 ^ (prefixWord ++ tailWord_3948477).sum := by decide
  have hdescent : baseEnd_3948477 < baseStart_3948477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948480 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 4, 3, 2]
def baseStart_3948480 : Nat := 118140960795 + 3948480 * 2 ^ 59
def prefixEnd_3948480 : Nat := 4983230072969 + 3 ^ 40 * 3948480 * 2
def baseEnd_3948480 : Nat := 2027468094664816787541277

theorem tailTrace_3948480 : CollatzResearch.WordTrace tailWord_3948480 prefixEnd_3948480 2027468094664816787541277 := by
  unfold tailWord_3948480
  simp only [CollatzResearch.WordTrace]
  refine ⟨72006448367669390770813447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96008597823559187694417929 72006448367669390770813447)
  ·
    refine ⟨108009672551504086156220171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72006448367669390770813447 108009672551504086156220171)
    ·
      refine ⟨162014508827256129234330257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108009672551504086156220171 162014508827256129234330257)
      ·
        refine ⟨121510881620442096925747693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162014508827256129234330257 121510881620442096925747693)
        ·
          refine ⟨45566580607665786347155385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121510881620442096925747693 45566580607665786347155385)
          ·
            refine ⟨34174935455749339760366539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45566580607665786347155385 34174935455749339760366539)
            ·
              refine ⟨51262403183624009640549809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34174935455749339760366539 51262403183624009640549809)
              ·
                refine ⟨38446802387718007230412357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51262403183624009640549809 38446802387718007230412357)
                ·
                  refine ⟨7208775447697126355702317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38446802387718007230412357 7208775447697126355702317)
                  ·
                    refine ⟨2703290792886422383388369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7208775447697126355702317 2703290792886422383388369)
                    ·
                      refine ⟨2027468094664816787541277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703290792886422383388369 2027468094664816787541277)
                      ·
                        rfl

theorem cell23_3948480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_3948480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948480 prefixEnd_3948480 := by exact prefixLift 3948480
  have htrace : WordTrace (prefixWord ++ tailWord_3948480) baseStart_3948480 baseEnd_3948480 := by
    simpa [prefixWord, tailWord_3948480, baseEnd_3948480] using wordTrace_append hprefix tailTrace_3948480
  have hstable : (prefixWord ++ tailWord_3948480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948480).length < 2 ^ (prefixWord ++ tailWord_3948480).sum := by decide
  have hdescent : baseEnd_3948480 < baseStart_3948480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948490 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_3948490 : Nat := 118140960795 + 3948490 * 2 ^ 59
def prefixEnd_3948490 : Nat := 4983230072969 + 3 ^ 40 * 3948490 * 2
def baseEnd_3948490 : Nat := 675824409823787249472077

theorem tailTrace_3948490 : CollatzResearch.WordTrace tailWord_3948490 prefixEnd_3948490 675824409823787249472077 := by
  unfold tailWord_3948490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36003315366325638312372731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96008840976868368832993949 36003315366325638312372731)
  ·
    refine ⟨54004973049488457468559097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36003315366325638312372731 54004973049488457468559097)
    ·
      refine ⟨40503729787116343101419323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54004973049488457468559097 40503729787116343101419323)
      ·
        refine ⟨60755594680674514652128985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40503729787116343101419323 60755594680674514652128985)
        ·
          refine ⟨45566696010505885989096739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60755594680674514652128985 45566696010505885989096739)
          ·
            refine ⟨68350044015758828983645109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45566696010505885989096739 68350044015758828983645109)
            ·
              refine ⟨6407816626477390217216729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68350044015758828983645109 6407816626477390217216729)
              ·
                refine ⟨4805862469858042662912547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6407816626477390217216729 4805862469858042662912547)
                ·
                  refine ⟨7208793704787063994368821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805862469858042662912547 7208793704787063994368821)
                  ·
                    refine ⟨675824409823787249472077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7208793704787063994368821 675824409823787249472077)
                    ·
                      rfl

theorem cell23_3948490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_3948490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948490 prefixEnd_3948490 := by exact prefixLift 3948490
  have htrace : WordTrace (prefixWord ++ tailWord_3948490) baseStart_3948490 baseEnd_3948490 := by
    simpa [prefixWord, tailWord_3948490, baseEnd_3948490] using wordTrace_append hprefix tailTrace_3948490
  have hstable : (prefixWord ++ tailWord_3948490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948490).length < 2 ^ (prefixWord ++ tailWord_3948490).sum := by decide
  have hdescent : baseEnd_3948490 < baseStart_3948490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948503 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 1, 6]
def baseStart_3948503 : Nat := 118140960795 + 3948503 * 2 ^ 59
def prefixEnd_3948503 : Nat := 4983230072969 + 3 ^ 40 * 3948503 * 2
def baseEnd_3948503 : Nat := 675826634906623399184557

theorem tailTrace_3948503 : CollatzResearch.WordTrace tailWord_3948503 prefixEnd_3948503 675826634906623399184557 := by
  unfold tailWord_3948503
  simp only [CollatzResearch.WordTrace]
  refine ⟨144013735614255456469714163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96009157076170304313142775 144013735614255456469714163)
  ·
    refine ⟨216020603421383184704571245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144013735614255456469714163 216020603421383184704571245)
    ·
      refine ⟨81007726283018694264214217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216020603421383184704571245 81007726283018694264214217)
      ·
        refine ⟨60755794712264020698160663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81007726283018694264214217 60755794712264020698160663)
        ·
          refine ⟨91133692068396031047240995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60755794712264020698160663 91133692068396031047240995)
          ·
            refine ⟨136700538102594046570861493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91133692068396031047240995 136700538102594046570861493)
            ·
              refine ⟨12815675447118191866018265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136700538102594046570861493 12815675447118191866018265)
              ·
                refine ⟨9611756585338643899513699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12815675447118191866018265 9611756585338643899513699)
                ·
                  refine ⟨14417634878007965849270549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9611756585338643899513699 14417634878007965849270549)
                  ·
                    refine ⟨675826634906623399184557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14417634878007965849270549 675826634906623399184557)
                    ·
                      rfl

theorem cell23_3948503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_3948503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948503 prefixEnd_3948503 := by exact prefixLift 3948503
  have htrace : WordTrace (prefixWord ++ tailWord_3948503) baseStart_3948503 baseEnd_3948503 := by
    simpa [prefixWord, tailWord_3948503, baseEnd_3948503] using wordTrace_append hprefix tailTrace_3948503
  have hstable : (prefixWord ++ tailWord_3948503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948503).length < 2 ^ (prefixWord ++ tailWord_3948503).sum := by decide
  have hdescent : baseEnd_3948503 < baseStart_3948503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948527 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 3, 2, 2]
def baseStart_3948527 : Nat := 118140960795 + 3948527 * 2 ^ 59
def prefixEnd_3948527 : Nat := 4983230072969 + 3 ^ 40 * 3948527 * 2
def baseEnd_3948527 : Nat := 2027492228255578103653561

theorem tailTrace_3948527 : CollatzResearch.WordTrace tailWord_3948527 prefixEnd_3948527 2027492228255578103653561 := by
  unfold tailWord_3948527
  simp only [CollatzResearch.WordTrace]
  refine ⟨144014610966168508568587835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96009740644112339045725223 144014610966168508568587835)
  ·
    refine ⟨216021916449252762852881753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144014610966168508568587835 216021916449252762852881753)
    ·
      refine ⟨162016437336939572139661315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216021916449252762852881753 162016437336939572139661315)
      ·
        refine ⟨243024656005409358209491973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162016437336939572139661315 243024656005409358209491973)
        ·
          refine ⟨45567123001014254664279745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243024656005409358209491973 45567123001014254664279745)
          ·
            refine ⟨34175342250760690998209809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45567123001014254664279745 34175342250760690998209809)
            ·
              refine ⟨25631506688070518248657357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34175342250760690998209809 25631506688070518248657357)
              ·
                refine ⟨9611815008026444343246509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25631506688070518248657357 9611815008026444343246509)
                ·
                  refine ⟨3604430628009916628717441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9611815008026444343246509 3604430628009916628717441)
                  ·
                    refine ⟨2703322971007437471538081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3604430628009916628717441 2703322971007437471538081)
                    ·
                      refine ⟨2027492228255578103653561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703322971007437471538081 2027492228255578103653561)
                      ·
                        rfl

theorem cell23_3948527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 2, 2].length) (baseStart_3948527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948527 prefixEnd_3948527 := by exact prefixLift 3948527
  have htrace : WordTrace (prefixWord ++ tailWord_3948527) baseStart_3948527 baseEnd_3948527 := by
    simpa [prefixWord, tailWord_3948527, baseEnd_3948527] using wordTrace_append hprefix tailTrace_3948527
  have hstable : (prefixWord ++ tailWord_3948527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948527).length < 2 ^ (prefixWord ++ tailWord_3948527).sum := by decide
  have hdescent : baseEnd_3948527 < baseStart_3948527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948540 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_3948540 : Nat := 118140960795 + 3948540 * 2 ^ 59
def prefixEnd_3948540 : Nat := 4983230072969 + 3 ^ 40 * 3948540 * 2
def baseEnd_3948540 : Nat := 2027498903504086552791001

theorem tailTrace_3948540 : CollatzResearch.WordTrace tailWord_3948540 prefixEnd_3948540 2027498903504086552791001 := by
  unfold tailWord_3948540
  simp only [CollatzResearch.WordTrace]
  refine ⟨72007542557560705894405537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96010056743414274525874049 72007542557560705894405537)
  ·
    refine ⟨54005656918170529420804153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72007542557560705894405537 54005656918170529420804153)
    ·
      refine ⟨40504242688627897065603115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54005656918170529420804153 40504242688627897065603115)
      ·
        refine ⟨60756364032941845598404673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40504242688627897065603115 60756364032941845598404673)
        ·
          refine ⟨45567273024706384198803505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60756364032941845598404673 45567273024706384198803505)
          ·
            refine ⟨34175454768529788149102629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45567273024706384198803505 34175454768529788149102629)
            ·
              refine ⟨6407897769099335277956743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34175454768529788149102629 6407897769099335277956743)
              ·
                refine ⟨9611846653649002916935115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6407897769099335277956743 9611846653649002916935115)
                ·
                  refine ⟨14417769980473504375402673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9611846653649002916935115 14417769980473504375402673)
                  ·
                    refine ⟨10813327485355128281552005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14417769980473504375402673 10813327485355128281552005)
                    ·
                      refine ⟨2027498903504086552791001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10813327485355128281552005 2027498903504086552791001)
                      ·
                        rfl

theorem cell23_3948540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_3948540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948540 prefixEnd_3948540 := by exact prefixLift 3948540
  have htrace : WordTrace (prefixWord ++ tailWord_3948540) baseStart_3948540 baseEnd_3948540 := by
    simpa [prefixWord, tailWord_3948540, baseEnd_3948540] using wordTrace_append hprefix tailTrace_3948540
  have hstable : (prefixWord ++ tailWord_3948540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948540).length < 2 ^ (prefixWord ++ tailWord_3948540).sum := by decide
  have hdescent : baseEnd_3948540 < baseStart_3948540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948548 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3948548 : Nat := 118140960795 + 3948548 * 2 ^ 59
def prefixEnd_3948548 : Nat := 4983230072969 + 3 ^ 40 * 3948548 * 2
def baseEnd_3948548 : Nat := 2027503011349322521490965

theorem tailTrace_3948548 : CollatzResearch.WordTrace tailWord_3948548 prefixEnd_3948548 2027503011349322521490965 := by
  unfold tailWord_3948548
  simp only [CollatzResearch.WordTrace]
  refine ⟨72007688449546214577551149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96010251266061619436734865 72007688449546214577551149)
  ·
    refine ⟨27002883168579830466581681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72007688449546214577551149 27002883168579830466581681)
    ·
      refine ⟨20252162376434872849936261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27002883168579830466581681 20252162376434872849936261)
      ·
        refine ⟨3797280445581538659363049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20252162376434872849936261 3797280445581538659363049)
        ·
          refine ⟨2847960334186153994522287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3797280445581538659363049 2847960334186153994522287)
          ·
            refine ⟨4271940501279230991783431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847960334186153994522287 4271940501279230991783431)
            ·
              refine ⟨6407910751918846487675147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271940501279230991783431 6407910751918846487675147)
              ·
                refine ⟨9611866127878269731512721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6407910751918846487675147 9611866127878269731512721)
                ·
                  refine ⟨7208899595908702298634541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9611866127878269731512721 7208899595908702298634541)
                  ·
                    refine ⟨2703337348465763361987953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7208899595908702298634541 2703337348465763361987953)
                    ·
                      refine ⟨2027503011349322521490965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703337348465763361987953 2027503011349322521490965)
                      ·
                        rfl

theorem cell23_3948548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3948548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948548 prefixEnd_3948548 := by exact prefixLift 3948548
  have htrace : WordTrace (prefixWord ++ tailWord_3948548) baseStart_3948548 baseEnd_3948548 := by
    simpa [prefixWord, tailWord_3948548, baseEnd_3948548] using wordTrace_append hprefix tailTrace_3948548
  have hstable : (prefixWord ++ tailWord_3948548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948548).length < 2 ^ (prefixWord ++ tailWord_3948548).sum := by decide
  have hdescent : baseEnd_3948548 < baseStart_3948548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948560 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 6, 1, 3]
def baseStart_3948560 : Nat := 118140960795 + 3948560 * 2 ^ 59
def prefixEnd_3948560 : Nat := 4983230072969 + 3 ^ 40 * 3948560 * 2
def baseEnd_3948560 : Nat := 2027509173117176474540909

theorem tailTrace_3948560 : CollatzResearch.WordTrace tailWord_3948560 prefixEnd_3948560 2027509173117176474540909 := by
  unfold tailWord_3948560
  simp only [CollatzResearch.WordTrace]
  refine ⟨72007907287524477602269567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96010543050032636803026089 72007907287524477602269567)
  ·
    refine ⟨108011860931286716403404351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72007907287524477602269567 108011860931286716403404351)
    ·
      refine ⟨162017791396930074605106527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108011860931286716403404351 162017791396930074605106527)
      ·
        refine ⟨243026687095395111907659791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162017791396930074605106527 243026687095395111907659791)
        ·
          refine ⟨364540030643092667861489687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243026687095395111907659791 364540030643092667861489687)
          ·
            refine ⟨546810045964639001792234531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364540030643092667861489687 546810045964639001792234531)
            ·
              refine ⟨820215068946958502688351797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546810045964639001792234531 820215068946958502688351797)
              ·
                refine ⟨76895162713777359627032981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 820215068946958502688351797 76895162713777359627032981)
                ·
                  refine ⟨3604460752208313732517171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76895162713777359627032981 3604460752208313732517171)
                  ·
                    refine ⟨5406691128312470598775757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3604460752208313732517171 5406691128312470598775757)
                    ·
                      refine ⟨2027509173117176474540909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5406691128312470598775757 2027509173117176474540909)
                      ·
                        rfl

theorem cell23_3948560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 1, 3].length) (baseStart_3948560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948560 prefixEnd_3948560 := by exact prefixLift 3948560
  have htrace : WordTrace (prefixWord ++ tailWord_3948560) baseStart_3948560 baseEnd_3948560 := by
    simpa [prefixWord, tailWord_3948560, baseEnd_3948560] using wordTrace_append hprefix tailTrace_3948560
  have hstable : (prefixWord ++ tailWord_3948560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948560).length < 2 ^ (prefixWord ++ tailWord_3948560).sum := by decide
  have hdescent : baseEnd_3948560 < baseStart_3948560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948603 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 5]
def baseStart_3948603 : Nat := 118140960795 + 3948603 * 2 ^ 59
def prefixEnd_3948603 : Nat := 4983230072969 + 3 ^ 40 * 3948603 * 2
def baseEnd_3948603 : Nat := 2027531252785319806303211

theorem tailTrace_3948603 : CollatzResearch.WordTrace tailWord_3948603 prefixEnd_3948603 2027531252785319806303211 := by
  unfold tailWord_3948603
  simp only [CollatzResearch.WordTrace]
  refine ⟨144017382913893173548354463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96011588609262115698902975 144017382913893173548354463)
  ·
    refine ⟨216026074370839760322531695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144017382913893173548354463 216026074370839760322531695)
    ·
      refine ⟨324039111556259640483797543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216026074370839760322531695 324039111556259640483797543)
      ·
        refine ⟨486058667334389460725696315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324039111556259640483797543 486058667334389460725696315)
        ·
          refine ⟨729088001001584191088544473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486058667334389460725696315 729088001001584191088544473)
          ·
            refine ⟨546816000751188143316408355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729088001001584191088544473 546816000751188143316408355)
            ·
              refine ⟨820224001126782214974612533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546816000751188143316408355 820224001126782214974612533)
              ·
                refine ⟨76896000105635832653869925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 820224001126782214974612533 76896000105635832653869925)
                ·
                  refine ⟨14418000019806718622600611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76896000105635832653869925 14418000019806718622600611)
                  ·
                    refine ⟨21627000029710077933900917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14418000019806718622600611 21627000029710077933900917)
                    ·
                      refine ⟨2027531252785319806303211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21627000029710077933900917 2027531252785319806303211)
                      ·
                        rfl

theorem cell23_3948603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 5].length) (baseStart_3948603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948603 prefixEnd_3948603 := by exact prefixLift 3948603
  have htrace : WordTrace (prefixWord ++ tailWord_3948603) baseStart_3948603 baseEnd_3948603 := by
    simpa [prefixWord, tailWord_3948603, baseEnd_3948603] using wordTrace_append hprefix tailTrace_3948603
  have hstable : (prefixWord ++ tailWord_3948603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948603).length < 2 ^ (prefixWord ++ tailWord_3948603).sum := by decide
  have hdescent : baseEnd_3948603 < baseStart_3948603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948604 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_3948604 : Nat := 118140960795 + 3948604 * 2 ^ 59
def prefixEnd_3948604 : Nat := 4983230072969 + 3 ^ 40 * 3948604 * 2
def baseEnd_3948604 : Nat := 2027531766265974302390707

theorem tailTrace_3948604 : CollatzResearch.WordTrace tailWord_3948604 prefixEnd_3948604 2027531766265974302390707 := by
  unfold tailWord_3948604
  simp only [CollatzResearch.WordTrace]
  refine ⟨72008709693444775359570433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96011612924593033812760577 72008709693444775359570433)
  ·
    refine ⟨54006532270083581519677825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72008709693444775359570433 54006532270083581519677825)
    ·
      refine ⟨40504899202562686139758369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54006532270083581519677825 40504899202562686139758369)
      ·
        refine ⟨30378674401922014604818777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40504899202562686139758369 30378674401922014604818777)
        ·
          refine ⟨22784005801441510953614083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30378674401922014604818777 22784005801441510953614083)
          ·
            refine ⟨34176008702162266430421125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22784005801441510953614083 34176008702162266430421125)
            ·
              refine ⟨6408001631655424955703961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34176008702162266430421125 6408001631655424955703961)
              ·
                refine ⟨4806001223741568716777971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6408001631655424955703961 4806001223741568716777971)
                ·
                  refine ⟨7209001835612353075166957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806001223741568716777971 7209001835612353075166957)
                  ·
                    refine ⟨2703375688354632403187609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7209001835612353075166957 2703375688354632403187609)
                    ·
                      refine ⟨2027531766265974302390707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703375688354632403187609 2027531766265974302390707)
                      ·
                        rfl

theorem cell23_3948604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_3948604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948604 prefixEnd_3948604 := by exact prefixLift 3948604
  have htrace : WordTrace (prefixWord ++ tailWord_3948604) baseStart_3948604 baseEnd_3948604 := by
    simpa [prefixWord, tailWord_3948604, baseEnd_3948604] using wordTrace_append hprefix tailTrace_3948604
  have hstable : (prefixWord ++ tailWord_3948604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948604).length < 2 ^ (prefixWord ++ tailWord_3948604).sum := by decide
  have hdescent : baseEnd_3948604 < baseStart_3948604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948617 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 6, 2, 2]
def baseStart_3948617 : Nat := 118140960795 + 3948617 * 2 ^ 59
def prefixEnd_3948617 : Nat := 4983230072969 + 3 ^ 40 * 3948617 * 2
def baseEnd_3948617 : Nat := 2027538441514482751528147

theorem tailTrace_3948617 : CollatzResearch.WordTrace tailWord_3948617 prefixEnd_3948617 2027538441514482751528147 := by
  unfold tailWord_3948617
  simp only [CollatzResearch.WordTrace]
  refine ⟨144017893535842453939364105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96011929023894969292909403 144017893535842453939364105)
  ·
    refine ⟨108013420151881840454523079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144017893535842453939364105 108013420151881840454523079)
    ·
      refine ⟨162020130227822760681784619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108013420151881840454523079 162020130227822760681784619)
      ·
        refine ⟨243030195341734141022676929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162020130227822760681784619 243030195341734141022676929)
        ·
          refine ⟨182272646506300605767007697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243030195341734141022676929 182272646506300605767007697)
          ·
            refine ⟨136704484879725454325255773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182272646506300605767007697 136704484879725454325255773)
            ·
              refine ⟨51264181829897045371970915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136704484879725454325255773 51264181829897045371970915)
              ·
                refine ⟨76896272744845568057956373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51264181829897045371970915 76896272744845568057956373)
                ·
                  refine ⟨3604512784914636002716705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76896272744845568057956373 3604512784914636002716705)
                  ·
                    refine ⟨2703384588685977002037529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3604512784914636002716705 2703384588685977002037529)
                    ·
                      refine ⟨2027538441514482751528147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703384588685977002037529 2027538441514482751528147)
                      ·
                        rfl

theorem cell23_3948617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 2, 2].length) (baseStart_3948617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948617 prefixEnd_3948617 := by exact prefixLift 3948617
  have htrace : WordTrace (prefixWord ++ tailWord_3948617) baseStart_3948617 baseEnd_3948617 := by
    simpa [prefixWord, tailWord_3948617, baseEnd_3948617] using wordTrace_append hprefix tailTrace_3948617
  have hstable : (prefixWord ++ tailWord_3948617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948617).length < 2 ^ (prefixWord ++ tailWord_3948617).sum := by decide
  have hdescent : baseEnd_3948617 < baseStart_3948617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948633 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_3948633 : Nat := 118140960795 + 3948633 * 2 ^ 59
def prefixEnd_3948633 : Nat := 4983230072969 + 3 ^ 40 * 3948633 * 2
def baseEnd_3948633 : Nat := 2027546657204954688928073

theorem tailTrace_3948633 : CollatzResearch.WordTrace tailWord_3948633 prefixEnd_3948633 2027546657204954688928073 := by
  unfold tailWord_3948633
  simp only [CollatzResearch.WordTrace]
  refine ⟨144018477103784488671946553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96012318069189659114631035 144018477103784488671946553)
  ·
    refine ⟨108013857827838366503959915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144018477103784488671946553 108013857827838366503959915)
    ·
      refine ⟨162020786741757549755939873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108013857827838366503959915 162020786741757549755939873)
      ·
        refine ⟨121515590056318162316954905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162020786741757549755939873 121515590056318162316954905)
        ·
          refine ⟨91136692542238621737716179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121515590056318162316954905 91136692542238621737716179)
          ·
            refine ⟨136705038813357932606574269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91136692542238621737716179 136705038813357932606574269)
            ·
              refine ⟨51264389555009224727465351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136705038813357932606574269 51264389555009224727465351)
              ·
                refine ⟨76896584332513837091198027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51264389555009224727465351 76896584332513837091198027)
                ·
                  refine ⟨115344876498770755636797041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76896584332513837091198027 115344876498770755636797041)
                  ·
                    refine ⟨86508657374078066727597781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115344876498770755636797041 86508657374078066727597781)
                    ·
                      refine ⟨2027546657204954688928073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86508657374078066727597781 2027546657204954688928073)
                      ·
                        rfl

theorem cell23_3948633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_3948633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948633 prefixEnd_3948633 := by exact prefixLift 3948633
  have htrace : WordTrace (prefixWord ++ tailWord_3948633) baseStart_3948633 baseEnd_3948633 := by
    simpa [prefixWord, tailWord_3948633, baseEnd_3948633] using wordTrace_append hprefix tailTrace_3948633
  have hstable : (prefixWord ++ tailWord_3948633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948633).length < 2 ^ (prefixWord ++ tailWord_3948633).sum := by decide
  have hdescent : baseEnd_3948633 < baseStart_3948633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948634 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2]
def baseStart_3948634 : Nat := 118140960795 + 3948634 * 2 ^ 59
def prefixEnd_3948634 : Nat := 4983230072969 + 3 ^ 40 * 3948634 * 2
def baseEnd_3948634 : Nat := 2027547170685609185015569

theorem tailTrace_3948634 : CollatzResearch.WordTrace tailWord_3948634 prefixEnd_3948634 2027547170685609185015569 := by
  unfold tailWord_3948634
  simp only [CollatzResearch.WordTrace]
  refine ⟨36004628394195216460683239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96012342384520577228488637 36004628394195216460683239)
  ·
    refine ⟨54006942591292824691024859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36004628394195216460683239 54006942591292824691024859)
    ·
      refine ⟨81010413886939237036537289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54006942591292824691024859 81010413886939237036537289)
      ·
        refine ⟨60757810415204427777402967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81010413886939237036537289 60757810415204427777402967)
        ·
          refine ⟨91136715622806641666104451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60757810415204427777402967 91136715622806641666104451)
          ·
            refine ⟨136705073434209962499156677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91136715622806641666104451 136705073434209962499156677)
            ·
              refine ⟨25632201268914367968591877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136705073434209962499156677 25632201268914367968591877)
              ·
                refine ⟨4806037737921443994110977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25632201268914367968591877 4806037737921443994110977)
                ·
                  refine ⟨3604528303441082995583233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4806037737921443994110977 3604528303441082995583233)
                  ·
                    refine ⟨2703396227580812246687425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3604528303441082995583233 2703396227580812246687425)
                    ·
                      refine ⟨2027547170685609185015569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703396227580812246687425 2027547170685609185015569)
                      ·
                        rfl

theorem cell23_3948634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_3948634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948634 prefixEnd_3948634 := by exact prefixLift 3948634
  have htrace : WordTrace (prefixWord ++ tailWord_3948634) baseStart_3948634 baseEnd_3948634 := by
    simpa [prefixWord, tailWord_3948634, baseEnd_3948634] using wordTrace_append hprefix tailTrace_3948634
  have hstable : (prefixWord ++ tailWord_3948634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948634).length < 2 ^ (prefixWord ++ tailWord_3948634).sum := by decide
  have hdescent : baseEnd_3948634 < baseStart_3948634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948640 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 7]
def baseStart_3948640 : Nat := 118140960795 + 3948640 * 2 ^ 59
def prefixEnd_3948640 : Nat := 4983230072969 + 3 ^ 40 * 3948640 * 2
def baseEnd_3948640 : Nat := 225283361285504017948949

theorem tailTrace_3948640 : CollatzResearch.WordTrace tailWord_3948640 prefixEnd_3948640 225283361285504017948949 := by
  unfold tailWord_3948640
  simp only [CollatzResearch.WordTrace]
  refine ⟨72009366207379564433725687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96012488276506085911634249 72009366207379564433725687)
  ·
    refine ⟨108014049311069346650588531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72009366207379564433725687 108014049311069346650588531)
    ·
      refine ⟨162021073966604019975882797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108014049311069346650588531 162021073966604019975882797)
      ·
        refine ⟨60757902737476507490956049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162021073966604019975882797 60757902737476507490956049)
        ·
          refine ⟨45568427053107380618217037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60757902737476507490956049 45568427053107380618217037)
          ·
            refine ⟨17088160144915267731831389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45568427053107380618217037 17088160144915267731831389)
            ·
              refine ⟨6408060054343225399436771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17088160144915267731831389 6408060054343225399436771)
              ·
                refine ⟨9612090081514838099155157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408060054343225399436771 9612090081514838099155157)
                ·
                  refine ⟨225283361285504017948949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9612090081514838099155157 225283361285504017948949)
                  ·
                    rfl

theorem cell23_3948640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 7].length) (baseStart_3948640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948640 prefixEnd_3948640 := by exact prefixLift 3948640
  have htrace : WordTrace (prefixWord ++ tailWord_3948640) baseStart_3948640 baseEnd_3948640 := by
    simpa [prefixWord, tailWord_3948640, baseEnd_3948640] using wordTrace_append hprefix tailTrace_3948640
  have hstable : (prefixWord ++ tailWord_3948640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948640).length < 2 ^ (prefixWord ++ tailWord_3948640).sum := by decide
  have hdescent : baseEnd_3948640 < baseStart_3948640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948721 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 2, 5]
def baseStart_3948721 : Nat := 118140960795 + 3948721 * 2 ^ 59
def prefixEnd_3948721 : Nat := 4983230072969 + 3 ^ 40 * 3948721 * 2
def baseEnd_3948721 : Nat := 675863947834183448209223

theorem tailTrace_3948721 : CollatzResearch.WordTrace tailWord_3948721 prefixEnd_3948721 675863947834183448209223 := by
  unfold tailWord_3948721
  simp only [CollatzResearch.WordTrace]
  refine ⟨144021686727465679701150017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96014457818310453134100011 144021686727465679701150017)
  ·
    refine ⟨108016265045599259775862513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144021686727465679701150017 108016265045599259775862513)
    ·
      refine ⟨81012198784199444831896885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108016265045599259775862513 81012198784199444831896885)
      ·
        refine ⟨7594893636018697952990333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81012198784199444831896885 7594893636018697952990333)
        ·
          refine ⟨2848085113507011732371375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7594893636018697952990333 2848085113507011732371375)
          ·
            refine ⟨4272127670260517598557063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848085113507011732371375 4272127670260517598557063)
            ·
              refine ⟨6408191505390776397835595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272127670260517598557063 6408191505390776397835595)
              ·
                refine ⟨9612287258086164596753393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408191505390776397835595 9612287258086164596753393)
                ·
                  refine ⟨7209215443564623447565045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9612287258086164596753393 7209215443564623447565045)
                  ·
                    refine ⟨675863947834183448209223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7209215443564623447565045 675863947834183448209223)
                    ·
                      rfl

theorem cell23_3948721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_3948721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948721 prefixEnd_3948721 := by exact prefixLift 3948721
  have htrace : WordTrace (prefixWord ++ tailWord_3948721) baseStart_3948721 baseEnd_3948721 := by
    simpa [prefixWord, tailWord_3948721, baseEnd_3948721] using wordTrace_append hprefix tailTrace_3948721
  have hstable : (prefixWord ++ tailWord_3948721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948721).length < 2 ^ (prefixWord ++ tailWord_3948721).sum := by decide
  have hdescent : baseEnd_3948721 < baseStart_3948721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948727 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_3948727 : Nat := 118140960795 + 3948727 * 2 ^ 59
def prefixEnd_3948727 : Nat := 4983230072969 + 3 ^ 40 * 3948727 * 2
def baseEnd_3948727 : Nat := 2027594924386477321152641

theorem tailTrace_3948727 : CollatzResearch.WordTrace tailWord_3948727 prefixEnd_3948727 2027594924386477321152641 := by
  unfold tailWord_3948727
  simp only [CollatzResearch.WordTrace]
  refine ⟨144021905565443942725868435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96014603710295961817245623 144021905565443942725868435)
  ·
    refine ⟨216032858348165914088802653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144021905565443942725868435 216032858348165914088802653)
    ·
      refine ⟨81012321880562217783300995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216032858348165914088802653 81012321880562217783300995)
      ·
        refine ⟨121518482820843326674951493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81012321880562217783300995 121518482820843326674951493)
        ·
          refine ⟨22784715528908123751553405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121518482820843326674951493 22784715528908123751553405)
          ·
            refine ⟨8544268323340546406832527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22784715528908123751553405 8544268323340546406832527)
            ·
              refine ⟨12816402485010819610248791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8544268323340546406832527 12816402485010819610248791)
              ·
                refine ⟨19224603727516229415373187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12816402485010819610248791 19224603727516229415373187)
                ·
                  refine ⟨28836905591274344123059781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19224603727516229415373187 28836905591274344123059781)
                  ·
                    refine ⟨5406919798363939523073709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28836905591274344123059781 5406919798363939523073709)
                    ·
                      refine ⟨2027594924386477321152641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5406919798363939523073709 2027594924386477321152641)
                      ·
                        rfl

theorem cell23_3948727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_3948727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948727 prefixEnd_3948727 := by exact prefixLift 3948727
  have htrace : WordTrace (prefixWord ++ tailWord_3948727) baseStart_3948727 baseEnd_3948727 := by
    simpa [prefixWord, tailWord_3948727, baseEnd_3948727] using wordTrace_append hprefix tailTrace_3948727
  have hstable : (prefixWord ++ tailWord_3948727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948727).length < 2 ^ (prefixWord ++ tailWord_3948727).sum := by decide
  have hdescent : baseEnd_3948727 < baseStart_3948727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948817 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_3948817 : Nat := 118140960795 + 3948817 * 2 ^ 59
def prefixEnd_3948817 : Nat := 4983230072969 + 3 ^ 40 * 3948817 * 2
def baseEnd_3948817 : Nat := 2027641137645381969027227

theorem tailTrace_3948817 : CollatzResearch.WordTrace tailWord_3948817 prefixEnd_3948817 2027641137645381969027227 := by
  unfold tailWord_3948817
  simp only [CollatzResearch.WordTrace]
  refine ⟨144025188135117888096644705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96016792090078592064429803 144025188135117888096644705)
  ·
    refine ⟨108018891101338416072483529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144025188135117888096644705 108018891101338416072483529)
    ·
      refine ⟨81014168326003812054362647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108018891101338416072483529 81014168326003812054362647)
      ·
        refine ⟨121521252489005718081543971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81014168326003812054362647 121521252489005718081543971)
        ·
          refine ⟨182281878733508577122315957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121521252489005718081543971 182281878733508577122315957)
          ·
            refine ⟨17088926131266429105217121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182281878733508577122315957 17088926131266429105217121)
            ·
              refine ⟨12816694598449821828912841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17088926131266429105217121 12816694598449821828912841)
              ·
                refine ⟨9612520948837366371684631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12816694598449821828912841 9612520948837366371684631)
                ·
                  refine ⟨14418781423256049557526947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9612520948837366371684631 14418781423256049557526947)
                  ·
                    refine ⟨21628172134884074336290421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14418781423256049557526947 21628172134884074336290421)
                    ·
                      refine ⟨2027641137645381969027227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21628172134884074336290421 2027641137645381969027227)
                      ·
                        rfl

theorem cell23_3948817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_3948817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948817 prefixEnd_3948817 := by exact prefixLift 3948817
  have htrace : WordTrace (prefixWord ++ tailWord_3948817) baseStart_3948817 baseEnd_3948817 := by
    simpa [prefixWord, tailWord_3948817, baseEnd_3948817] using wordTrace_append hprefix tailTrace_3948817
  have hstable : (prefixWord ++ tailWord_3948817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948817).length < 2 ^ (prefixWord ++ tailWord_3948817).sum := by decide
  have hdescent : baseEnd_3948817 < baseStart_3948817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948824 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 2, 4]
def baseStart_3948824 : Nat := 118140960795 + 3948824 * 2 ^ 59
def prefixEnd_3948824 : Nat := 4983230072969 + 3 ^ 40 * 3948824 * 2
def baseEnd_3948824 : Nat := 675881577336654480546565

theorem tailTrace_3948824 : CollatzResearch.WordTrace tailWord_3948824 prefixEnd_3948824 675881577336654480546565 := by
  unfold tailWord_3948824
  simp only [CollatzResearch.WordTrace]
  refine ⟨72012721723046264146074763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96016962297395018861433017 72012721723046264146074763)
  ·
    refine ⟨108019082584569396219112145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72012721723046264146074763 108019082584569396219112145)
    ·
      refine ⟨81014311938427047164334109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108019082584569396219112145 81014311938427047164334109)
      ·
        refine ⟨30380366976910142686625291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81014311938427047164334109 30380366976910142686625291)
        ·
          refine ⟨45570550465365214029937937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30380366976910142686625291 45570550465365214029937937)
          ·
            refine ⟨34177912849023910522453453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45570550465365214029937937 34177912849023910522453453)
            ·
              refine ⟨12816717318383966445920045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34177912849023910522453453 12816717318383966445920045)
              ·
                refine ⟨4806268994393987417220017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12816717318383966445920045 4806268994393987417220017)
                ·
                  refine ⟨3604701745795490562915013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4806268994393987417220017 3604701745795490562915013)
                  ·
                    refine ⟨675881577336654480546565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3604701745795490562915013 675881577336654480546565)
                    ·
                      rfl

theorem cell23_3948824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_3948824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948824 prefixEnd_3948824 := by exact prefixLift 3948824
  have htrace : WordTrace (prefixWord ++ tailWord_3948824) baseStart_3948824 baseEnd_3948824 := by
    simpa [prefixWord, tailWord_3948824, baseEnd_3948824] using wordTrace_append hprefix tailTrace_3948824
  have hstable : (prefixWord ++ tailWord_3948824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948824).length < 2 ^ (prefixWord ++ tailWord_3948824).sum := by decide
  have hdescent : baseEnd_3948824 < baseStart_3948824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948831 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 4]
def baseStart_3948831 : Nat := 118140960795 + 3948831 * 2 ^ 59
def prefixEnd_3948831 : Nat := 4983230072969 + 3 ^ 40 * 3948831 * 2
def baseEnd_3948831 : Nat := 2027648326374544914252163

theorem tailTrace_3948831 : CollatzResearch.WordTrace tailWord_3948831 prefixEnd_3948831 2027648326374544914252163 := by
  unfold tailWord_3948831
  simp only [CollatzResearch.WordTrace]
  refine ⟨144025698757067168487654347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96017132504711445658436231 144025698757067168487654347)
  ·
    refine ⟨216038548135600752731481521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144025698757067168487654347 216038548135600752731481521)
    ·
      refine ⟨162028911101700564548611141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216038548135600752731481521 162028911101700564548611141)
      ·
        refine ⟨30380420831568855852864589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162028911101700564548611141 30380420831568855852864589)
        ·
          refine ⟨11392657811838320944824221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30380420831568855852864589 11392657811838320944824221)
          ·
            refine ⟨4272246679439370354309083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11392657811838320944824221 4272246679439370354309083)
            ·
              refine ⟨6408370019159055531463625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272246679439370354309083 6408370019159055531463625)
              ·
                refine ⟨4806277514369291648597719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6408370019159055531463625 4806277514369291648597719)
                ·
                  refine ⟨7209416271553937472896579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806277514369291648597719 7209416271553937472896579)
                  ·
                    refine ⟨10814124407330906209344869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7209416271553937472896579 10814124407330906209344869)
                    ·
                      refine ⟨2027648326374544914252163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10814124407330906209344869 2027648326374544914252163)
                      ·
                        rfl

theorem cell23_3948831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_3948831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948831 prefixEnd_3948831 := by exact prefixLift 3948831
  have htrace : WordTrace (prefixWord ++ tailWord_3948831) baseStart_3948831 baseEnd_3948831 := by
    simpa [prefixWord, tailWord_3948831, baseEnd_3948831] using wordTrace_append hprefix tailTrace_3948831
  have hstable : (prefixWord ++ tailWord_3948831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948831).length < 2 ^ (prefixWord ++ tailWord_3948831).sum := by decide
  have hdescent : baseEnd_3948831 < baseStart_3948831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948847 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 3]
def baseStart_3948847 : Nat := 118140960795 + 3948847 * 2 ^ 59
def prefixEnd_3948847 : Nat := 4983230072969 + 3 ^ 40 * 3948847 * 2
def baseEnd_3948847 : Nat := 2027656542065016851652089

theorem tailTrace_3948847 : CollatzResearch.WordTrace tailWord_3948847 prefixEnd_3948847 2027656542065016851652089 := by
  unfold tailWord_3948847
  simp only [CollatzResearch.WordTrace]
  refine ⟨144026282325009203220236795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96017521550006135480157863 144026282325009203220236795)
  ·
    refine ⟨216039423487513804830355193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144026282325009203220236795 216039423487513804830355193)
    ·
      refine ⟨162029567615635353622766395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216039423487513804830355193 162029567615635353622766395)
      ·
        refine ⟨243044351423453030434149593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162029567615635353622766395 243044351423453030434149593)
        ·
          refine ⟨182283263567589772825612195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243044351423453030434149593 182283263567589772825612195)
          ·
            refine ⟨273424895351384659238418293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182283263567589772825612195 273424895351384659238418293)
            ·
              refine ⟨25633583939192311803601715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273424895351384659238418293 25633583939192311803601715)
              ·
                refine ⟨38450375908788467705402573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25633583939192311803601715 38450375908788467705402573)
                ·
                  refine ⟨14418890965795675389525965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38450375908788467705402573 14418890965795675389525965)
                  ·
                    refine ⟨5407084112173378271072237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14418890965795675389525965 5407084112173378271072237)
                    ·
                      refine ⟨2027656542065016851652089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5407084112173378271072237 2027656542065016851652089)
                      ·
                        rfl

theorem cell23_3948847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_3948847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948847 prefixEnd_3948847 := by exact prefixLift 3948847
  have htrace : WordTrace (prefixWord ++ tailWord_3948847) baseStart_3948847 baseEnd_3948847 := by
    simpa [prefixWord, tailWord_3948847, baseEnd_3948847] using wordTrace_append hprefix tailTrace_3948847
  have hstable : (prefixWord ++ tailWord_3948847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948847).length < 2 ^ (prefixWord ++ tailWord_3948847).sum := by decide
  have hdescent : baseEnd_3948847 < baseStart_3948847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948851 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 1, 2, 3]
def baseStart_3948851 : Nat := 118140960795 + 3948851 * 2 ^ 59
def prefixEnd_3948851 : Nat := 4983230072969 + 3 ^ 40 * 3948851 * 2
def baseEnd_3948851 : Nat := 2027658595987634836002071

theorem tailTrace_3948851 : CollatzResearch.WordTrace tailWord_3948851 prefixEnd_3948851 2027658595987634836002071 := by
  unfold tailWord_3948851
  simp only [CollatzResearch.WordTrace]
  refine ⟨144026428216994711903382407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96017618811329807935588271 144026428216994711903382407)
  ·
    refine ⟨216039642325492067855073611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144026428216994711903382407 216039642325492067855073611)
    ·
      refine ⟨324059463488238101782610417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216039642325492067855073611 324059463488238101782610417)
      ·
        refine ⟨243044597616178576336957813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324059463488238101782610417 243044597616178576336957813)
        ·
          refine ⟨22785431026516741531589795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243044597616178576336957813 22785431026516741531589795)
          ·
            refine ⟨34178146539775112297384693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22785431026516741531589795 34178146539775112297384693)
            ·
              refine ⟨3204201238103916777879815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34178146539775112297384693 3204201238103916777879815)
              ·
                refine ⟨4806301857155875166819723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204201238103916777879815 4806301857155875166819723)
                ·
                  refine ⟨7209452785733812750229585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806301857155875166819723 7209452785733812750229585)
                  ·
                    refine ⟨5407089589300359562672189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7209452785733812750229585 5407089589300359562672189)
                    ·
                      refine ⟨2027658595987634836002071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5407089589300359562672189 2027658595987634836002071)
                      ·
                        rfl

theorem cell23_3948851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 2, 3].length) (baseStart_3948851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948851 prefixEnd_3948851 := by exact prefixLift 3948851
  have htrace : WordTrace (prefixWord ++ tailWord_3948851) baseStart_3948851 baseEnd_3948851 := by
    simpa [prefixWord, tailWord_3948851, baseEnd_3948851] using wordTrace_append hprefix tailTrace_3948851
  have hstable : (prefixWord ++ tailWord_3948851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948851).length < 2 ^ (prefixWord ++ tailWord_3948851).sum := by decide
  have hdescent : baseEnd_3948851 < baseStart_3948851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948881 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 3]
def baseStart_3948881 : Nat := 118140960795 + 3948881 * 2 ^ 59
def prefixEnd_3948881 : Nat := 4983230072969 + 3 ^ 40 * 3948881 * 2
def baseEnd_3948881 : Nat := 2027674000407269718626933

theorem tailTrace_3948881 : CollatzResearch.WordTrace tailWord_3948881 prefixEnd_3948881 2027674000407269718626933 := by
  unfold tailWord_3948881
  simp only [CollatzResearch.WordTrace]
  refine ⟨144027522406886027026974497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96018348271257351351316331 144027522406886027026974497)
  ·
    refine ⟨108020641805164520270230873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144027522406886027026974497 108020641805164520270230873)
    ·
      refine ⟨81015481353873390202673155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108020641805164520270230873 81015481353873390202673155)
      ·
        refine ⟨121523222030810085304009733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81015481353873390202673155 121523222030810085304009733)
        ·
          refine ⟨22785604130776890994501825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121523222030810085304009733 22785604130776890994501825)
          ·
            refine ⟨17089203098082668245876369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22785604130776890994501825 17089203098082668245876369)
            ·
              refine ⟨12816902323562001184407277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17089203098082668245876369 12816902323562001184407277)
              ·
                refine ⟨4806338371335750444152729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12816902323562001184407277 4806338371335750444152729)
                ·
                  refine ⟨3604753778501812833114547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4806338371335750444152729 3604753778501812833114547)
                  ·
                    refine ⟨5407130667752719249671821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3604753778501812833114547 5407130667752719249671821)
                    ·
                      refine ⟨2027674000407269718626933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5407130667752719249671821 2027674000407269718626933)
                      ·
                        rfl

theorem cell23_3948881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_3948881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948881 prefixEnd_3948881 := by exact prefixLift 3948881
  have htrace : WordTrace (prefixWord ++ tailWord_3948881) baseStart_3948881 baseEnd_3948881 := by
    simpa [prefixWord, tailWord_3948881, baseEnd_3948881] using wordTrace_append hprefix tailTrace_3948881
  have hstable : (prefixWord ++ tailWord_3948881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948881).length < 2 ^ (prefixWord ++ tailWord_3948881).sum := by decide
  have hdescent : baseEnd_3948881 < baseStart_3948881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948887 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_3948887 : Nat := 118140960795 + 3948887 * 2 ^ 59
def prefixEnd_3948887 : Nat := 4983230072969 + 3 ^ 40 * 3948887 * 2
def baseEnd_3948887 : Nat := 2027677081291196695151905

theorem tailTrace_3948887 : CollatzResearch.WordTrace tailWord_3948887 prefixEnd_3948887 2027677081291196695151905 := by
  unfold tailWord_3948887
  simp only [CollatzResearch.WordTrace]
  refine ⟨144027741244864290051692915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96018494163242860034461943 144027741244864290051692915)
  ·
    refine ⟨216041611867296435077539373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144027741244864290051692915 216041611867296435077539373)
    ·
      refine ⟨81015604450236163154077265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216041611867296435077539373 81015604450236163154077265)
      ·
        refine ⟨60761703337677122365557949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81015604450236163154077265 60761703337677122365557949)
        ·
          refine ⟨22785638751628920887084231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60761703337677122365557949 22785638751628920887084231)
          ·
            refine ⟨34178458127443381330626347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22785638751628920887084231 34178458127443381330626347)
            ·
              refine ⟨51267687191165071995939521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34178458127443381330626347 51267687191165071995939521)
              ·
                refine ⟨38450765393373803996954641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51267687191165071995939521 38450765393373803996954641)
                ·
                  refine ⟨28838074045030352997715981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38450765393373803996954641 28838074045030352997715981)
                  ·
                    refine ⟨10814277766886382374143493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28838074045030352997715981 10814277766886382374143493)
                    ·
                      refine ⟨2027677081291196695151905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10814277766886382374143493 2027677081291196695151905)
                      ·
                        rfl

theorem cell23_3948887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_3948887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948887 prefixEnd_3948887 := by exact prefixLift 3948887
  have htrace : WordTrace (prefixWord ++ tailWord_3948887) baseStart_3948887 baseEnd_3948887 := by
    simpa [prefixWord, tailWord_3948887, baseEnd_3948887] using wordTrace_append hprefix tailTrace_3948887
  have hstable : (prefixWord ++ tailWord_3948887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948887).length < 2 ^ (prefixWord ++ tailWord_3948887).sum := by decide
  have hdescent : baseEnd_3948887 < baseStart_3948887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948907 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 3]
def baseStart_3948907 : Nat := 118140960795 + 3948907 * 2 ^ 59
def prefixEnd_3948907 : Nat := 4983230072969 + 3 ^ 40 * 3948907 * 2
def baseEnd_3948907 : Nat := 2027687350904286616901813

theorem tailTrace_3948907 : CollatzResearch.WordTrace tailWord_3948907 prefixEnd_3948907 2027687350904286616901813 := by
  unfold tailWord_3948907
  simp only [CollatzResearch.WordTrace]
  refine ⟨144028470704791833467420975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96018980469861222311613983 144028470704791833467420975)
  ·
    refine ⟨216042706057187750201131463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144028470704791833467420975 216042706057187750201131463)
    ·
      refine ⟨324064059085781625301697195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216042706057187750201131463 324064059085781625301697195)
      ·
        refine ⟨486096088628672437952545793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324064059085781625301697195 486096088628672437952545793)
        ·
          refine ⟨364572066471504328464409345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486096088628672437952545793 364572066471504328464409345)
          ·
            refine ⟨273429049853628246348307009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364572066471504328464409345 273429049853628246348307009)
            ·
              refine ⟨205071787390221184761230257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273429049853628246348307009 205071787390221184761230257)
              ·
                refine ⟨153803840542665888570922693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205071787390221184761230257 153803840542665888570922693)
                ·
                  refine ⟨28838220101749854107048005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153803840542665888570922693 28838220101749854107048005)
                  ·
                    refine ⟨5407166269078097645071501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28838220101749854107048005 5407166269078097645071501)
                    ·
                      refine ⟨2027687350904286616901813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5407166269078097645071501 2027687350904286616901813)
                      ·
                        rfl

theorem cell23_3948907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 3].length) (baseStart_3948907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948907 prefixEnd_3948907 := by exact prefixLift 3948907
  have htrace : WordTrace (prefixWord ++ tailWord_3948907) baseStart_3948907 baseEnd_3948907 := by
    simpa [prefixWord, tailWord_3948907, baseEnd_3948907] using wordTrace_append hprefix tailTrace_3948907
  have hstable : (prefixWord ++ tailWord_3948907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948907).length < 2 ^ (prefixWord ++ tailWord_3948907).sum := by decide
  have hdescent : baseEnd_3948907 < baseStart_3948907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948908 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 1, 3, 2]
def baseStart_3948908 : Nat := 118140960795 + 3948908 * 2 ^ 59
def prefixEnd_3948908 : Nat := 4983230072969 + 3 ^ 40 * 3948908 * 2
def baseEnd_3948908 : Nat := 2027687864384941112989309

theorem tailTrace_3948908 : CollatzResearch.WordTrace tailWord_3948908 prefixEnd_3948908 2027687864384941112989309 := by
  unfold tailWord_3948908
  simp only [CollatzResearch.WordTrace]
  refine ⟨72014253588894105319103689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96019004785192140425471585 72014253588894105319103689)
  ·
    refine ⟨54010690191670578989327767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72014253588894105319103689 54010690191670578989327767)
    ·
      refine ⟨81016035287505868483991651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54010690191670578989327767 81016035287505868483991651)
      ·
        refine ⟨121524052931258802725987477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81016035287505868483991651 121524052931258802725987477)
        ·
          refine ⟨5696439981152756377780663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121524052931258802725987477 5696439981152756377780663)
          ·
            refine ⟨8544659971729134566670995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696439981152756377780663 8544659971729134566670995)
            ·
              refine ⟨12816989957593701850006493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8544659971729134566670995 12816989957593701850006493)
              ·
                refine ⟨4806371234097638193752435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12816989957593701850006493 4806371234097638193752435)
                ·
                  refine ⟨7209556851146457290628653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806371234097638193752435 7209556851146457290628653)
                  ·
                    refine ⟨2703583819179921483985745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7209556851146457290628653 2703583819179921483985745)
                    ·
                      refine ⟨2027687864384941112989309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703583819179921483985745 2027687864384941112989309)
                      ·
                        rfl

theorem cell23_3948908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_3948908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948908 prefixEnd_3948908 := by exact prefixLift 3948908
  have htrace : WordTrace (prefixWord ++ tailWord_3948908) baseStart_3948908 baseEnd_3948908 := by
    simpa [prefixWord, tailWord_3948908, baseEnd_3948908] using wordTrace_append hprefix tailTrace_3948908
  have hstable : (prefixWord ++ tailWord_3948908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948908).length < 2 ^ (prefixWord ++ tailWord_3948908).sum := by decide
  have hdescent : baseEnd_3948908 < baseStart_3948908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3948997 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_3948997 : Nat := 118140960795 + 3948997 * 2 ^ 59
def prefixEnd_3948997 : Nat := 4983230072969 + 3 ^ 40 * 3948997 * 2
def baseEnd_3948997 : Nat := 2027733564163191264776399

theorem tailTrace_3948997 : CollatzResearch.WordTrace tailWord_3948997 prefixEnd_3948997 2027733564163191264776399 := by
  unfold tailWord_3948997
  simp only [CollatzResearch.WordTrace]
  refine ⟨144031753274465778838197245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96021168849643852558798163 144031753274465778838197245)
  ·
    refine ⟨54011907477924667064323967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144031753274465778838197245 54011907477924667064323967)
    ·
      refine ⟨81017861216887000596485951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54011907477924667064323967 81017861216887000596485951)
      ·
        refine ⟨121526791825330500894728927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81017861216887000596485951 121526791825330500894728927)
        ·
          refine ⟨182290187737995751342093391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121526791825330500894728927 182290187737995751342093391)
          ·
            refine ⟨273435281606993627013140087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182290187737995751342093391 273435281606993627013140087)
            ·
              refine ⟨410152922410490440519710131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273435281606993627013140087 410152922410490440519710131)
              ·
                refine ⟨615229383615735660779565197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410152922410490440519710131 615229383615735660779565197)
                ·
                  refine ⟨230711018855900872792336949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615229383615735660779565197 230711018855900872792336949)
                  ·
                    refine ⟨21629158017740706824281589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 230711018855900872792336949 21629158017740706824281589)
                    ·
                      refine ⟨2027733564163191264776399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21629158017740706824281589 2027733564163191264776399)
                      ·
                        rfl

theorem cell23_3948997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_3948997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3948997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3948997 prefixEnd_3948997 := by exact prefixLift 3948997
  have htrace : WordTrace (prefixWord ++ tailWord_3948997) baseStart_3948997 baseEnd_3948997 := by
    simpa [prefixWord, tailWord_3948997, baseEnd_3948997] using wordTrace_append hprefix tailTrace_3948997
  have hstable : (prefixWord ++ tailWord_3948997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3948997).length < 2 ^ (prefixWord ++ tailWord_3948997).sum := by decide
  have hdescent : baseEnd_3948997 < baseStart_3948997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3948997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949007 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_3949007 : Nat := 118140960795 + 3949007 * 2 ^ 59
def prefixEnd_3949007 : Nat := 4983230072969 + 3 ^ 40 * 3949007 * 2
def baseEnd_3949007 : Nat := 2027738698969736225651353

theorem tailTrace_3949007 : CollatzResearch.WordTrace tailWord_3949007 prefixEnd_3949007 2027738698969736225651353 := by
  unfold tailWord_3949007
  simp only [CollatzResearch.WordTrace]
  refine ⟨144032118004429550546061275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96021412002953033697374183 144032118004429550546061275)
  ·
    refine ⟨216048177006644325819091913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144032118004429550546061275 216048177006644325819091913)
    ·
      refine ⟨162036132754983244364318935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216048177006644325819091913 162036132754983244364318935)
      ·
        refine ⟨243054199132474866546478403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162036132754983244364318935 243054199132474866546478403)
        ·
          refine ⟨364581298698712299819717605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243054199132474866546478403 364581298698712299819717605)
          ·
            refine ⟨68358993506008556216197051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364581298698712299819717605 68358993506008556216197051)
            ·
              refine ⟨102538490259012834324295577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68358993506008556216197051 102538490259012834324295577)
              ·
                refine ⟨76903867694259625743221683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102538490259012834324295577 76903867694259625743221683)
                ·
                  refine ⟨115355801541389438614832525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76903867694259625743221683 115355801541389438614832525)
                  ·
                    refine ⟨43258425578021039480562197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115355801541389438614832525 43258425578021039480562197)
                    ·
                      refine ⟨2027738698969736225651353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43258425578021039480562197 2027738698969736225651353)
                      ·
                        rfl

theorem cell23_3949007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_3949007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949007 prefixEnd_3949007 := by exact prefixLift 3949007
  have htrace : WordTrace (prefixWord ++ tailWord_3949007) baseStart_3949007 baseEnd_3949007 := by
    simpa [prefixWord, tailWord_3949007, baseEnd_3949007] using wordTrace_append hprefix tailTrace_3949007
  have hstable : (prefixWord ++ tailWord_3949007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949007).length < 2 ^ (prefixWord ++ tailWord_3949007).sum := by decide
  have hdescent : baseEnd_3949007 < baseStart_3949007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949031 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3949031 : Nat := 118140960795 + 3949031 * 2 ^ 59
def prefixEnd_3949031 : Nat := 4983230072969 + 3 ^ 40 * 3949031 * 2
def baseEnd_3949031 : Nat := 2027751022505444131751243

theorem tailTrace_3949031 : CollatzResearch.WordTrace tailWord_3949031 prefixEnd_3949031 2027751022505444131751243 := by
  unfold tailWord_3949031
  simp only [CollatzResearch.WordTrace]
  refine ⟨144032993356342602644934947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96021995570895068429956631 144032993356342602644934947)
  ·
    refine ⟨216049490034513903967402421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144032993356342602644934947 216049490034513903967402421)
    ·
      refine ⟨20254639690735678496943977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216049490034513903967402421 20254639690735678496943977)
      ·
        refine ⟨15190979768051758872707983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20254639690735678496943977 15190979768051758872707983)
        ·
          refine ⟨22786469652077638309061975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15190979768051758872707983 22786469652077638309061975)
          ·
            refine ⟨34179704478116457463592963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22786469652077638309061975 34179704478116457463592963)
            ·
              refine ⟨51269556717174686195389445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34179704478116457463592963 51269556717174686195389445)
              ·
                refine ⟨9613041884470253661635521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51269556717174686195389445 9613041884470253661635521)
                ·
                  refine ⟨7209781413352690246226641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9613041884470253661635521 7209781413352690246226641)
                  ·
                    refine ⟨5407336060014517684669981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7209781413352690246226641 5407336060014517684669981)
                    ·
                      refine ⟨2027751022505444131751243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5407336060014517684669981 2027751022505444131751243)
                      ·
                        rfl

theorem cell23_3949031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3949031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949031 prefixEnd_3949031 := by exact prefixLift 3949031
  have htrace : WordTrace (prefixWord ++ tailWord_3949031) baseStart_3949031 baseEnd_3949031 := by
    simpa [prefixWord, tailWord_3949031, baseEnd_3949031] using wordTrace_append hprefix tailTrace_3949031
  have hstable : (prefixWord ++ tailWord_3949031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949031).length < 2 ^ (prefixWord ++ tailWord_3949031).sum := by decide
  have hdescent : baseEnd_3949031 < baseStart_3949031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949045 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_3949045 : Nat := 118140960795 + 3949045 * 2 ^ 59
def prefixEnd_3949045 : Nat := 4983230072969 + 3 ^ 40 * 3949045 * 2
def baseEnd_3949045 : Nat := 2027758211234607076976179

theorem tailTrace_3949045 : CollatzResearch.WordTrace tailWord_3949045 prefixEnd_3949045 2027758211234607076976179 := by
  unfold tailWord_3949045
  simp only [CollatzResearch.WordTrace]
  refine ⟨144033503978291883035944589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96022335985527922023963059 144033503978291883035944589)
  ·
    refine ⟨54012563991859456138479221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144033503978291883035944589 54012563991859456138479221)
    ·
      refine ⟨5063677874236824012982427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54012563991859456138479221 5063677874236824012982427)
      ·
        refine ⟨7595516811355236019473641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063677874236824012982427 7595516811355236019473641)
        ·
          refine ⟨5696637608516427014605231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7595516811355236019473641 5696637608516427014605231)
          ·
            refine ⟨8544956412774640521907847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696637608516427014605231 8544956412774640521907847)
            ·
              refine ⟨12817434619161960782861771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8544956412774640521907847 12817434619161960782861771)
              ·
                refine ⟨19226151928742941174292657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12817434619161960782861771 19226151928742941174292657)
                ·
                  refine ⟨14419613946557205880719493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19226151928742941174292657 14419613946557205880719493)
                  ·
                    refine ⟨2703677614979476102634905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14419613946557205880719493 2703677614979476102634905)
                    ·
                      refine ⟨2027758211234607076976179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703677614979476102634905 2027758211234607076976179)
                      ·
                        rfl

theorem cell23_3949045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_3949045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949045 prefixEnd_3949045 := by exact prefixLift 3949045
  have htrace : WordTrace (prefixWord ++ tailWord_3949045) baseStart_3949045 baseEnd_3949045 := by
    simpa [prefixWord, tailWord_3949045, baseEnd_3949045] using wordTrace_append hprefix tailTrace_3949045
  have hstable : (prefixWord ++ tailWord_3949045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949045).length < 2 ^ (prefixWord ++ tailWord_3949045).sum := by decide
  have hdescent : baseEnd_3949045 < baseStart_3949045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949061 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 3]
def baseStart_3949061 : Nat := 118140960795 + 3949061 * 2 ^ 59
def prefixEnd_3949061 : Nat := 4983230072969 + 3 ^ 40 * 3949061 * 2
def baseEnd_3949061 : Nat := 2027766426925079014376105

theorem tailTrace_3949061 : CollatzResearch.WordTrace tailWord_3949061 prefixEnd_3949061 2027766426925079014376105 := by
  unfold tailWord_3949061
  simp only [CollatzResearch.WordTrace]
  refine ⟨144034087546233917768527037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96022725030822611845684691 144034087546233917768527037)
  ·
    refine ⟨54012782829837719163197639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144034087546233917768527037 54012782829837719163197639)
    ·
      refine ⟨81019174244756578744796459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54012782829837719163197639 81019174244756578744796459)
      ·
        refine ⟨121528761367134868117194689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81019174244756578744796459 121528761367134868117194689)
        ·
          refine ⟨91146571025351151087896017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121528761367134868117194689 91146571025351151087896017)
          ·
            refine ⟨68359928269013363315922013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91146571025351151087896017 68359928269013363315922013)
            ·
              refine ⟨25634973100880011243470755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68359928269013363315922013 25634973100880011243470755)
              ·
                refine ⟨38452459651320016865206133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25634973100880011243470755 38452459651320016865206133)
                ·
                  refine ⟨3604918092311251581113075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38452459651320016865206133 3604918092311251581113075)
                  ·
                    refine ⟨5407377138466877371669613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3604918092311251581113075 5407377138466877371669613)
                    ·
                      refine ⟨2027766426925079014376105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5407377138466877371669613 2027766426925079014376105)
                      ·
                        rfl

theorem cell23_3949061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_3949061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949061 prefixEnd_3949061 := by exact prefixLift 3949061
  have htrace : WordTrace (prefixWord ++ tailWord_3949061) baseStart_3949061 baseEnd_3949061 := by
    simpa [prefixWord, tailWord_3949061, baseEnd_3949061] using wordTrace_append hprefix tailTrace_3949061
  have hstable : (prefixWord ++ tailWord_3949061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949061).length < 2 ^ (prefixWord ++ tailWord_3949061).sum := by decide
  have hdescent : baseEnd_3949061 < baseStart_3949061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949062 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3949062 : Nat := 118140960795 + 3949062 * 2 ^ 59
def prefixEnd_3949062 : Nat := 4983230072969 + 3 ^ 40 * 3949062 * 2
def baseEnd_3949062 : Nat := 2027766940405733510463601

theorem tailTrace_3949062 : CollatzResearch.WordTrace tailWord_3949062 prefixEnd_3949062 2027766940405733510463601 := by
  unfold tailWord_3949062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4501066375600946716853545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96022749346153529959542293 4501066375600946716853545)
  ·
    refine ⟨3375799781700710037640159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4501066375600946716853545 3375799781700710037640159)
    ·
      refine ⟨5063699672551065056460239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375799781700710037640159 5063699672551065056460239)
      ·
        refine ⟨7595549508826597584690359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063699672551065056460239 7595549508826597584690359)
        ·
          refine ⟨11393324263239896377035539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7595549508826597584690359 11393324263239896377035539)
          ·
            refine ⟨17089986394859844565553309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11393324263239896377035539 17089986394859844565553309)
            ·
              refine ⟨6408744898072441712082491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17089986394859844565553309 6408744898072441712082491)
              ·
                refine ⟨9613117347108662568123737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408744898072441712082491 9613117347108662568123737)
                ·
                  refine ⟨7209838010331496926092803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9613117347108662568123737 7209838010331496926092803)
                  ·
                    refine ⟨10814757015497245389139205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7209838010331496926092803 10814757015497245389139205)
                    ·
                      refine ⟨2027766940405733510463601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10814757015497245389139205 2027766940405733510463601)
                      ·
                        rfl

theorem cell23_3949062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3949062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949062 prefixEnd_3949062 := by exact prefixLift 3949062
  have htrace : WordTrace (prefixWord ++ tailWord_3949062) baseStart_3949062 baseEnd_3949062 := by
    simpa [prefixWord, tailWord_3949062, baseEnd_3949062] using wordTrace_append hprefix tailTrace_3949062
  have hstable : (prefixWord ++ tailWord_3949062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949062).length < 2 ^ (prefixWord ++ tailWord_3949062).sum := by decide
  have hdescent : baseEnd_3949062 < baseStart_3949062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949104 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_3949104 : Nat := 118140960795 + 3949104 * 2 ^ 59
def prefixEnd_3949104 : Nat := 4983230072969 + 3 ^ 40 * 3949104 * 2
def baseEnd_3949104 : Nat := 2027788506593222346138407

theorem tailTrace_3949104 : CollatzResearch.WordTrace tailWord_3949104 prefixEnd_3949104 2027788506593222346138407 := by
  unfold tailWord_3949104
  simp only [CollatzResearch.WordTrace]
  refine ⟨72017827942539068056171183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96023770590052090741561577 72017827942539068056171183)
  ·
    refine ⟨108026741913808602084256775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72017827942539068056171183 108026741913808602084256775)
    ·
      refine ⟨162040112870712903126385163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108026741913808602084256775 162040112870712903126385163)
      ·
        refine ⟨243060169306069354689577745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162040112870712903126385163 243060169306069354689577745)
        ·
          refine ⟨182295126979552016017183309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243060169306069354689577745 182295126979552016017183309)
          ·
            refine ⟨68360672617332006006443741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182295126979552016017183309 68360672617332006006443741)
            ·
              refine ⟨25635252231499502252416403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68360672617332006006443741 25635252231499502252416403)
              ·
                refine ⟨38452878347249253378624605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25635252231499502252416403 38452878347249253378624605)
                ·
                  refine ⟨14419829380218470016984227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38452878347249253378624605 14419829380218470016984227)
                  ·
                    refine ⟨21629744070327705025476341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14419829380218470016984227 21629744070327705025476341)
                    ·
                      refine ⟨2027788506593222346138407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21629744070327705025476341 2027788506593222346138407)
                      ·
                        rfl

theorem cell23_3949104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_3949104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949104 prefixEnd_3949104 := by exact prefixLift 3949104
  have htrace : WordTrace (prefixWord ++ tailWord_3949104) baseStart_3949104 baseEnd_3949104 := by
    simpa [prefixWord, tailWord_3949104, baseEnd_3949104] using wordTrace_append hprefix tailTrace_3949104
  have hstable : (prefixWord ++ tailWord_3949104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949104).length < 2 ^ (prefixWord ++ tailWord_3949104).sum := by decide
  have hdescent : baseEnd_3949104 < baseStart_3949104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949138 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_3949138 : Nat := 118140960795 + 3949138 * 2 ^ 59
def prefixEnd_3949138 : Nat := 4983230072969 + 3 ^ 40 * 3949138 * 2
def baseEnd_3949138 : Nat := 2027805964935475213113251

theorem tailTrace_3949138 : CollatzResearch.WordTrace tailWord_3949138 prefixEnd_3949138 2027805964935475213113251 := by
  unfold tailWord_3949138
  simp only [CollatzResearch.WordTrace]
  refine ⟨36009223991738739979770017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96024597311303306612720045 36009223991738739979770017)
  ·
    refine ⟨27006917993804054984827513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36009223991738739979770017 27006917993804054984827513)
    ·
      refine ⟨20255188495353041238620635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27006917993804054984827513 20255188495353041238620635)
      ·
        refine ⟨30382782743029561857930953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20255188495353041238620635 30382782743029561857930953)
        ·
          refine ⟨22787087057272171393448215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30382782743029561857930953 22787087057272171393448215)
          ·
            refine ⟨34180630585908257090172323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22787087057272171393448215 34180630585908257090172323)
            ·
              refine ⟨51270945878862385635258485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34180630585908257090172323 51270945878862385635258485)
              ·
                refine ⟨4806651176143348653305483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51270945878862385635258485 4806651176143348653305483)
                ·
                  refine ⟨7209976764215022979958225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806651176143348653305483 7209976764215022979958225)
                  ·
                    refine ⟨5407482573161267234968669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7209976764215022979958225 5407482573161267234968669)
                    ·
                      refine ⟨2027805964935475213113251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5407482573161267234968669 2027805964935475213113251)
                      ·
                        rfl

theorem cell23_3949138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_3949138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949138 prefixEnd_3949138 := by exact prefixLift 3949138
  have htrace : WordTrace (prefixWord ++ tailWord_3949138) baseStart_3949138 baseEnd_3949138 := by
    simpa [prefixWord, tailWord_3949138, baseEnd_3949138] using wordTrace_append hprefix tailTrace_3949138
  have hstable : (prefixWord ++ tailWord_3949138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949138).length < 2 ^ (prefixWord ++ tailWord_3949138).sum := by decide
  have hdescent : baseEnd_3949138 < baseStart_3949138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949161 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 2, 7, 2]
def baseStart_3949161 : Nat := 118140960795 + 3949161 * 2 ^ 59
def prefixEnd_3949161 : Nat := 4983230072969 + 3 ^ 40 * 3949161 * 2
def baseEnd_3949161 : Nat := 2027817774990528623125645

theorem tailTrace_3949161 : CollatzResearch.WordTrace tailWord_3949161 prefixEnd_3949161 2027817774990528623125645 := by
  unfold tailWord_3949161
  simp only [CollatzResearch.WordTrace]
  refine ⟨144037734845871634847167337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96025156563914423231444891 144037734845871634847167337)
  ·
    refine ⟨108028301134403726135375503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144037734845871634847167337 108028301134403726135375503)
    ·
      refine ⟨162042451701605589203063255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108028301134403726135375503 162042451701605589203063255)
      ·
        refine ⟨243063677552408383804594883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162042451701605589203063255 243063677552408383804594883)
        ·
          refine ⟨364595516328612575706892325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243063677552408383804594883 364595516328612575706892325)
          ·
            refine ⟨68361659311614857945042311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364595516328612575706892325 68361659311614857945042311)
            ·
              refine ⟨102542488967422286917563467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68361659311614857945042311 102542488967422286917563467)
              ·
                refine ⟨153813733451133430376345201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102542488967422286917563467 153813733451133430376345201)
                ·
                  refine ⟨115360300088350072782258901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153813733451133430376345201 115360300088350072782258901)
                  ·
                    refine ⟨2703757033320704830834193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 115360300088350072782258901 2703757033320704830834193)
                    ·
                      refine ⟨2027817774990528623125645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703757033320704830834193 2027817774990528623125645)
                      ·
                        rfl

theorem cell23_3949161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 7, 2].length) (baseStart_3949161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949161 prefixEnd_3949161 := by exact prefixLift 3949161
  have htrace : WordTrace (prefixWord ++ tailWord_3949161) baseStart_3949161 baseEnd_3949161 := by
    simpa [prefixWord, tailWord_3949161, baseEnd_3949161] using wordTrace_append hprefix tailTrace_3949161
  have hstable : (prefixWord ++ tailWord_3949161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949161).length < 2 ^ (prefixWord ++ tailWord_3949161).sum := by decide
  have hdescent : baseEnd_3949161 < baseStart_3949161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949186 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3949186 : Nat := 118140960795 + 3949186 * 2 ^ 59
def prefixEnd_3949186 : Nat := 4983230072969 + 3 ^ 40 * 3949186 * 2
def baseEnd_3949186 : Nat := 2027830612006891025313031

theorem tailTrace_3949186 : CollatzResearch.WordTrace tailWord_3949186 prefixEnd_3949186 2027830612006891025313031 := by
  unfold tailWord_3949186
  simp only [CollatzResearch.WordTrace]
  refine ⟨36009661667695266029206853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96025764447187376077884941 36009661667695266029206853)
  ·
    refine ⟨6751811562692862380476285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36009661667695266029206853 6751811562692862380476285)
    ·
      refine ⟨2531929336009823392678607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6751811562692862380476285 2531929336009823392678607)
      ·
        refine ⟨3797894004014735089017911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531929336009823392678607 3797894004014735089017911)
        ·
          refine ⟨5696841006022102633526867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3797894004014735089017911 5696841006022102633526867)
          ·
            refine ⟨8545261509033153950290301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696841006022102633526867 8545261509033153950290301)
            ·
              refine ⟨3204473065887432731358863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8545261509033153950290301 3204473065887432731358863)
              ·
                refine ⟨4806709598831149097038295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204473065887432731358863 4806709598831149097038295)
                ·
                  refine ⟨7210064398246723645557443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806709598831149097038295 7210064398246723645557443)
                  ·
                    refine ⟨10815096597370085468336165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7210064398246723645557443 10815096597370085468336165)
                    ·
                      refine ⟨2027830612006891025313031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10815096597370085468336165 2027830612006891025313031)
                      ·
                        rfl

theorem cell23_3949186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3949186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949186 prefixEnd_3949186 := by exact prefixLift 3949186
  have htrace : WordTrace (prefixWord ++ tailWord_3949186) baseStart_3949186 baseEnd_3949186 := by
    simpa [prefixWord, tailWord_3949186, baseEnd_3949186] using wordTrace_append hprefix tailTrace_3949186
  have hstable : (prefixWord ++ tailWord_3949186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949186).length < 2 ^ (prefixWord ++ tailWord_3949186).sum := by decide
  have hdescent : baseEnd_3949186 < baseStart_3949186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949202 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3949202 : Nat := 118140960795 + 3949202 * 2 ^ 59
def prefixEnd_3949202 : Nat := 4983230072969 + 3 ^ 40 * 3949202 * 2
def baseEnd_3949202 : Nat := 2027838827697362962712957

theorem tailTrace_3949202 : CollatzResearch.WordTrace tailWord_3949202 prefixEnd_3949202 2027838827697362962712957 := by
  unfold tailWord_3949202
  simp only [CollatzResearch.WordTrace]
  refine ⟨36009807559680774712352465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96026153492482065899606573 36009807559680774712352465)
  ·
    refine ⟨27007355669760581034264349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36009807559680774712352465 27007355669760581034264349)
    ·
      refine ⟨10127758376160217887849131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27007355669760581034264349 10127758376160217887849131)
      ·
        refine ⟨15191637564240326831773697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10127758376160217887849131 15191637564240326831773697)
        ·
          refine ⟨11393728173180245123830273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15191637564240326831773697 11393728173180245123830273)
          ·
            refine ⟨8545296129885183842872705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11393728173180245123830273 8545296129885183842872705)
            ·
              refine ⟨6408972097413887882154529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8545296129885183842872705 6408972097413887882154529)
              ·
                refine ⟨4806729073060415911615897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6408972097413887882154529 4806729073060415911615897)
                ·
                  refine ⟨3605046804795311933711923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4806729073060415911615897 3605046804795311933711923)
                  ·
                    refine ⟨5407570207192967900567885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3605046804795311933711923 5407570207192967900567885)
                    ·
                      refine ⟨2027838827697362962712957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5407570207192967900567885 2027838827697362962712957)
                      ·
                        rfl

theorem cell23_3949202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3949202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949202 prefixEnd_3949202 := by exact prefixLift 3949202
  have htrace : WordTrace (prefixWord ++ tailWord_3949202) baseStart_3949202 baseEnd_3949202 := by
    simpa [prefixWord, tailWord_3949202, baseEnd_3949202] using wordTrace_append hprefix tailTrace_3949202
  have hstable : (prefixWord ++ tailWord_3949202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949202).length < 2 ^ (prefixWord ++ tailWord_3949202).sum := by decide
  have hdescent : baseEnd_3949202 < baseStart_3949202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949208 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 3, 4, 2]
def baseStart_3949208 : Nat := 118140960795 + 3949208 * 2 ^ 59
def prefixEnd_3949208 : Nat := 4983230072969 + 3 ^ 40 * 3949208 * 2
def baseEnd_3949208 : Nat := 2027841908581289939237929

theorem tailTrace_3949208 : CollatzResearch.WordTrace tailWord_3949208 prefixEnd_3949208 2027841908581289939237929 := by
  unfold tailWord_3949208
  simp only [CollatzResearch.WordTrace]
  refine ⟨72019724538350680937064139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96026299384467574582752185 72019724538350680937064139)
  ·
    refine ⟨108029586807526021405596209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72019724538350680937064139 108029586807526021405596209)
    ·
      refine ⟨81022190105644516054197157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108029586807526021405596209 81022190105644516054197157)
      ·
        refine ⟨15191660644808346760161967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81022190105644516054197157 15191660644808346760161967)
        ·
          refine ⟨22787490967212520140242951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15191660644808346760161967 22787490967212520140242951)
          ·
            refine ⟨34181236450818780210364427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22787490967212520140242951 34181236450818780210364427)
            ·
              refine ⟨51271854676228170315546641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34181236450818780210364427 51271854676228170315546641)
              ·
                refine ⟨38453891007171127736659981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51271854676228170315546641 38453891007171127736659981)
                ·
                  refine ⟨14420209127689172901247493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38453891007171127736659981 14420209127689172901247493)
                  ·
                    refine ⟨2703789211441719918983905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14420209127689172901247493 2703789211441719918983905)
                    ·
                      refine ⟨2027841908581289939237929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703789211441719918983905 2027841908581289939237929)
                      ·
                        rfl

theorem cell23_3949208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_3949208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949208 prefixEnd_3949208 := by exact prefixLift 3949208
  have htrace : WordTrace (prefixWord ++ tailWord_3949208) baseStart_3949208 baseEnd_3949208 := by
    simpa [prefixWord, tailWord_3949208, baseEnd_3949208] using wordTrace_append hprefix tailTrace_3949208
  have hstable : (prefixWord ++ tailWord_3949208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949208).length < 2 ^ (prefixWord ++ tailWord_3949208).sum := by decide
  have hdescent : baseEnd_3949208 < baseStart_3949208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949231 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 7]
def baseStart_3949231 : Nat := 118140960795 + 3949231 * 2 ^ 59
def prefixEnd_3949231 : Nat := 4983230072969 + 3 ^ 40 * 3949231 * 2
def baseEnd_3949231 : Nat := 225317079848482594361147

theorem tailTrace_3949231 : CollatzResearch.WordTrace tailWord_3949231 prefixEnd_3949231 225317079848482594361147 := by
  unfold tailWord_3949231
  simp only [CollatzResearch.WordTrace]
  refine ⟨144040287955618036802215547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96026858637078691201477031 144040287955618036802215547)
  ·
    refine ⟨216060431933427055203323321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144040287955618036802215547 216060431933427055203323321)
    ·
      refine ⟨162045323950070291402492491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216060431933427055203323321 162045323950070291402492491)
      ·
        refine ⟨243067985925105437103738737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162045323950070291402492491 243067985925105437103738737)
        ·
          refine ⟨182300989443829077827804053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243067985925105437103738737 182300989443829077827804053)
          ·
            refine ⟨8545358880179488023178315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182300989443829077827804053 8545358880179488023178315)
            ·
              refine ⟨12818038320269232034767473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8545358880179488023178315 12818038320269232034767473)
              ·
                refine ⟨9613528740201924026075605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12818038320269232034767473 9613528740201924026075605)
                ·
                  refine ⟨225317079848482594361147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9613528740201924026075605 225317079848482594361147)
                  ·
                    rfl

theorem cell23_3949231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 7].length) (baseStart_3949231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949231 prefixEnd_3949231 := by exact prefixLift 3949231
  have htrace : WordTrace (prefixWord ++ tailWord_3949231) baseStart_3949231 baseEnd_3949231 := by
    simpa [prefixWord, tailWord_3949231, baseEnd_3949231] using wordTrace_append hprefix tailTrace_3949231
  have hstable : (prefixWord ++ tailWord_3949231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949231).length < 2 ^ (prefixWord ++ tailWord_3949231).sum := by decide
  have hdescent : baseEnd_3949231 < baseStart_3949231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949241 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 3]
def baseStart_3949241 : Nat := 118140960795 + 3949241 * 2 ^ 59
def prefixEnd_3949241 : Nat := 4983230072969 + 3 ^ 40 * 3949241 * 2
def baseEnd_3949241 : Nat := 2027858853442888310125277

theorem tailTrace_3949241 : CollatzResearch.WordTrace tailWord_3949241 prefixEnd_3949241 2027858853442888310125277 := by
  unfold tailWord_3949241
  simp only [CollatzResearch.WordTrace]
  refine ⟨144040652685581808510079577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96027101790387872340053051 144040652685581808510079577)
  ·
    refine ⟨108030489514186356382559683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144040652685581808510079577 108030489514186356382559683)
    ·
      refine ⟨162045734271279534573839525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108030489514186356382559683 162045734271279534573839525)
      ·
        refine ⟨30383575175864912732594911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162045734271279534573839525 30383575175864912732594911)
        ·
          refine ⟨45575362763797369098892367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30383575175864912732594911 45575362763797369098892367)
          ·
            refine ⟨68363044145696053648338551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45575362763797369098892367 68363044145696053648338551)
            ·
              refine ⟨102544566218544080472507827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68363044145696053648338551 102544566218544080472507827)
              ·
                refine ⟨153816849327816120708761741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102544566218544080472507827 153816849327816120708761741)
                ·
                  refine ⟨57681318497931045265785653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153816849327816120708761741 57681318497931045265785653)
                  ·
                    refine ⟨5407623609181035493667405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57681318497931045265785653 5407623609181035493667405)
                    ·
                      refine ⟨2027858853442888310125277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5407623609181035493667405 2027858853442888310125277)
                      ·
                        rfl

theorem cell23_3949241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_3949241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949241 prefixEnd_3949241 := by exact prefixLift 3949241
  have htrace : WordTrace (prefixWord ++ tailWord_3949241) baseStart_3949241 baseEnd_3949241 := by
    simpa [prefixWord, tailWord_3949241, baseEnd_3949241] using wordTrace_append hprefix tailTrace_3949241
  have hstable : (prefixWord ++ tailWord_3949241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949241).length < 2 ^ (prefixWord ++ tailWord_3949241).sum := by decide
  have hdescent : baseEnd_3949241 < baseStart_3949241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949248 : List Nat := [2, 1, 1, 2, 4, 2, 1, 5, 5]
def baseStart_3949248 : Nat := 118140960795 + 3949248 * 2 ^ 59
def prefixEnd_3949248 : Nat := 4983230072969 + 3 ^ 40 * 3949248 * 2
def baseEnd_3949248 : Nat := 225318049756385531415305

theorem tailTrace_3949248 : CollatzResearch.WordTrace tailWord_3949248 prefixEnd_3949248 225318049756385531415305 := by
  unfold tailWord_3949248
  simp only [CollatzResearch.WordTrace]
  refine ⟨72020453998278224352792199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96027271997704299137056265 72020453998278224352792199)
  ·
    refine ⟨108030680997417336529188299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72020453998278224352792199 108030680997417336529188299)
    ·
      refine ⟨162046021496126004793782449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108030680997417336529188299 162046021496126004793782449)
      ·
        refine ⟨121534516122094503595336837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162046021496126004793782449 121534516122094503595336837)
        ·
          refine ⟨22787721772892719424125657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121534516122094503595336837 22787721772892719424125657)
          ·
            refine ⟨17090791329669539568094243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22787721772892719424125657 17090791329669539568094243)
            ·
              refine ⟨25636186994504309352141365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17090791329669539568094243 25636186994504309352141365)
              ·
                refine ⟨2403392530734779001763253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25636186994504309352141365 2403392530734779001763253)
                ·
                  refine ⟨225318049756385531415305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2403392530734779001763253 225318049756385531415305)
                  ·
                    rfl

theorem cell23_3949248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 5].length) (baseStart_3949248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949248 prefixEnd_3949248 := by exact prefixLift 3949248
  have htrace : WordTrace (prefixWord ++ tailWord_3949248) baseStart_3949248 baseEnd_3949248 := by
    simpa [prefixWord, tailWord_3949248, baseEnd_3949248] using wordTrace_append hprefix tailTrace_3949248
  have hstable : (prefixWord ++ tailWord_3949248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949248).length < 2 ^ (prefixWord ++ tailWord_3949248).sum := by decide
  have hdescent : baseEnd_3949248 < baseStart_3949248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949258 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_3949258 : Nat := 118140960795 + 3949258 * 2 ^ 59
def prefixEnd_3949258 : Nat := 4983230072969 + 3 ^ 40 * 3949258 * 2
def baseEnd_3949258 : Nat := 2027867582614014743612699

theorem tailTrace_3949258 : CollatzResearch.WordTrace tailWord_3949258 prefixEnd_3949258 2027867582614014743612699 := by
  unfold tailWord_3949258
  simp only [CollatzResearch.WordTrace]
  refine ⟨36010318181630055103362107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96027515151013480275632285 36010318181630055103362107)
  ·
    refine ⟨54015477272445082655043161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36010318181630055103362107 54015477272445082655043161)
    ·
      refine ⟨40511607954333811991282371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54015477272445082655043161 40511607954333811991282371)
      ·
        refine ⟨60767411931500717986923557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40511607954333811991282371 60767411931500717986923557)
        ·
          refine ⟨11393889737156384622548167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60767411931500717986923557 11393889737156384622548167)
          ·
            refine ⟨17090834605734576933822251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11393889737156384622548167 17090834605734576933822251)
            ·
              refine ⟨25636251908601865400733377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17090834605734576933822251 25636251908601865400733377)
              ·
                refine ⟨19227188931451399050550033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25636251908601865400733377 19227188931451399050550033)
                ·
                  refine ⟨14420391698588549287912525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19227188931451399050550033 14420391698588549287912525)
                  ·
                    refine ⟨5407646886970705982967197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14420391698588549287912525 5407646886970705982967197)
                    ·
                      refine ⟨2027867582614014743612699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5407646886970705982967197 2027867582614014743612699)
                      ·
                        rfl

theorem cell23_3949258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_3949258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949258 prefixEnd_3949258 := by exact prefixLift 3949258
  have htrace : WordTrace (prefixWord ++ tailWord_3949258) baseStart_3949258 baseEnd_3949258 := by
    simpa [prefixWord, tailWord_3949258, baseEnd_3949258] using wordTrace_append hprefix tailTrace_3949258
  have hstable : (prefixWord ++ tailWord_3949258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949258).length < 2 ^ (prefixWord ++ tailWord_3949258).sum := by decide
  have hdescent : baseEnd_3949258 < baseStart_3949258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949276 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_3949276 : Nat := 118140960795 + 3949276 * 2 ^ 59
def prefixEnd_3949276 : Nat := 4983230072969 + 3 ^ 40 * 3949276 * 2
def baseEnd_3949276 : Nat := 2027876825265795673187617

theorem tailTrace_3949276 : CollatzResearch.WordTrace tailWord_3949276 prefixEnd_3949276 2027876825265795673187617 := by
  unfold tailWord_3949276
  simp only [CollatzResearch.WordTrace]
  refine ⟨72020964620227504743801841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96027952826970006325069121 72020964620227504743801841)
  ·
    refine ⟨54015723465170628557851381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72020964620227504743801841 54015723465170628557851381)
    ·
      refine ⟨5063974074859746427298567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54015723465170628557851381 5063974074859746427298567)
      ·
        refine ⟨7595961112289619640947851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063974074859746427298567 7595961112289619640947851)
        ·
          refine ⟨11393941668434429461421777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7595961112289619640947851 11393941668434429461421777)
          ·
            refine ⟨8545456251325822096066333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11393941668434429461421777 8545456251325822096066333)
            ·
              refine ⟨3204546094247183286024875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8545456251325822096066333 3204546094247183286024875)
              ·
                refine ⟨4806819141370774929037313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204546094247183286024875 4806819141370774929037313)
                ·
                  refine ⟨3605114356028081196777985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4806819141370774929037313 3605114356028081196777985)
                  ·
                    refine ⟨2703835767021060897583489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3605114356028081196777985 2703835767021060897583489)
                    ·
                      refine ⟨2027876825265795673187617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703835767021060897583489 2027876825265795673187617)
                      ·
                        rfl

theorem cell23_3949276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_3949276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949276 prefixEnd_3949276 := by exact prefixLift 3949276
  have htrace : WordTrace (prefixWord ++ tailWord_3949276) baseStart_3949276 baseEnd_3949276 := by
    simpa [prefixWord, tailWord_3949276, baseEnd_3949276] using wordTrace_append hprefix tailTrace_3949276
  have hstable : (prefixWord ++ tailWord_3949276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949276).length < 2 ^ (prefixWord ++ tailWord_3949276).sum := by decide
  have hdescent : baseEnd_3949276 < baseStart_3949276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949298 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3949298 : Nat := 118140960795 + 3949298 * 2 ^ 59
def prefixEnd_3949298 : Nat := 4983230072969 + 3 ^ 40 * 3949298 * 2
def baseEnd_3949298 : Nat := 2027888121840194587112515

theorem tailTrace_3949298 : CollatzResearch.WordTrace tailWord_3949298 prefixEnd_3949298 2027888121840194587112515 := by
  unfold tailWord_3949298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36010682911593826811226137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96028487764250204829936365 36010682911593826811226137)
  ·
    refine ⟨27008012183695370108419603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36010682911593826811226137 27008012183695370108419603)
    ·
      refine ⟨40512018275543055162629405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27008012183695370108419603 40512018275543055162629405)
      ·
        refine ⟨15192006853328645685986027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40512018275543055162629405 15192006853328645685986027)
        ·
          refine ⟨22788010279992968528979041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15192006853328645685986027 22788010279992968528979041)
          ·
            refine ⟨17091007709994726396734281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22788010279992968528979041 17091007709994726396734281)
            ·
              refine ⟨12818255782496044797550711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17091007709994726396734281 12818255782496044797550711)
              ·
                refine ⟨19227383673744067196326067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12818255782496044797550711 19227383673744067196326067)
                ·
                  refine ⟨28841075510616100794489101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19227383673744067196326067 28841075510616100794489101)
                  ·
                    refine ⟨10815403316481037797933413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28841075510616100794489101 10815403316481037797933413)
                    ·
                      refine ⟨2027888121840194587112515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10815403316481037797933413 2027888121840194587112515)
                      ·
                        rfl

theorem cell23_3949298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3949298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949298 prefixEnd_3949298 := by exact prefixLift 3949298
  have htrace : WordTrace (prefixWord ++ tailWord_3949298) baseStart_3949298 baseEnd_3949298 := by
    simpa [prefixWord, tailWord_3949298, baseEnd_3949298] using wordTrace_append hprefix tailTrace_3949298
  have hstable : (prefixWord ++ tailWord_3949298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949298).length < 2 ^ (prefixWord ++ tailWord_3949298).sum := by decide
  have hdescent : baseEnd_3949298 < baseStart_3949298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949321 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 8]
def baseStart_3949321 : Nat := 118140960795 + 3949321 * 2 ^ 59
def prefixEnd_3949321 : Nat := 4983230072969 + 3 ^ 40 * 3949321 * 2
def baseEnd_3949321 : Nat := 225322214655027555236101

theorem tailTrace_3949321 : CollatzResearch.WordTrace tailWord_3949321 prefixEnd_3949321 225322214655027555236101 := by
  unfold tailWord_3949321
  simp only [CollatzResearch.WordTrace]
  refine ⟨144043570525291982172991817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96029047016861321448661211 144043570525291982172991817)
  ·
    refine ⟨108032677893968986629743863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144043570525291982172991817 108032677893968986629743863)
    ·
      refine ⟨162049016840953479944615795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108032677893968986629743863 162049016840953479944615795)
      ·
        refine ⟨243073525261430219916923693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162049016840953479944615795 243073525261430219916923693)
        ·
          refine ⟨91152571973036332468846385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243073525261430219916923693 91152571973036332468846385)
          ·
            refine ⟨68364428979777249351634789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91152571973036332468846385 68364428979777249351634789)
            ·
              refine ⟨12818330433708234253431523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68364428979777249351634789 12818330433708234253431523)
              ·
                refine ⟨19227495650562351380147285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12818330433708234253431523 19227495650562351380147285)
                ·
                  refine ⟨225322214655027555236101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19227495650562351380147285 225322214655027555236101)
                  ·
                    rfl

theorem cell23_3949321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 8].length) (baseStart_3949321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949321 prefixEnd_3949321 := by exact prefixLift 3949321
  have htrace : WordTrace (prefixWord ++ tailWord_3949321) baseStart_3949321 baseEnd_3949321 := by
    simpa [prefixWord, tailWord_3949321, baseEnd_3949321] using wordTrace_append hprefix tailTrace_3949321
  have hstable : (prefixWord ++ tailWord_3949321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949321).length < 2 ^ (prefixWord ++ tailWord_3949321).sum := by decide
  have hdescent : baseEnd_3949321 < baseStart_3949321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949338 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 6]
def baseStart_3949338 : Nat := 118140960795 + 3949338 * 2 ^ 59
def prefixEnd_3949338 : Nat := 4983230072969 + 3 ^ 40 * 3949338 * 2
def baseEnd_3949338 : Nat := 225323184562930492290259

theorem tailTrace_3949338 : CollatzResearch.WordTrace tailWord_3949338 prefixEnd_3949338 225323184562930492290259 := by
  unfold tailWord_3949338
  simp only [CollatzResearch.WordTrace]
  refine ⟨36011047641557598519090167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96029460377486929384240445 36011047641557598519090167)
  ·
    refine ⟨54016571462336397778635251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36011047641557598519090167 54016571462336397778635251)
    ·
      refine ⟨81024857193504596667952877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54016571462336397778635251 81024857193504596667952877)
      ·
        refine ⟨30384321447564223750482329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81024857193504596667952877 30384321447564223750482329)
        ·
          refine ⟨22788241085673167812861747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30384321447564223750482329 22788241085673167812861747)
          ·
            refine ⟨34182361628509751719292621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22788241085673167812861747 34182361628509751719292621)
            ·
              refine ⟨12818385610691156894734733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34182361628509751719292621 12818385610691156894734733)
              ·
                refine ⟨4806894604009183835525525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12818385610691156894734733 4806894604009183835525525)
                ·
                  refine ⟨225323184562930492290259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4806894604009183835525525 225323184562930492290259)
                  ·
                    rfl

theorem cell23_3949338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_3949338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949338 prefixEnd_3949338 := by exact prefixLift 3949338
  have htrace : WordTrace (prefixWord ++ tailWord_3949338) baseStart_3949338 baseEnd_3949338 := by
    simpa [prefixWord, tailWord_3949338, baseEnd_3949338] using wordTrace_append hprefix tailTrace_3949338
  have hstable : (prefixWord ++ tailWord_3949338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949338).length < 2 ^ (prefixWord ++ tailWord_3949338).sum := by decide
  have hdescent : baseEnd_3949338 < baseStart_3949338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949439 : List Nat := [1, 1, 2, 2, 1, 1, 6, 4, 1, 2, 2]
def baseStart_3949439 : Nat := 118140960795 + 3949439 * 2 ^ 59
def prefixEnd_3949439 : Nat := 4983230072969 + 3 ^ 40 * 3949439 * 2
def baseEnd_3949439 : Nat := 2027960522612478535449367

theorem tailTrace_3949439 : CollatzResearch.WordTrace tailWord_3949439 prefixEnd_3949439 2027960522612478535449367 := by
  unfold tailWord_3949439
  simp only [CollatzResearch.WordTrace]
  refine ⟨144047874338864488325787371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96031916225909658883858247 144047874338864488325787371)
  ·
    refine ⟨216071811508296732488681057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144047874338864488325787371 216071811508296732488681057)
    ·
      refine ⟨162053858631222549366510793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216071811508296732488681057 162053858631222549366510793)
      ·
        refine ⟨121540393973416912024883095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162053858631222549366510793 121540393973416912024883095)
        ·
          refine ⟨182310590960125368037324643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121540393973416912024883095 182310590960125368037324643)
          ·
            refine ⟨273465886440188052055986965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182310590960125368037324643 273465886440188052055986965)
            ·
              refine ⟨12818713426883814940124389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 273465886440188052055986965 12818713426883814940124389)
              ·
                refine ⟨2403508767540715301273323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12818713426883814940124389 2403508767540715301273323)
                ·
                  refine ⟨3605263151311072951909985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403508767540715301273323 3605263151311072951909985)
                  ·
                    refine ⟨2703947363483304713932489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3605263151311072951909985 2703947363483304713932489)
                    ·
                      refine ⟨2027960522612478535449367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703947363483304713932489 2027960522612478535449367)
                      ·
                        rfl

theorem cell23_3949439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 2, 2].length) (baseStart_3949439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949439 prefixEnd_3949439 := by exact prefixLift 3949439
  have htrace : WordTrace (prefixWord ++ tailWord_3949439) baseStart_3949439 baseEnd_3949439 := by
    simpa [prefixWord, tailWord_3949439, baseEnd_3949439] using wordTrace_append hprefix tailTrace_3949439
  have hstable : (prefixWord ++ tailWord_3949439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949439).length < 2 ^ (prefixWord ++ tailWord_3949439).sum := by decide
  have hdescent : baseEnd_3949439 < baseStart_3949439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949473 : List Nat := [1, 2, 3, 4, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3949473 : Nat := 118140960795 + 3949473 * 2 ^ 59
def prefixEnd_3949473 : Nat := 4983230072969 + 3 ^ 40 * 3949473 * 2
def baseEnd_3949473 : Nat := 2027977980954731402424211

theorem tailTrace_3949473 : CollatzResearch.WordTrace tailWord_3949473 prefixEnd_3949473 2027977980954731402424211 := by
  unfold tailWord_3949473
  simp only [CollatzResearch.WordTrace]
  refine ⟨144049114420741312132525073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96032742947160874755016715 144049114420741312132525073)
  ·
    refine ⟨108036835815555984099393805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144049114420741312132525073 108036835815555984099393805)
    ·
      refine ⟨40513813430833494037272677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108036835815555984099393805 40513813430833494037272677)
      ·
        refine ⟨7596340018281280131988627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40513813430833494037272677 7596340018281280131988627)
        ·
          refine ⟨11394510027421920197982941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7596340018281280131988627 11394510027421920197982941)
          ·
            refine ⟨4272941260283220074243603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11394510027421920197982941 4272941260283220074243603)
            ·
              refine ⟨6409411890424830111365405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272941260283220074243603 6409411890424830111365405)
              ·
                refine ⟨2403529458909311291762027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6409411890424830111365405 2403529458909311291762027)
                ·
                  refine ⟨3605294188363966937643041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403529458909311291762027 3605294188363966937643041)
                  ·
                    refine ⟨2703970641272975203232281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3605294188363966937643041 2703970641272975203232281)
                    ·
                      refine ⟨2027977980954731402424211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2703970641272975203232281 2027977980954731402424211)
                      ·
                        rfl

theorem cell23_3949473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3949473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949473 prefixEnd_3949473 := by exact prefixLift 3949473
  have htrace : WordTrace (prefixWord ++ tailWord_3949473) baseStart_3949473 baseEnd_3949473 := by
    simpa [prefixWord, tailWord_3949473, baseEnd_3949473] using wordTrace_append hprefix tailTrace_3949473
  have hstable : (prefixWord ++ tailWord_3949473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949473).length < 2 ^ (prefixWord ++ tailWord_3949473).sum := by decide
  have hdescent : baseEnd_3949473 < baseStart_3949473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949498 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_3949498 : Nat := 118140960795 + 3949498 * 2 ^ 59
def prefixEnd_3949498 : Nat := 4983230072969 + 3 ^ 40 * 3949498 * 2
def baseEnd_3949498 : Nat := 2027990817971093804611595

theorem tailTrace_3949498 : CollatzResearch.WordTrace tailWord_3949498 prefixEnd_3949498 2027990817971093804611595 := by
  unfold tailWord_3949498
  simp only [CollatzResearch.WordTrace]
  refine ⟨36012506561412685350546287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96033350830433827601456765 36012506561412685350546287)
  ·
    refine ⟨54018759842119028025819431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36012506561412685350546287 54018759842119028025819431)
    ·
      refine ⟨81028139763178542038729147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54018759842119028025819431 81028139763178542038729147)
      ·
        refine ⟨121542209644767813058093721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81028139763178542038729147 121542209644767813058093721)
        ·
          refine ⟨91156657233575859793570291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121542209644767813058093721 91156657233575859793570291)
          ·
            refine ⟨136734985850363789690355437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91156657233575859793570291 136734985850363789690355437)
            ·
              refine ⟨51275619693886421133883289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136734985850363789690355437 51275619693886421133883289)
              ·
                refine ⟨38456714770414815850412467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51275619693886421133883289 38456714770414815850412467)
                ·
                  refine ⟨57685072155622223775618701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38456714770414815850412467 57685072155622223775618701)
                  ·
                    refine ⟨21631902058358333915857013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57685072155622223775618701 21631902058358333915857013)
                    ·
                      refine ⟨2027990817971093804611595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21631902058358333915857013 2027990817971093804611595)
                      ·
                        rfl

theorem cell23_3949498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_3949498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949498 prefixEnd_3949498 := by exact prefixLift 3949498
  have htrace : WordTrace (prefixWord ++ tailWord_3949498) baseStart_3949498 baseEnd_3949498 := by
    simpa [prefixWord, tailWord_3949498, baseEnd_3949498] using wordTrace_append hprefix tailTrace_3949498
  have hstable : (prefixWord ++ tailWord_3949498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949498).length < 2 ^ (prefixWord ++ tailWord_3949498).sum := by decide
  have hdescent : baseEnd_3949498 < baseStart_3949498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949546 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_3949546 : Nat := 118140960795 + 3949546 * 2 ^ 59
def prefixEnd_3949546 : Nat := 4983230072969 + 3 ^ 40 * 3949546 * 2
def baseEnd_3949546 : Nat := 2028015465042509616811375

theorem tailTrace_3949546 : CollatzResearch.WordTrace tailWord_3949546 prefixEnd_3949546 2028015465042509616811375 := by
  unfold tailWord_3949546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36012944237369211399983123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96034517966317897066621661 36012944237369211399983123)
  ·
    refine ⟨54019416356053817099974685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36012944237369211399983123 54019416356053817099974685)
    ·
      refine ⟨20257281133520181412490507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54019416356053817099974685 20257281133520181412490507)
      ·
        refine ⟨30385921700280272118735761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20257281133520181412490507 30385921700280272118735761)
        ·
          refine ⟨22789441275210204089051821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30385921700280272118735761 22789441275210204089051821)
          ·
            refine ⟨8546040478203826533394433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22789441275210204089051821 8546040478203826533394433)
            ·
              refine ⟨6409530358652869900045825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8546040478203826533394433 6409530358652869900045825)
              ·
                refine ⟨4807147768989652425034369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409530358652869900045825 4807147768989652425034369)
                ·
                  refine ⟨3605360826742239318775777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4807147768989652425034369 3605360826742239318775777)
                  ·
                    refine ⟨2704020620056679489081833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3605360826742239318775777 2704020620056679489081833)
                    ·
                      refine ⟨2028015465042509616811375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2704020620056679489081833 2028015465042509616811375)
                      ·
                        rfl

theorem cell23_3949546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_3949546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949546 prefixEnd_3949546 := by exact prefixLift 3949546
  have htrace : WordTrace (prefixWord ++ tailWord_3949546) baseStart_3949546 baseEnd_3949546 := by
    simpa [prefixWord, tailWord_3949546, baseEnd_3949546] using wordTrace_append hprefix tailTrace_3949546
  have hstable : (prefixWord ++ tailWord_3949546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949546).length < 2 ^ (prefixWord ++ tailWord_3949546).sum := by decide
  have hdescent : baseEnd_3949546 < baseStart_3949546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949548 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_3949548 : Nat := 118140960795 + 3949548 * 2 ^ 59
def prefixEnd_3949548 : Nat := 4983230072969 + 3 ^ 40 * 3949548 * 2
def baseEnd_3949548 : Nat := 676005497334606202995455

theorem tailTrace_3949548 : CollatzResearch.WordTrace tailWord_3949548 prefixEnd_3949548 676005497334606202995455 := by
  unfold tailWord_3949548
  simp only [CollatzResearch.WordTrace]
  refine ⟨72025924947734799970752649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96034566596979733294336865 72025924947734799970752649)
  ·
    refine ⟨54019443710801099978064487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72025924947734799970752649 54019443710801099978064487)
    ·
      refine ⟨81029165566201649967096731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54019443710801099978064487 81029165566201649967096731)
      ·
        refine ⟨121543748349302474950645097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81029165566201649967096731 121543748349302474950645097)
        ·
          refine ⟨91157811261976856212983823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121543748349302474950645097 91157811261976856212983823)
          ·
            refine ⟨136736716892965284319475735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91157811261976856212983823 136736716892965284319475735)
            ·
              refine ⟨205105075339447926479213603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136736716892965284319475735 205105075339447926479213603)
              ·
                refine ⟨307657613009171889718820405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205105075339447926479213603 307657613009171889718820405)
                ·
                  refine ⟨28842901219609864661139413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 307657613009171889718820405 28842901219609864661139413)
                  ·
                    refine ⟨676005497334606202995455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28842901219609864661139413 676005497334606202995455)
                    ·
                      rfl

theorem cell23_3949548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_3949548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949548 prefixEnd_3949548 := by exact prefixLift 3949548
  have htrace : WordTrace (prefixWord ++ tailWord_3949548) baseStart_3949548 baseEnd_3949548 := by
    simpa [prefixWord, tailWord_3949548, baseEnd_3949548] using wordTrace_append hprefix tailTrace_3949548
  have hstable : (prefixWord ++ tailWord_3949548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949548).length < 2 ^ (prefixWord ++ tailWord_3949548).sum := by decide
  have hdescent : baseEnd_3949548 < baseStart_3949548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949582 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_3949582 : Nat := 118140960795 + 3949582 * 2 ^ 59
def prefixEnd_3949582 : Nat := 4983230072969 + 3 ^ 40 * 3949582 * 2
def baseEnd_3949582 : Nat := 676011316782023825320403

theorem tailTrace_3949582 : CollatzResearch.WordTrace tailWord_3949582 prefixEnd_3949582 676011316782023825320403 := by
  unfold tailWord_3949582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18006636247168302968530375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96035393318230949165495333 18006636247168302968530375)
  ·
    refine ⟨27009954370752454452795563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18006636247168302968530375 27009954370752454452795563)
    ·
      refine ⟨40514931556128681679193345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27009954370752454452795563 40514931556128681679193345)
      ·
        refine ⟨30386198667096511259395009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40514931556128681679193345 30386198667096511259395009)
        ·
          refine ⟨22789649000322383444546257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30386198667096511259395009 22789649000322383444546257)
          ·
            refine ⟨17092236750241787583409693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22789649000322383444546257 17092236750241787583409693)
            ·
              refine ⟨6409588781340670343778635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17092236750241787583409693 6409588781340670343778635)
              ·
                refine ⟨9614383172011005515667953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6409588781340670343778635 9614383172011005515667953)
                ·
                  refine ⟨7210787379008254136750965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9614383172011005515667953 7210787379008254136750965)
                  ·
                    refine ⟨676011316782023825320403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7210787379008254136750965 676011316782023825320403)
                    ·
                      rfl

theorem cell23_3949582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_3949582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949582 prefixEnd_3949582 := by exact prefixLift 3949582
  have htrace : WordTrace (prefixWord ++ tailWord_3949582) baseStart_3949582 baseEnd_3949582 := by
    simpa [prefixWord, tailWord_3949582, baseEnd_3949582] using wordTrace_append hprefix tailTrace_3949582
  have hstable : (prefixWord ++ tailWord_3949582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949582).length < 2 ^ (prefixWord ++ tailWord_3949582).sum := by decide
  have hdescent : baseEnd_3949582 < baseStart_3949582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949612 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_3949612 : Nat := 118140960795 + 3949612 * 2 ^ 59
def prefixEnd_3949612 : Nat := 4983230072969 + 3 ^ 40 * 3949612 * 2
def baseEnd_3949612 : Nat := 676016451588568786195357

theorem tailTrace_3949612 : CollatzResearch.WordTrace tailWord_3949612 prefixEnd_3949612 676016451588568786195357 := by
  unfold tailWord_3949612
  simp only [CollatzResearch.WordTrace]
  refine ⟨72027092083618869435917545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96036122778158492581223393 72027092083618869435917545)
  ·
    refine ⟨54020319062714152076938159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72027092083618869435917545 54020319062714152076938159)
    ·
      refine ⟨81030478594071228115407239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54020319062714152076938159 81030478594071228115407239)
      ·
        refine ⟨121545717891106842173110859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81030478594071228115407239 121545717891106842173110859)
        ·
          refine ⟨182318576836660263259666289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121545717891106842173110859 182318576836660263259666289)
          ·
            refine ⟨136738932627495197444749717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182318576836660263259666289 136738932627495197444749717)
            ·
              refine ⟨6409637466913837380222643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136738932627495197444749717 6409637466913837380222643)
              ·
                refine ⟨9614456200370756070333965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6409637466913837380222643 9614456200370756070333965)
                ·
                  refine ⟨3605421075139033526375237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9614456200370756070333965 3605421075139033526375237)
                  ·
                    refine ⟨676016451588568786195357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3605421075139033526375237 676016451588568786195357)
                    ·
                      rfl

theorem cell23_3949612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_3949612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949612 prefixEnd_3949612 := by exact prefixLift 3949612
  have htrace : WordTrace (prefixWord ++ tailWord_3949612) baseStart_3949612 baseEnd_3949612 := by
    simpa [prefixWord, tailWord_3949612, baseEnd_3949612] using wordTrace_append hprefix tailTrace_3949612
  have hstable : (prefixWord ++ tailWord_3949612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949612).length < 2 ^ (prefixWord ++ tailWord_3949612).sum := by decide
  have hdescent : baseEnd_3949612 < baseStart_3949612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949635 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 3]
def baseStart_3949635 : Nat := 118140960795 + 3949635 * 2 ^ 59
def prefixEnd_3949635 : Nat := 4983230072969 + 3 ^ 40 * 3949635 * 2
def baseEnd_3949635 : Nat := 2028061164820759768598465

theorem tailTrace_3949635 : CollatzResearch.WordTrace tailWord_3949635 prefixEnd_3949635 2028061164820759768598465 := by
  unfold tailWord_3949635
  simp only [CollatzResearch.WordTrace]
  refine ⟨144055023046154413799922359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96036682030769609199948239 144055023046154413799922359)
  ·
    refine ⟨216082534569231620699883539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144055023046154413799922359 216082534569231620699883539)
    ·
      refine ⟨324123801853847431049825309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216082534569231620699883539 324123801853847431049825309)
      ·
        refine ⟨121546425695192786643684491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324123801853847431049825309 121546425695192786643684491)
        ·
          refine ⟨182319638542789179965526737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121546425695192786643684491 182319638542789179965526737)
          ·
            refine ⟨136739728907091884974145053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182319638542789179965526737 136739728907091884974145053)
            ·
              refine ⟨51277398340159456865304395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136739728907091884974145053 51277398340159456865304395)
              ·
                refine ⟨76916097510239185297956593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51277398340159456865304395 76916097510239185297956593)
                ·
                  refine ⟨57687073132679388973467445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76916097510239185297956593 57687073132679388973467445)
                  ·
                    refine ⟨5408163106188692716262573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57687073132679388973467445 5408163106188692716262573)
                    ·
                      refine ⟨2028061164820759768598465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5408163106188692716262573 2028061164820759768598465)
                      ·
                        rfl

theorem cell23_3949635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_3949635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949635 prefixEnd_3949635 := by exact prefixLift 3949635
  have htrace : WordTrace (prefixWord ++ tailWord_3949635) baseStart_3949635 baseEnd_3949635 := by
    simpa [prefixWord, tailWord_3949635, baseEnd_3949635] using wordTrace_append hprefix tailTrace_3949635
  have hstable : (prefixWord ++ tailWord_3949635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949635).length < 2 ^ (prefixWord ++ tailWord_3949635).sum := by decide
  have hdescent : baseEnd_3949635 < baseStart_3949635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
