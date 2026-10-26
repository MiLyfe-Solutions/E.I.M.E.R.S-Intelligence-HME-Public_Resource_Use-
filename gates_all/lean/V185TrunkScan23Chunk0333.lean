import V185TrunkScan23Chunk0332

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1968551 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_1968551 : Nat := 118140960795 + 1968551 * 2 ^ 59
def prefixEnd_1968551 : Nat := 4983230072969 + 3 ^ 40 * 1968551 * 2
def baseEnd_1968551 : Nat := 1010812855889032768859305

theorem tailTrace_1968551 : CollatzResearch.WordTrace tailWord_1968551 prefixEnd_1968551 1010812855889032768859305 := by
  unfold tailWord_1968551
  simp only [CollatzResearch.WordTrace]
  refine ⟨71798953491283403589521507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47865968994188935726347671 71798953491283403589521507)
  ·
    refine ⟨107698430236925105384282261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71798953491283403589521507 107698430236925105384282261)
    ·
      refine ⟨5048363917355864314888231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107698430236925105384282261 5048363917355864314888231)
      ·
        refine ⟨7572545876033796472332347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048363917355864314888231 7572545876033796472332347)
        ·
          refine ⟨11358818814050694708498521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572545876033796472332347 11358818814050694708498521)
          ·
            refine ⟨8519114110538021031373891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358818814050694708498521 8519114110538021031373891)
            ·
              refine ⟨12778671165807031547060837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8519114110538021031373891 12778671165807031547060837)
              ·
                refine ⟨2396000843588818415073907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12778671165807031547060837 2396000843588818415073907)
                ·
                  refine ⟨3594001265383227622610861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396000843588818415073907 3594001265383227622610861)
                  ·
                    refine ⟨1347750474518710358479073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3594001265383227622610861 1347750474518710358479073)
                    ·
                      refine ⟨1010812855889032768859305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347750474518710358479073 1010812855889032768859305)
                      ·
                        rfl

theorem cell23_1968551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_1968551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968551 prefixEnd_1968551 := by exact prefixLift 1968551
  have htrace : WordTrace (prefixWord ++ tailWord_1968551) baseStart_1968551 baseEnd_1968551 := by
    simpa [prefixWord, tailWord_1968551, baseEnd_1968551] using wordTrace_append hprefix tailTrace_1968551
  have hstable : (prefixWord ++ tailWord_1968551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968551).length < 2 ^ (prefixWord ++ tailWord_1968551).sum := by decide
  have hdescent : baseEnd_1968551 < baseStart_1968551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968567 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_1968567 : Nat := 118140960795 + 1968567 * 2 ^ 59
def prefixEnd_1968567 : Nat := 4983230072969 + 3 ^ 40 * 1968567 * 2
def baseEnd_1968567 : Nat := 1010821071579504706259231

theorem tailTrace_1968567 : CollatzResearch.WordTrace tailWord_1968567 prefixEnd_1968567 1010821071579504706259231 := by
  unfold tailWord_1968567
  simp only [CollatzResearch.WordTrace]
  refine ⟨71799537059225438322103955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47866358039483625548069303 71799537059225438322103955)
  ·
    refine ⟨107699305588838157483155933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71799537059225438322103955 107699305588838157483155933)
    ·
      refine ⟨40387239595814309056183475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107699305588838157483155933 40387239595814309056183475)
      ·
        refine ⟨60580859393721463584275213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40387239595814309056183475 60580859393721463584275213)
        ·
          refine ⟨22717822272645548844103205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60580859393721463584275213 22717822272645548844103205)
          ·
            refine ⟨4259591676121040408269351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22717822272645548844103205 4259591676121040408269351)
            ·
              refine ⟨6389387514181560612404027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4259591676121040408269351 6389387514181560612404027)
              ·
                refine ⟨9584081271272340918606041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389387514181560612404027 9584081271272340918606041)
                ·
                  refine ⟨7188060953454255688954531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9584081271272340918606041 7188060953454255688954531)
                  ·
                    refine ⟨10782091430181383533431797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7188060953454255688954531 10782091430181383533431797)
                    ·
                      refine ⟨1010821071579504706259231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10782091430181383533431797 1010821071579504706259231)
                      ·
                        rfl

theorem cell23_1968567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_1968567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968567 prefixEnd_1968567 := by exact prefixLift 1968567
  have htrace : WordTrace (prefixWord ++ tailWord_1968567) baseStart_1968567 baseEnd_1968567 := by
    simpa [prefixWord, tailWord_1968567, baseEnd_1968567] using wordTrace_append hprefix tailTrace_1968567
  have hstable : (prefixWord ++ tailWord_1968567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968567).length < 2 ^ (prefixWord ++ tailWord_1968567).sum := by decide
  have hdescent : baseEnd_1968567 < baseStart_1968567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968570 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 9]
def baseStart_1968570 : Nat := 118140960795 + 1968570 * 2 ^ 59
def prefixEnd_1968570 : Nat := 4983230072969 + 3 ^ 40 * 1968570 * 2
def baseEnd_1968570 : Nat := 112313623557940910502413

theorem tailTrace_1968570 : CollatzResearch.WordTrace tailWord_1968570 prefixEnd_1968570 112313623557940910502413 := by
  unfold tailWord_1968570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17949911619553642458615791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47866430985476379889642109 17949911619553642458615791)
  ·
    refine ⟨26924867429330463687923687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17949911619553642458615791 26924867429330463687923687)
    ·
      refine ⟨40387301143995695531885531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26924867429330463687923687 40387301143995695531885531)
      ·
        refine ⟨60580951715993543297828297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40387301143995695531885531 60580951715993543297828297)
        ·
          refine ⟨45435713786995157473371223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60580951715993543297828297 45435713786995157473371223)
          ·
            refine ⟨68153570680492736210056835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45435713786995157473371223 68153570680492736210056835)
            ·
              refine ⟨102230356020739104315085253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68153570680492736210056835 102230356020739104315085253)
              ·
                refine ⟨19168191753888582059078485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102230356020739104315085253 19168191753888582059078485)
                ·
                  refine ⟨112313623557940910502413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19168191753888582059078485 112313623557940910502413)
                  ·
                    rfl

theorem cell23_1968570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_1968570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968570 prefixEnd_1968570 := by exact prefixLift 1968570
  have htrace : WordTrace (prefixWord ++ tailWord_1968570) baseStart_1968570 baseEnd_1968570 := by
    simpa [prefixWord, tailWord_1968570, baseEnd_1968570] using wordTrace_append hprefix tailTrace_1968570
  have hstable : (prefixWord ++ tailWord_1968570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968570).length < 2 ^ (prefixWord ++ tailWord_1968570).sum := by decide
  have hdescent : baseEnd_1968570 < baseStart_1968570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968644 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1968644 : Nat := 118140960795 + 1968644 * 2 ^ 59
def prefixEnd_1968644 : Nat := 4983230072969 + 3 ^ 40 * 1968644 * 2
def baseEnd_1968644 : Nat := 1010860609589900904996377

theorem tailTrace_1968644 : CollatzResearch.WordTrace tailWord_1968644 prefixEnd_1968644 1010860609589900904996377 := by
  unfold tailWord_1968644
  simp only [CollatzResearch.WordTrace]
  refine ⟨35901172739973240236328493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47868230319964320315104657 35901172739973240236328493)
  ·
    refine ⟨13462939777489965088623185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35901172739973240236328493 13462939777489965088623185)
    ·
      refine ⟨10097204833117473816467389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13462939777489965088623185 10097204833117473816467389)
      ·
        refine ⟨3786451812419052681175271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10097204833117473816467389 3786451812419052681175271)
        ·
          refine ⟨5679677718628579021762907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3786451812419052681175271 5679677718628579021762907)
          ·
            refine ⟨8519516577942868532644361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679677718628579021762907 8519516577942868532644361)
            ·
              refine ⟨6389637433457151399483271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8519516577942868532644361 6389637433457151399483271)
              ·
                refine ⟨9584456150185727099224907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389637433457151399483271 9584456150185727099224907)
                ·
                  refine ⟨14376684225278590648837361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9584456150185727099224907 14376684225278590648837361)
                  ·
                    refine ⟨10782513168958942986628021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14376684225278590648837361 10782513168958942986628021)
                    ·
                      refine ⟨1010860609589900904996377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10782513168958942986628021 1010860609589900904996377)
                      ·
                        rfl

theorem cell23_1968644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1968644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968644 prefixEnd_1968644 := by exact prefixLift 1968644
  have htrace : WordTrace (prefixWord ++ tailWord_1968644) baseStart_1968644 baseEnd_1968644 := by
    simpa [prefixWord, tailWord_1968644, baseEnd_1968644] using wordTrace_append hprefix tailTrace_1968644
  have hstable : (prefixWord ++ tailWord_1968644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968644).length < 2 ^ (prefixWord ++ tailWord_1968644).sum := by decide
  have hdescent : baseEnd_1968644 < baseStart_1968644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968664 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 5, 4]
def baseStart_1968664 : Nat := 118140960795 + 1968664 * 2 ^ 59
def prefixEnd_1968664 : Nat := 4983230072969 + 3 ^ 40 * 1968664 * 2
def baseEnd_1968664 : Nat := 336956959734330275582095

theorem tailTrace_1968664 : CollatzResearch.WordTrace tailWord_1968664 prefixEnd_1968664 336956959734330275582095 := by
  unfold tailWord_1968664
  simp only [CollatzResearch.WordTrace]
  refine ⟨35901537469937011944192523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47868716626582682592256697 35901537469937011944192523)
  ·
    refine ⟨53852306204905517916288785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35901537469937011944192523 53852306204905517916288785)
    ·
      refine ⟨40389229653679138437216589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53852306204905517916288785 40389229653679138437216589)
      ·
        refine ⟨15145961120129676913956221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40389229653679138437216589 15145961120129676913956221)
        ·
          refine ⟨5679735420048628842733583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15145961120129676913956221 5679735420048628842733583)
          ·
            refine ⟨8519603130072943264100375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679735420048628842733583 8519603130072943264100375)
            ·
              refine ⟨12779404695109414896150563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8519603130072943264100375 12779404695109414896150563)
              ·
                refine ⟨19169107042664122344225845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12779404695109414896150563 19169107042664122344225845)
                ·
                  refine ⟨1797103785249761469771173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19169107042664122344225845 1797103785249761469771173)
                  ·
                    refine ⟨336956959734330275582095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797103785249761469771173 336956959734330275582095)
                    ·
                      rfl

theorem cell23_1968664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_1968664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968664 prefixEnd_1968664 := by exact prefixLift 1968664
  have htrace : WordTrace (prefixWord ++ tailWord_1968664) baseStart_1968664 baseEnd_1968664 := by
    simpa [prefixWord, tailWord_1968664, baseEnd_1968664] using wordTrace_append hprefix tailTrace_1968664
  have hstable : (prefixWord ++ tailWord_1968664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968664).length < 2 ^ (prefixWord ++ tailWord_1968664).sum := by decide
  have hdescent : baseEnd_1968664 < baseStart_1968664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968687 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 3]
def baseStart_1968687 : Nat := 118140960795 + 1968687 * 2 ^ 59
def prefixEnd_1968687 : Nat := 4983230072969 + 3 ^ 40 * 1968687 * 2
def baseEnd_1968687 : Nat := 1010882689258044236758679

theorem tailTrace_1968687 : CollatzResearch.WordTrace tailWord_1968687 prefixEnd_1968687 1010882689258044236758679 := by
  unfold tailWord_1968687
  simp only [CollatzResearch.WordTrace]
  refine ⟨71803913818790698816472315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47869275879193799210981543 71803913818790698816472315)
  ·
    refine ⟨107705870728186048224708473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71803913818790698816472315 107705870728186048224708473)
    ·
      refine ⟨80779403046139536168531355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107705870728186048224708473 80779403046139536168531355)
      ·
        refine ⟨121169104569209304252797033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80779403046139536168531355 121169104569209304252797033)
        ·
          refine ⟨90876828426906978189597775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121169104569209304252797033 90876828426906978189597775)
          ·
            refine ⟨136315242640360467284396663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90876828426906978189597775 136315242640360467284396663)
            ·
              refine ⟨204472863960540700926594995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136315242640360467284396663 204472863960540700926594995)
              ·
                refine ⟨306709295940811051389892493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204472863960540700926594995 306709295940811051389892493)
                ·
                  refine ⟨115015985977804144271209685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306709295940811051389892493 115015985977804144271209685)
                  ·
                    refine ⟨2695687171354784631356477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 115015985977804144271209685 2695687171354784631356477)
                    ·
                      refine ⟨1010882689258044236758679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2695687171354784631356477 1010882689258044236758679)
                      ·
                        rfl

theorem cell23_1968687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_1968687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968687 prefixEnd_1968687 := by exact prefixLift 1968687
  have htrace : WordTrace (prefixWord ++ tailWord_1968687) baseStart_1968687 baseEnd_1968687 := by
    simpa [prefixWord, tailWord_1968687, baseEnd_1968687] using wordTrace_append hprefix tailTrace_1968687
  have hstable : (prefixWord ++ tailWord_1968687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968687).length < 2 ^ (prefixWord ++ tailWord_1968687).sum := by decide
  have hdescent : baseEnd_1968687 < baseStart_1968687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968697 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1968697 : Nat := 118140960795 + 1968697 * 2 ^ 59
def prefixEnd_1968697 : Nat := 4983230072969 + 3 ^ 40 * 1968697 * 2
def baseEnd_1968697 : Nat := 1010887824064589197633633

theorem tailTrace_1968697 : CollatzResearch.WordTrace tailWord_1968697 prefixEnd_1968697 1010887824064589197633633 := by
  unfold tailWord_1968697
  simp only [CollatzResearch.WordTrace]
  refine ⟨71804278548754470524336345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47869519032502980349557563 71804278548754470524336345)
  ·
    refine ⟨53853208911565852893252259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71804278548754470524336345 53853208911565852893252259)
    ·
      refine ⟨80779813367348779339878389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53853208911565852893252259 80779813367348779339878389)
      ·
        refine ⟨7573107503188948063113599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80779813367348779339878389 7573107503188948063113599)
        ·
          refine ⟨11359661254783422094670399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7573107503188948063113599 11359661254783422094670399)
          ·
            refine ⟨17039491882175133142005599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11359661254783422094670399 17039491882175133142005599)
            ·
              refine ⟨25559237823262699713008399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17039491882175133142005599 25559237823262699713008399)
              ·
                refine ⟨38338856734894049569512599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25559237823262699713008399 38338856734894049569512599)
                ·
                  refine ⟨57508285102341074354268899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38338856734894049569512599 57508285102341074354268899)
                  ·
                    refine ⟨86262427653511611531403349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57508285102341074354268899 86262427653511611531403349)
                    ·
                      refine ⟨1010887824064589197633633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 86262427653511611531403349 1010887824064589197633633)
                      ·
                        rfl

theorem cell23_1968697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1968697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968697 prefixEnd_1968697 := by exact prefixLift 1968697
  have htrace : WordTrace (prefixWord ++ tailWord_1968697) baseStart_1968697 baseEnd_1968697 := by
    simpa [prefixWord, tailWord_1968697, baseEnd_1968697] using wordTrace_append hprefix tailTrace_1968697
  have hstable : (prefixWord ++ tailWord_1968697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968697).length < 2 ^ (prefixWord ++ tailWord_1968697).sum := by decide
  have hdescent : baseEnd_1968697 < baseStart_1968697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968707 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 5, 5]
def baseStart_1968707 : Nat := 118140960795 + 1968707 * 2 ^ 59
def prefixEnd_1968707 : Nat := 4983230072969 + 3 ^ 40 * 1968707 * 2
def baseEnd_1968707 : Nat := 336964319623711386169529

theorem tailTrace_1968707 : CollatzResearch.WordTrace tailWord_1968707 prefixEnd_1968707 336964319623711386169529 := by
  unfold tailWord_1968707
  simp only [CollatzResearch.WordTrace]
  refine ⟨71804643278718242232200375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47869762185812161488133583 71804643278718242232200375)
  ·
    refine ⟨107706964918077363348300563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71804643278718242232200375 107706964918077363348300563)
    ·
      refine ⟨161560447377116045022450845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107706964918077363348300563 161560447377116045022450845)
      ·
        refine ⟨60585167766418516883419067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161560447377116045022450845 60585167766418516883419067)
        ·
          refine ⟨90877751649627775325128601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60585167766418516883419067 90877751649627775325128601)
          ·
            refine ⟨68158313737220831493846451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90877751649627775325128601 68158313737220831493846451)
            ·
              refine ⟨102237470605831247240769677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68158313737220831493846451 102237470605831247240769677)
              ·
                refine ⟨38339051477186717715288629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102237470605831247240769677 38339051477186717715288629)
                ·
                  refine ⟨3594286075986254785808309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38339051477186717715288629 3594286075986254785808309)
                  ·
                    refine ⟨336964319623711386169529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3594286075986254785808309 336964319623711386169529)
                    ·
                      rfl

theorem cell23_1968707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 5].length) (baseStart_1968707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968707 prefixEnd_1968707 := by exact prefixLift 1968707
  have htrace : WordTrace (prefixWord ++ tailWord_1968707) baseStart_1968707 baseEnd_1968707 := by
    simpa [prefixWord, tailWord_1968707, baseEnd_1968707] using wordTrace_append hprefix tailTrace_1968707
  have hstable : (prefixWord ++ tailWord_1968707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968707).length < 2 ^ (prefixWord ++ tailWord_1968707).sum := by decide
  have hdescent : baseEnd_1968707 < baseStart_1968707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968711 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 6]
def baseStart_1968711 : Nat := 118140960795 + 1968711 * 2 ^ 59
def prefixEnd_1968711 : Nat := 4983230072969 + 3 ^ 40 * 1968711 * 2
def baseEnd_1968711 : Nat := 112321668088194682539841

theorem tailTrace_1968711 : CollatzResearch.WordTrace tailWord_1968711 prefixEnd_1968711 112321668088194682539841 := by
  unfold tailWord_1968711
  simp only [CollatzResearch.WordTrace]
  refine ⟨71804789170703750915345987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47869859447135833943563991 71804789170703750915345987)
  ·
    refine ⟨107707183756055626373018981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71804789170703750915345987 107707183756055626373018981)
    ·
      refine ⟨20195096954260429944941059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107707183756055626373018981 20195096954260429944941059)
      ·
        refine ⟨30292645431390644917411589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20195096954260429944941059 30292645431390644917411589)
        ·
          refine ⟨5679871018385745922014673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30292645431390644917411589 5679871018385745922014673)
          ·
            refine ⟨4259903263789309441511005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5679871018385745922014673 4259903263789309441511005)
            ·
              refine ⟨1597463723920991040566627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4259903263789309441511005 1597463723920991040566627)
              ·
                refine ⟨2396195585881486560849941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597463723920991040566627 2396195585881486560849941)
                ·
                  refine ⟨112321668088194682539841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2396195585881486560849941 112321668088194682539841)
                  ·
                    rfl

theorem cell23_1968711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 6].length) (baseStart_1968711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968711 prefixEnd_1968711 := by exact prefixLift 1968711
  have htrace : WordTrace (prefixWord ++ tailWord_1968711) baseStart_1968711 baseEnd_1968711 := by
    simpa [prefixWord, tailWord_1968711, baseEnd_1968711] using wordTrace_append hprefix tailTrace_1968711
  have hstable : (prefixWord ++ tailWord_1968711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968711).length < 2 ^ (prefixWord ++ tailWord_1968711).sum := by decide
  have hdescent : baseEnd_1968711 < baseStart_1968711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968721 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 3]
def baseStart_1968721 : Nat := 118140960795 + 1968721 * 2 ^ 59
def prefixEnd_1968721 : Nat := 4983230072969 + 3 ^ 40 * 1968721 * 2
def baseEnd_1968721 : Nat := 1010900147600297103733523

theorem tailTrace_1968721 : CollatzResearch.WordTrace tailWord_1968721 prefixEnd_1968721 1010900147600297103733523 := by
  unfold tailWord_1968721
  simp only [CollatzResearch.WordTrace]
  refine ⟨71805153900667522623210017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47870102600445015082140011 71805153900667522623210017)
  ·
    refine ⟨53853865425500641967407513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71805153900667522623210017 53853865425500641967407513)
    ·
      refine ⟨40390399069125481475555635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53853865425500641967407513 40390399069125481475555635)
      ·
        refine ⟨60585598603688222213333453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40390399069125481475555635 60585598603688222213333453)
        ·
          refine ⟨22719599476383083330000045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60585598603688222213333453 22719599476383083330000045)
          ·
            refine ⟨8519849803643656248750017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22719599476383083330000045 8519849803643656248750017)
            ·
              refine ⟨6389887352732742186562513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8519849803643656248750017 6389887352732742186562513)
              ·
                refine ⟨4792415514549556639921885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6389887352732742186562513 4792415514549556639921885)
                ·
                  refine ⟨1797155817956083739970707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4792415514549556639921885 1797155817956083739970707)
                  ·
                    refine ⟨2695733726934125609956061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1797155817956083739970707 2695733726934125609956061)
                    ·
                      refine ⟨1010900147600297103733523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2695733726934125609956061 1010900147600297103733523)
                      ·
                        rfl

theorem cell23_1968721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_1968721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968721 prefixEnd_1968721 := by exact prefixLift 1968721
  have htrace : WordTrace (prefixWord ++ tailWord_1968721) baseStart_1968721 baseEnd_1968721 := by
    simpa [prefixWord, tailWord_1968721, baseEnd_1968721] using wordTrace_append hprefix tailTrace_1968721
  have hstable : (prefixWord ++ tailWord_1968721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968721).length < 2 ^ (prefixWord ++ tailWord_1968721).sum := by decide
  have hdescent : baseEnd_1968721 < baseStart_1968721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968732 : List Nat := [2, 2, 4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1968732 : Nat := 118140960795 + 1968732 * 2 ^ 59
def prefixEnd_1968732 : Nat := 4983230072969 + 3 ^ 40 * 1968732 * 2
def baseEnd_1968732 : Nat := 336968598629165520231991

theorem tailTrace_1968732 : CollatzResearch.WordTrace tailWord_1968732 prefixEnd_1968732 336968598629165520231991 := by
  unfold tailWord_1968732
  simp only [CollatzResearch.WordTrace]
  refine ⟨35902777551813835750930225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47870370069085114334573633 35902777551813835750930225)
  ·
    refine ⟨26927083163860376813197669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35902777551813835750930225 26927083163860376813197669)
    ·
      refine ⟨5048828093223820652474563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26927083163860376813197669 5048828093223820652474563)
      ·
        refine ⟨7573242139835730978711845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048828093223820652474563 7573242139835730978711845)
        ·
          refine ⟨1419982901219199558508471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7573242139835730978711845 1419982901219199558508471)
          ·
            refine ⟨2129974351828799337762707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419982901219199558508471 2129974351828799337762707)
            ·
              refine ⟨3194961527743199006644061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129974351828799337762707 3194961527743199006644061)
              ·
                refine ⟨1198110572903699627491523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3194961527743199006644061 1198110572903699627491523)
                ·
                  refine ⟨1797165859355549441237285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198110572903699627491523 1797165859355549441237285)
                  ·
                    refine ⟨336968598629165520231991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797165859355549441237285 336968598629165520231991)
                    ·
                      rfl

theorem cell23_1968732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1968732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968732 prefixEnd_1968732 := by exact prefixLift 1968732
  have htrace : WordTrace (prefixWord ++ tailWord_1968732) baseStart_1968732 baseEnd_1968732 := by
    simpa [prefixWord, tailWord_1968732, baseEnd_1968732] using wordTrace_append hprefix tailTrace_1968732
  have hstable : (prefixWord ++ tailWord_1968732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968732).length < 2 ^ (prefixWord ++ tailWord_1968732).sum := by decide
  have hdescent : baseEnd_1968732 < baseStart_1968732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968764 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1968764 : Nat := 118140960795 + 1968764 * 2 ^ 59
def prefixEnd_1968764 : Nat := 4983230072969 + 3 ^ 40 * 1968764 * 2
def baseEnd_1968764 : Nat := 1010922227268440435495825

theorem tailTrace_1968764 : CollatzResearch.WordTrace tailWord_1968764 prefixEnd_1968764 1010922227268440435495825 := by
  unfold tailWord_1968764
  simp only [CollatzResearch.WordTrace]
  refine ⟨35903361119755870483512673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47871148159674493978016897 35903361119755870483512673)
  ·
    refine ⟨26927520839816902862634505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35903361119755870483512673 26927520839816902862634505)
    ·
      refine ⟨20195640629862677146975879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26927520839816902862634505 20195640629862677146975879)
      ·
        refine ⟨30293460944794015720463819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20195640629862677146975879 30293460944794015720463819)
        ·
          refine ⟨45440191417191023580695729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30293460944794015720463819 45440191417191023580695729)
          ·
            refine ⟨34080143562893267685521797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45440191417191023580695729 34080143562893267685521797)
            ·
              refine ⟨6390026918042487691035337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34080143562893267685521797 6390026918042487691035337)
              ·
                refine ⟨4792520188531865768276503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6390026918042487691035337 4792520188531865768276503)
                ·
                  refine ⟨7188780282797798652414755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792520188531865768276503 7188780282797798652414755)
                  ·
                    refine ⟨10783170424196697978622133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7188780282797798652414755 10783170424196697978622133)
                    ·
                      refine ⟨1010922227268440435495825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10783170424196697978622133 1010922227268440435495825)
                      ·
                        rfl

theorem cell23_1968764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1968764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968764 prefixEnd_1968764 := by exact prefixLift 1968764
  have htrace : WordTrace (prefixWord ++ tailWord_1968764) baseStart_1968764 baseEnd_1968764 := by
    simpa [prefixWord, tailWord_1968764, baseEnd_1968764] using wordTrace_append hprefix tailTrace_1968764
  have hstable : (prefixWord ++ tailWord_1968764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968764).length < 2 ^ (prefixWord ++ tailWord_1968764).sum := by decide
  have hdescent : baseEnd_1968764 < baseStart_1968764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968787 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 6]
def baseStart_1968787 : Nat := 118140960795 + 1968787 * 2 ^ 59
def prefixEnd_1968787 : Nat := 4983230072969 + 3 ^ 40 * 1968787 * 2
def baseEnd_1968787 : Nat := 1010934037323493845508219

theorem tailTrace_1968787 : CollatzResearch.WordTrace tailWord_1968787 prefixEnd_1968787 1010934037323493845508219 := by
  unfold tailWord_1968787
  simp only [CollatzResearch.WordTrace]
  refine ⟨71807561118428415895112615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47871707412285610596741743 71807561118428415895112615)
  ·
    refine ⟨107711341677642623842668923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71807561118428415895112615 107711341677642623842668923)
    ·
      refine ⟨161567012516463935764003385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107711341677642623842668923 161567012516463935764003385)
      ·
        refine ⟨121175259387347951823002539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161567012516463935764003385 121175259387347951823002539)
        ·
          refine ⟨181762889081021927734503809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121175259387347951823002539 181762889081021927734503809)
          ·
            refine ⟨136322166810766445800877857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181762889081021927734503809 136322166810766445800877857)
            ·
              refine ⟨102241625108074834350658393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136322166810766445800877857 102241625108074834350658393)
              ·
                refine ⟨76681218831056125762993795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102241625108074834350658393 76681218831056125762993795)
                ·
                  refine ⟨115021828246584188644490693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76681218831056125762993795 115021828246584188644490693)
                  ·
                    refine ⟨21566592796234535370842005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115021828246584188644490693 21566592796234535370842005)
                    ·
                      refine ⟨1010934037323493845508219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21566592796234535370842005 1010934037323493845508219)
                      ·
                        rfl

theorem cell23_1968787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_1968787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968787 prefixEnd_1968787 := by exact prefixLift 1968787
  have htrace : WordTrace (prefixWord ++ tailWord_1968787) baseStart_1968787 baseEnd_1968787 := by
    simpa [prefixWord, tailWord_1968787, baseEnd_1968787] using wordTrace_append hprefix tailTrace_1968787
  have hstable : (prefixWord ++ tailWord_1968787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968787).length < 2 ^ (prefixWord ++ tailWord_1968787).sum := by decide
  have hdescent : baseEnd_1968787 < baseStart_1968787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968828 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1968828 : Nat := 118140960795 + 1968828 * 2 ^ 59
def prefixEnd_1968828 : Nat := 4983230072969 + 3 ^ 40 * 1968828 * 2
def baseEnd_1968828 : Nat := 1010955090030328185095531

theorem tailTrace_1968828 : CollatzResearch.WordTrace tailWord_1968828 prefixEnd_1968828 1010955090030328185095531 := by
  unfold tailWord_1968828
  simp only [CollatzResearch.WordTrace]
  refine ⟨35904528255639939948677569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47872704340853253264903425 35904528255639939948677569)
  ·
    refine ⟨26928396191729954961508177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35904528255639939948677569 26928396191729954961508177)
    ·
      refine ⟨20196297143797466221131133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26928396191729954961508177 20196297143797466221131133)
      ·
        refine ⟨7573611428924049832924175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20196297143797466221131133 7573611428924049832924175)
        ·
          refine ⟨11360417143386074749386263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7573611428924049832924175 11360417143386074749386263)
          ·
            refine ⟨17040625715079112124079395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11360417143386074749386263 17040625715079112124079395)
            ·
              refine ⟨25560938572618668186119093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17040625715079112124079395 25560938572618668186119093)
              ·
                refine ⟨2396337991183000142448665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25560938572618668186119093 2396337991183000142448665)
                ·
                  refine ⟨1797253493387250106836499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2396337991183000142448665 1797253493387250106836499)
                  ·
                    refine ⟨2695880240080875160254749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1797253493387250106836499 2695880240080875160254749)
                    ·
                      refine ⟨1010955090030328185095531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2695880240080875160254749 1010955090030328185095531)
                      ·
                        rfl

theorem cell23_1968828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1968828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968828 prefixEnd_1968828 := by exact prefixLift 1968828
  have htrace : WordTrace (prefixWord ++ tailWord_1968828) baseStart_1968828 baseEnd_1968828 := by
    simpa [prefixWord, tailWord_1968828, baseEnd_1968828] using wordTrace_append hprefix tailTrace_1968828
  have hstable : (prefixWord ++ tailWord_1968828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968828).length < 2 ^ (prefixWord ++ tailWord_1968828).sum := by decide
  have hdescent : baseEnd_1968828 < baseStart_1968828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968855 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 1, 3, 2]
def baseStart_1968855 : Nat := 118140960795 + 1968855 * 2 ^ 59
def prefixEnd_1968855 : Nat := 4983230072969 + 3 ^ 40 * 1968855 * 2
def baseEnd_1968855 : Nat := 1010968954007999579457907

theorem tailTrace_1968855 : CollatzResearch.WordTrace tailWord_1968855 prefixEnd_1968855 1010968954007999579457907 := by
  unfold tailWord_1968855
  simp only [CollatzResearch.WordTrace]
  refine ⟨71810041282182063508588019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47873360854788042339058679 71810041282182063508588019)
  ·
    refine ⟨107715061923273095262882029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71810041282182063508588019 107715061923273095262882029)
    ·
      refine ⟨40393148221227410723580761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107715061923273095262882029 40393148221227410723580761)
      ·
        refine ⟨30294861165920558042685571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40393148221227410723580761 30294861165920558042685571)
        ·
          refine ⟨45442291748880837064028357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30294861165920558042685571 45442291748880837064028357)
          ·
            refine ⟨8520429702915156949505317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45442291748880837064028357 8520429702915156949505317)
            ·
              refine ⟨1597580569296591928032247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8520429702915156949505317 1597580569296591928032247)
              ·
                refine ⟨2396370853944887892048371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597580569296591928032247 2396370853944887892048371)
                ·
                  refine ⟨3594556280917331838072557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396370853944887892048371 3594556280917331838072557)
                  ·
                    refine ⟨1347958605343999439277209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3594556280917331838072557 1347958605343999439277209)
                    ·
                      refine ⟨1010968954007999579457907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347958605343999439277209 1010968954007999579457907)
                      ·
                        rfl

theorem cell23_1968855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_1968855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968855 prefixEnd_1968855 := by exact prefixLift 1968855
  have htrace : WordTrace (prefixWord ++ tailWord_1968855) baseStart_1968855 baseEnd_1968855 := by
    simpa [prefixWord, tailWord_1968855, baseEnd_1968855] using wordTrace_append hprefix tailTrace_1968855
  have hstable : (prefixWord ++ tailWord_1968855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968855).length < 2 ^ (prefixWord ++ tailWord_1968855).sum := by decide
  have hdescent : baseEnd_1968855 < baseStart_1968855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968925 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 7]
def baseStart_1968925 : Nat := 118140960795 + 1968925 * 2 ^ 59
def prefixEnd_1968925 : Nat := 4983230072969 + 3 ^ 40 * 1968925 * 2
def baseEnd_1968925 : Nat := 112333877517090478398065

theorem tailTrace_1968925 : CollatzResearch.WordTrace tailWord_1968925 prefixEnd_1968925 112333877517090478398065 := by
  unfold tailWord_1968925
  simp only [CollatzResearch.WordTrace]
  refine ⟨71812594391928465463636229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47875062927952310309090819 71812594391928465463636229)
  ·
    refine ⟨13464861448486587274431793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71812594391928465463636229 13464861448486587274431793)
    ·
      refine ⟨10098646086364940455823845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13464861448486587274431793 10098646086364940455823845)
      ·
        refine ⟨1893496141193426335466971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10098646086364940455823845 1893496141193426335466971)
        ·
          refine ⟨2840244211790139503200457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893496141193426335466971 2840244211790139503200457)
          ·
            refine ⟨2130183158842604627400343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840244211790139503200457 2130183158842604627400343)
            ·
              refine ⟨3195274738263906941100515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130183158842604627400343 3195274738263906941100515)
              ·
                refine ⟨4792912107395860411650773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3195274738263906941100515 4792912107395860411650773)
                ·
                  refine ⟨112333877517090478398065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4792912107395860411650773 112333877517090478398065)
                  ·
                    rfl

theorem cell23_1968925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_1968925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968925 prefixEnd_1968925 := by exact prefixLift 1968925
  have htrace : WordTrace (prefixWord ++ tailWord_1968925) baseStart_1968925 baseEnd_1968925 := by
    simpa [prefixWord, tailWord_1968925, baseEnd_1968925] using wordTrace_append hprefix tailTrace_1968925
  have hstable : (prefixWord ++ tailWord_1968925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968925).length < 2 ^ (prefixWord ++ tailWord_1968925).sum := by decide
  have hdescent : baseEnd_1968925 < baseStart_1968925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968944 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_1968944 : Nat := 118140960795 + 1968944 * 2 ^ 59
def prefixEnd_1968944 : Nat := 4983230072969 + 3 ^ 40 * 1968944 * 2
def baseEnd_1968944 : Nat := 1011014653786249731244997

theorem tailTrace_1968944 : CollatzResearch.WordTrace tailWord_1968944 prefixEnd_1968944 1011014653786249731244997 := by
  unfold tailWord_1968944
  simp only [CollatzResearch.WordTrace]
  refine ⟨35906643689429815854288943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47875524919239754472385257 35906643689429815854288943)
  ·
    refine ⟨53859965534144723781433415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35906643689429815854288943 53859965534144723781433415)
    ·
      refine ⟨80789948301217085672150123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53859965534144723781433415 80789948301217085672150123)
      ·
        refine ⟨121184922451825628508225185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80789948301217085672150123 121184922451825628508225185)
        ·
          refine ⟨90888691838869221381168889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121184922451825628508225185 90888691838869221381168889)
          ·
            refine ⟨68166518879151916035876667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90888691838869221381168889 68166518879151916035876667)
            ·
              refine ⟨102249778318727874053815001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68166518879151916035876667 102249778318727874053815001)
              ·
                refine ⟨76687333739045905540361251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102249778318727874053815001 76687333739045905540361251)
                ·
                  refine ⟨115031000608568858310541877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76687333739045905540361251 115031000608568858310541877)
                  ·
                    refine ⟨10784156307053330466613301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115031000608568858310541877 10784156307053330466613301)
                    ·
                      refine ⟨1011014653786249731244997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10784156307053330466613301 1011014653786249731244997)
                      ·
                        rfl

theorem cell23_1968944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_1968944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968944 prefixEnd_1968944 := by exact prefixLift 1968944
  have htrace : WordTrace (prefixWord ++ tailWord_1968944) baseStart_1968944 baseEnd_1968944 := by
    simpa [prefixWord, tailWord_1968944, baseEnd_1968944] using wordTrace_append hprefix tailTrace_1968944
  have hstable : (prefixWord ++ tailWord_1968944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968944).length < 2 ^ (prefixWord ++ tailWord_1968944).sum := by decide
  have hdescent : baseEnd_1968944 < baseStart_1968944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968951 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 5, 4]
def baseStart_1968951 : Nat := 118140960795 + 1968951 * 2 ^ 59
def prefixEnd_1968951 : Nat := 4983230072969 + 3 ^ 40 * 1968951 * 2
def baseEnd_1968951 : Nat := 337006082716943734619155

theorem tailTrace_1968951 : CollatzResearch.WordTrace tailWord_1968951 prefixEnd_1968951 337006082716943734619155 := by
  unfold tailWord_1968951
  simp only [CollatzResearch.WordTrace]
  refine ⟨71813542689834271904082707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47875695126556181269388471 71813542689834271904082707)
  ·
    refine ⟨107720314034751407856124061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71813542689834271904082707 107720314034751407856124061)
    ·
      refine ⟨40395117763031777946046523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107720314034751407856124061 40395117763031777946046523)
      ·
        refine ⟨60592676644547666919069785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40395117763031777946046523 60592676644547666919069785)
        ·
          refine ⟨45444507483410750189302339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60592676644547666919069785 45444507483410750189302339)
          ·
            refine ⟨68166761225116125283953509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45444507483410750189302339 68166761225116125283953509)
            ·
              refine ⟨12781267729709273490741283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68166761225116125283953509 12781267729709273490741283)
              ·
                refine ⟨19171901594563910236111925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12781267729709273490741283 19171901594563910236111925)
                ·
                  refine ⟨1797365774490366584635493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19171901594563910236111925 1797365774490366584635493)
                  ·
                    refine ⟨337006082716943734619155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797365774490366584635493 337006082716943734619155)
                    ·
                      rfl

theorem cell23_1968951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_1968951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968951 prefixEnd_1968951 := by exact prefixLift 1968951
  have htrace : WordTrace (prefixWord ++ tailWord_1968951) baseStart_1968951 baseEnd_1968951 := by
    simpa [prefixWord, tailWord_1968951, baseEnd_1968951] using wordTrace_append hprefix tailTrace_1968951
  have hstable : (prefixWord ++ tailWord_1968951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968951).length < 2 ^ (prefixWord ++ tailWord_1968951).sum := by decide
  have hdescent : baseEnd_1968951 < baseStart_1968951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968978 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_1968978 : Nat := 118140960795 + 1968978 * 2 ^ 59
def prefixEnd_1968978 : Nat := 4983230072969 + 3 ^ 40 * 1968978 * 2
def baseEnd_1968978 : Nat := 1011032112128502598219841

theorem tailTrace_1968978 : CollatzResearch.WordTrace tailWord_1968978 prefixEnd_1968978 1011032112128502598219841 := by
  unfold tailWord_1968978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17953631865184113878828897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47876351640490970343543725 17953631865184113878828897)
  ·
    refine ⟨13465223898888085409121673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17953631865184113878828897 13465223898888085409121673)
    ·
      refine ⟨10098917924166064056841255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13465223898888085409121673 10098917924166064056841255)
      ·
        refine ⟨15148376886249096085261883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10098917924166064056841255 15148376886249096085261883)
        ·
          refine ⟨22722565329373644127892825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15148376886249096085261883 22722565329373644127892825)
          ·
            refine ⟨17041923997030233095919619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22722565329373644127892825 17041923997030233095919619)
            ·
              refine ⟨25562885995545349643879429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17041923997030233095919619 25562885995545349643879429)
              ·
                refine ⟨4793041124164753058227393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25562885995545349643879429 4793041124164753058227393)
                ·
                  refine ⟨3594780843123564793670545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4793041124164753058227393 3594780843123564793670545)
                  ·
                    refine ⟨2696085632342673595252909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3594780843123564793670545 2696085632342673595252909)
                    ·
                      refine ⟨1011032112128502598219841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2696085632342673595252909 1011032112128502598219841)
                      ·
                        rfl

theorem cell23_1968978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_1968978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968978 prefixEnd_1968978 := by exact prefixLift 1968978
  have htrace : WordTrace (prefixWord ++ tailWord_1968978) baseStart_1968978 baseEnd_1968978 := by
    simpa [prefixWord, tailWord_1968978, baseEnd_1968978] using wordTrace_append hprefix tailTrace_1968978
  have hstable : (prefixWord ++ tailWord_1968978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968978).length < 2 ^ (prefixWord ++ tailWord_1968978).sum := by decide
  have hdescent : baseEnd_1968978 < baseStart_1968978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968985 : List Nat := [1, 2, 1, 2, 2, 5, 1, 4, 1, 4]
def baseStart_1968985 : Nat := 118140960795 + 1968985 * 2 ^ 59
def prefixEnd_1968985 : Nat := 4983230072969 + 3 ^ 40 * 1968985 * 2
def baseEnd_1968985 : Nat := 337011902164361356944103

theorem tailTrace_1968985 : CollatzResearch.WordTrace tailWord_1968985 prefixEnd_1968985 337011902164361356944103 := by
  unfold tailWord_1968985
  simp only [CollatzResearch.WordTrace]
  refine ⟨71814782771711095710820409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47876521847807397140546939 71814782771711095710820409)
  ·
    refine ⟨53861087078783321783115307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71814782771711095710820409 53861087078783321783115307)
    ·
      refine ⟨80791630618174982674672961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53861087078783321783115307 80791630618174982674672961)
      ·
        refine ⟨60593722963631237006004721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80791630618174982674672961 60593722963631237006004721)
        ·
          refine ⟨45445292222723427754503541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60593722963631237006004721 45445292222723427754503541)
          ·
            refine ⟨4260496145880321351984707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45445292222723427754503541 4260496145880321351984707)
            ·
              refine ⟨6390744218820482027977061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4260496145880321351984707 6390744218820482027977061)
              ·
                refine ⟨1198264541028840380245699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6390744218820482027977061 1198264541028840380245699)
                ·
                  refine ⟨1797396811543260570368549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198264541028840380245699 1797396811543260570368549)
                  ·
                    refine ⟨337011902164361356944103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797396811543260570368549 337011902164361356944103)
                    ·
                      rfl

theorem cell23_1968985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 4].length) (baseStart_1968985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968985 prefixEnd_1968985 := by exact prefixLift 1968985
  have htrace : WordTrace (prefixWord ++ tailWord_1968985) baseStart_1968985 baseEnd_1968985 := by
    simpa [prefixWord, tailWord_1968985, baseEnd_1968985] using wordTrace_append hprefix tailTrace_1968985
  have hstable : (prefixWord ++ tailWord_1968985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968985).length < 2 ^ (prefixWord ++ tailWord_1968985).sum := by decide
  have hdescent : baseEnd_1968985 < baseStart_1968985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969008 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 5, 1, 3]
def baseStart_1969008 : Nat := 118140960795 + 1969008 * 2 ^ 59
def prefixEnd_1969008 : Nat := 4983230072969 + 3 ^ 40 * 1969008 * 2
def baseEnd_1969008 : Nat := 1011047516548137480844703

theorem tailTrace_1969008 : CollatzResearch.WordTrace tailWord_1969008 prefixEnd_1969008 1011047516548137480844703 := by
  unfold tailWord_1969008
  simp only [CollatzResearch.WordTrace]
  refine ⟨35907810825313885319453839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47877081100418513759271785 35907810825313885319453839)
  ·
    refine ⟨53861716237970827979180759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35907810825313885319453839 53861716237970827979180759)
    ·
      refine ⟨80792574356956241968771139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53861716237970827979180759 80792574356956241968771139)
      ·
        refine ⟨121188861535434362953156709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80792574356956241968771139 121188861535434362953156709)
        ·
          refine ⟨22722911537893943053716883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121188861535434362953156709 22722911537893943053716883)
          ·
            refine ⟨34084367306840914580575325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22722911537893943053716883 34084367306840914580575325)
            ·
              refine ⟨12781637740065342967715747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34084367306840914580575325 12781637740065342967715747)
              ·
                refine ⟨19172456610098014451573621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12781637740065342967715747 19172456610098014451573621)
                ·
                  refine ⟨1797417807196688854835027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19172456610098014451573621 1797417807196688854835027)
                  ·
                    refine ⟨2696126710795033282252541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1797417807196688854835027 2696126710795033282252541)
                    ·
                      refine ⟨1011047516548137480844703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2696126710795033282252541 1011047516548137480844703)
                      ·
                        rfl

theorem cell23_1969008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 1, 3].length) (baseStart_1969008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969008 prefixEnd_1969008 := by exact prefixLift 1969008
  have htrace : WordTrace (prefixWord ++ tailWord_1969008) baseStart_1969008 baseEnd_1969008 := by
    simpa [prefixWord, tailWord_1969008, baseEnd_1969008] using wordTrace_append hprefix tailTrace_1969008
  have hstable : (prefixWord ++ tailWord_1969008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969008).length < 2 ^ (prefixWord ++ tailWord_1969008).sum := by decide
  have hdescent : baseEnd_1969008 < baseStart_1969008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969011 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 3, 5]
def baseStart_1969011 : Nat := 118140960795 + 1969011 * 2 ^ 59
def prefixEnd_1969011 : Nat := 4983230072969 + 3 ^ 40 * 1969011 * 2
def baseEnd_1969011 : Nat := 337016352330033656369063

theorem tailTrace_1969011 : CollatzResearch.WordTrace tailWord_1969011 prefixEnd_1969011 337016352330033656369063 := by
  unfold tailWord_1969011
  simp only [CollatzResearch.WordTrace]
  refine ⟨71815731069616902151266887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47877154046411268100844591 71815731069616902151266887)
  ·
    refine ⟨107723596604425353226900331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71815731069616902151266887 107723596604425353226900331)
    ·
      refine ⟨161585394906638029840350497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107723596604425353226900331 161585394906638029840350497)
      ·
        refine ⟨121189046179978522380262873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161585394906638029840350497 121189046179978522380262873)
        ·
          refine ⟨90891784634983891785197155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121189046179978522380262873 90891784634983891785197155)
          ·
            refine ⟨136337676952475837677795733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90891784634983891785197155 136337676952475837677795733)
            ·
              refine ⟨6390828607147304891146675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136337676952475837677795733 6390828607147304891146675)
              ·
                refine ⟨9586242910720957336720013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6390828607147304891146675 9586242910720957336720013)
                ·
                  refine ⟨3594841091520359001270005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9586242910720957336720013 3594841091520359001270005)
                  ·
                    refine ⟨337016352330033656369063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3594841091520359001270005 337016352330033656369063)
                    ·
                      rfl

theorem cell23_1969011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 5].length) (baseStart_1969011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969011 prefixEnd_1969011 := by exact prefixLift 1969011
  have htrace : WordTrace (prefixWord ++ tailWord_1969011) baseStart_1969011 baseEnd_1969011 := by
    simpa [prefixWord, tailWord_1969011, baseEnd_1969011] using wordTrace_append hprefix tailTrace_1969011
  have hstable : (prefixWord ++ tailWord_1969011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969011).length < 2 ^ (prefixWord ++ tailWord_1969011).sum := by decide
  have hdescent : baseEnd_1969011 < baseStart_1969011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969065 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 3, 2, 2]
def baseStart_1969065 : Nat := 118140960795 + 1969065 * 2 ^ 59
def prefixEnd_1969065 : Nat := 4983230072969 + 3 ^ 40 * 1969065 * 2
def baseEnd_1969065 : Nat := 1011076784945443757831941

theorem tailTrace_1969065 : CollatzResearch.WordTrace tailWord_1969065 prefixEnd_1969065 1011076784945443757831941 := by
  unfold tailWord_1969065
  simp only [CollatzResearch.WordTrace]
  refine ⟨71817700611421269373732649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47878467074280846249155099 71817700611421269373732649)
  ·
    refine ⟨53863275458565952030299487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71817700611421269373732649 53863275458565952030299487)
    ·
      refine ⟨80794913187848928045449231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53863275458565952030299487 80794913187848928045449231)
      ·
        refine ⟨121192369781773392068173847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80794913187848928045449231 121192369781773392068173847)
        ·
          refine ⟨181788554672660088102260771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121192369781773392068173847 181788554672660088102260771)
          ·
            refine ⟨272682832008990132153391157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181788554672660088102260771 272682832008990132153391157)
            ·
              refine ⟨25564015500842824889380421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272682832008990132153391157 25564015500842824889380421)
              ·
                refine ⟨4793252906408029666758829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25564015500842824889380421 4793252906408029666758829)
                ·
                  refine ⟨1797469839903011125034561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4793252906408029666758829 1797469839903011125034561)
                  ·
                    refine ⟨1348102379927258343775921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1797469839903011125034561 1348102379927258343775921)
                    ·
                      refine ⟨1011076784945443757831941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348102379927258343775921 1011076784945443757831941)
                      ·
                        rfl

theorem cell23_1969065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 2, 2].length) (baseStart_1969065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969065 prefixEnd_1969065 := by exact prefixLift 1969065
  have htrace : WordTrace (prefixWord ++ tailWord_1969065) baseStart_1969065 baseEnd_1969065 := by
    simpa [prefixWord, tailWord_1969065, baseEnd_1969065] using wordTrace_append hprefix tailTrace_1969065
  have hstable : (prefixWord ++ tailWord_1969065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969065).length < 2 ^ (prefixWord ++ tailWord_1969065).sum := by decide
  have hdescent : baseEnd_1969065 < baseStart_1969065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969076 : List Nat := [2, 5, 2, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_1969076 : Nat := 118140960795 + 1969076 * 2 ^ 59
def prefixEnd_1969076 : Nat := 4983230072969 + 3 ^ 40 * 1969076 * 2
def baseEnd_1969076 : Nat := 1011082433232643214794391

theorem tailTrace_1969076 : CollatzResearch.WordTrace tailWord_1969076 prefixEnd_1969076 1011082433232643214794391 := by
  unfold tailWord_1969076
  simp only [CollatzResearch.WordTrace]
  refine ⟨35909050907190709126191541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47878734542920945501588721 35909050907190709126191541)
  ·
    refine ⟨3366473522549128980580457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35909050907190709126191541 3366473522549128980580457)
    ·
      refine ⟨2524855141911846735435343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3366473522549128980580457 2524855141911846735435343)
      ·
        refine ⟨3787282712867770103153015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2524855141911846735435343 3787282712867770103153015)
        ·
          refine ⟨5680924069301655154729523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787282712867770103153015 5680924069301655154729523)
          ·
            refine ⟨8521386103952482732094285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5680924069301655154729523 8521386103952482732094285)
            ·
              refine ⟨3195519788982181024535357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8521386103952482732094285 3195519788982181024535357)
              ·
                refine ⟨1198319920868317884200759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3195519788982181024535357 1198319920868317884200759)
                ·
                  refine ⟨1797479881302476826301139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198319920868317884200759 1797479881302476826301139)
                  ·
                    refine ⟨2696219821953715239451709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1797479881302476826301139 2696219821953715239451709)
                    ·
                      refine ⟨1011082433232643214794391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2696219821953715239451709 1011082433232643214794391)
                      ·
                        rfl

theorem cell23_1969076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_1969076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969076 prefixEnd_1969076 := by exact prefixLift 1969076
  have htrace : WordTrace (prefixWord ++ tailWord_1969076) baseStart_1969076 baseEnd_1969076 := by
    simpa [prefixWord, tailWord_1969076, baseEnd_1969076] using wordTrace_append hprefix tailTrace_1969076
  have hstable : (prefixWord ++ tailWord_1969076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969076).length < 2 ^ (prefixWord ++ tailWord_1969076).sum := by decide
  have hdescent : baseEnd_1969076 < baseStart_1969076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969085 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_1969085 : Nat := 118140960795 + 1969085 * 2 ^ 59
def prefixEnd_1969085 : Nat := 4983230072969 + 3 ^ 40 * 1969085 * 2
def baseEnd_1969085 : Nat := 1011087054558533679581849

theorem tailTrace_1969085 : CollatzResearch.WordTrace tailWord_1969085 prefixEnd_1969085 1011087054558533679581849 := by
  unfold tailWord_1969085
  simp only [CollatzResearch.WordTrace]
  refine ⟨71818430071348812789460709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47878953380899208526307139 71818430071348812789460709)
  ·
    refine ⟨13465955638377902398023883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71818430071348812789460709 13465955638377902398023883)
    ·
      refine ⟨20198933457566853597035825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13465955638377902398023883 20198933457566853597035825)
      ·
        refine ⟨15149200093175140197776869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20198933457566853597035825 15149200093175140197776869)
        ·
          refine ⟨2840475017470338787083163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15149200093175140197776869 2840475017470338787083163)
          ·
            refine ⟨4260712526205508180624745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840475017470338787083163 4260712526205508180624745)
            ·
              refine ⟨3195534394654131135468559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4260712526205508180624745 3195534394654131135468559)
              ·
                refine ⟨4793301591981196703202839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3195534394654131135468559 4793301591981196703202839)
                ·
                  refine ⟨7189952387971795054804259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793301591981196703202839 7189952387971795054804259)
                  ·
                    refine ⟨10784928581957692582206389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7189952387971795054804259 10784928581957692582206389)
                    ·
                      refine ⟨1011087054558533679581849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10784928581957692582206389 1011087054558533679581849)
                      ·
                        rfl

theorem cell23_1969085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_1969085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969085 prefixEnd_1969085 := by exact prefixLift 1969085
  have htrace : WordTrace (prefixWord ++ tailWord_1969085) baseStart_1969085 baseEnd_1969085 := by
    simpa [prefixWord, tailWord_1969085, baseEnd_1969085] using wordTrace_append hprefix tailTrace_1969085
  have hstable : (prefixWord ++ tailWord_1969085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969085).length < 2 ^ (prefixWord ++ tailWord_1969085).sum := by decide
  have hdescent : baseEnd_1969085 < baseStart_1969085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969109 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_1969109 : Nat := 118140960795 + 1969109 * 2 ^ 59
def prefixEnd_1969109 : Nat := 4983230072969 + 3 ^ 40 * 1969109 * 2
def baseEnd_1969109 : Nat := 337033126031413861893913

theorem tailTrace_1969109 : CollatzResearch.WordTrace tailWord_1969109 prefixEnd_1969109 337033126031413861893913 := by
  unfold tailWord_1969109
  simp only [CollatzResearch.WordTrace]
  refine ⟨71819305423261864888334381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47879536948841243258889587 71819305423261864888334381)
  ·
    refine ⟨26932239533723199333125393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71819305423261864888334381 26932239533723199333125393)
    ·
      refine ⟨20199179650292399499844045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26932239533723199333125393 20199179650292399499844045)
      ·
        refine ⟨7574692368859649812441517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20199179650292399499844045 7574692368859649812441517)
        ·
          refine ⟨2840509638322368679665569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7574692368859649812441517 2840509638322368679665569)
          ·
            refine ⟨2130382228741776509749177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840509638322368679665569 2130382228741776509749177)
            ·
              refine ⟨1597786671556332382311883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130382228741776509749177 1597786671556332382311883)
              ·
                refine ⟨2396680007334498573467825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597786671556332382311883 2396680007334498573467825)
                ·
                  refine ⟨1797510005500873930100869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2396680007334498573467825 1797510005500873930100869)
                  ·
                    refine ⟨337033126031413861893913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797510005500873930100869 337033126031413861893913)
                    ·
                      rfl

theorem cell23_1969109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_1969109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969109 prefixEnd_1969109 := by exact prefixLift 1969109
  have htrace : WordTrace (prefixWord ++ tailWord_1969109) baseStart_1969109 baseEnd_1969109 := by
    simpa [prefixWord, tailWord_1969109, baseEnd_1969109] using wordTrace_append hprefix tailTrace_1969109
  have hstable : (prefixWord ++ tailWord_1969109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969109).length < 2 ^ (prefixWord ++ tailWord_1969109).sum := by decide
  have hdescent : baseEnd_1969109 < baseStart_1969109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969111 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_1969111 : Nat := 118140960795 + 1969111 * 2 ^ 59
def prefixEnd_1969111 : Nat := 4983230072969 + 3 ^ 40 * 1969111 * 2
def baseEnd_1969111 : Nat := 1011100405055550577856729

theorem tailTrace_1969111 : CollatzResearch.WordTrace tailWord_1969111 prefixEnd_1969111 1011100405055550577856729 := by
  unfold tailWord_1969111
  simp only [CollatzResearch.WordTrace]
  refine ⟨71819378369254619229907187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47879585579503079486604791 71819378369254619229907187)
  ·
    refine ⟨107729067553881928844860781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71819378369254619229907187 107729067553881928844860781)
    ·
      refine ⟨40398400332705723316822793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107729067553881928844860781 40398400332705723316822793)
      ·
        refine ⟨30298800249529292487617095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40398400332705723316822793 30298800249529292487617095)
        ·
          refine ⟨45448200374293938731425643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30298800249529292487617095 45448200374293938731425643)
          ·
            refine ⟨68172300561440908097138465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45448200374293938731425643 68172300561440908097138465)
            ·
              refine ⟨51129225421080681072853849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68172300561440908097138465 51129225421080681072853849)
              ·
                refine ⟨38346919065810510804640387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51129225421080681072853849 38346919065810510804640387)
                ·
                  refine ⟨57520378598715766206960581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38346919065810510804640387 57520378598715766206960581)
                  ·
                    refine ⟨10785070987259206163805109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57520378598715766206960581 10785070987259206163805109)
                    ·
                      refine ⟨1011100405055550577856729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10785070987259206163805109 1011100405055550577856729)
                      ·
                        rfl

theorem cell23_1969111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_1969111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969111 prefixEnd_1969111 := by exact prefixLift 1969111
  have htrace : WordTrace (prefixWord ++ tailWord_1969111) baseStart_1969111 baseEnd_1969111 := by
    simpa [prefixWord, tailWord_1969111, baseEnd_1969111] using wordTrace_append hprefix tailTrace_1969111
  have hstable : (prefixWord ++ tailWord_1969111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969111).length < 2 ^ (prefixWord ++ tailWord_1969111).sum := by decide
  have hdescent : baseEnd_1969111 < baseStart_1969111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969119 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 1, 2, 3]
def baseStart_1969119 : Nat := 118140960795 + 1969119 * 2 ^ 59
def prefixEnd_1969119 : Nat := 4983230072969 + 3 ^ 40 * 1969119 * 2
def baseEnd_1969119 : Nat := 1011104512900786546556693

theorem tailTrace_1969119 : CollatzResearch.WordTrace tailWord_1969119 prefixEnd_1969119 1011104512900786546556693 := by
  unfold tailWord_1969119
  simp only [CollatzResearch.WordTrace]
  refine ⟨71819670153225636596198411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47879780102150424397465607 71819670153225636596198411)
  ·
    refine ⟨107729505229838454894297617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71819670153225636596198411 107729505229838454894297617)
    ·
      refine ⟨80797128922378841170723213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107729505229838454894297617 80797128922378841170723213)
      ·
        refine ⟨30298923345892065439021205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80797128922378841170723213 30298923345892065439021205)
        ·
          refine ⟨1420262031838690567454119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30298923345892065439021205 1420262031838690567454119)
          ·
            refine ⟨2130393047758035851181179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420262031838690567454119 2130393047758035851181179)
            ·
              refine ⟨3195589571637053776771769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130393047758035851181179 3195589571637053776771769)
              ·
                refine ⟨2396692178727790332578827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195589571637053776771769 2396692178727790332578827)
                ·
                  refine ⟨3595038268091685498868241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396692178727790332578827 3595038268091685498868241)
                  ·
                    refine ⟨2696278701068764124151181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3595038268091685498868241 2696278701068764124151181)
                    ·
                      refine ⟨1011104512900786546556693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2696278701068764124151181 1011104512900786546556693)
                      ·
                        rfl

theorem cell23_1969119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_1969119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969119 prefixEnd_1969119 := by exact prefixLift 1969119
  have htrace : WordTrace (prefixWord ++ tailWord_1969119) baseStart_1969119 baseEnd_1969119 := by
    simpa [prefixWord, tailWord_1969119, baseEnd_1969119] using wordTrace_append hprefix tailTrace_1969119
  have hstable : (prefixWord ++ tailWord_1969119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969119).length < 2 ^ (prefixWord ++ tailWord_1969119).sum := by decide
  have hdescent : baseEnd_1969119 < baseStart_1969119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969121 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1969121 : Nat := 118140960795 + 1969121 * 2 ^ 59
def prefixEnd_1969121 : Nat := 4983230072969 + 3 ^ 40 * 1969121 * 2
def baseEnd_1969121 : Nat := 1011105539862095538731683

theorem tailTrace_1969121 : CollatzResearch.WordTrace tailWord_1969121 prefixEnd_1969121 1011105539862095538731683 := by
  unfold tailWord_1969121
  simp only [CollatzResearch.WordTrace]
  refine ⟨71819743099218390937771217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47879828732812260625180811 71819743099218390937771217)
  ·
    refine ⟨53864807324413793203328413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71819743099218390937771217 53864807324413793203328413)
    ·
      refine ⟨20199302746655172451248155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53864807324413793203328413 20199302746655172451248155)
      ·
        refine ⟨30298954119982758676872233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20199302746655172451248155 30298954119982758676872233)
        ·
          refine ⟨22724215589987069007654175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30298954119982758676872233 22724215589987069007654175)
          ·
            refine ⟨34086323384980603511481263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22724215589987069007654175 34086323384980603511481263)
            ·
              refine ⟨51129485077470905267221895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34086323384980603511481263 51129485077470905267221895)
              ·
                refine ⟨76694227616206357900832843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51129485077470905267221895 76694227616206357900832843)
                ·
                  refine ⟨115041341424309536851249265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76694227616206357900832843 115041341424309536851249265)
                  ·
                    refine ⟨86281006068232152638436949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115041341424309536851249265 86281006068232152638436949)
                    ·
                      refine ⟨1011105539862095538731683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 86281006068232152638436949 1011105539862095538731683)
                      ·
                        rfl

theorem cell23_1969121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1969121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969121 prefixEnd_1969121 := by exact prefixLift 1969121
  have htrace : WordTrace (prefixWord ++ tailWord_1969121) baseStart_1969121 baseEnd_1969121 := by
    simpa [prefixWord, tailWord_1969121, baseEnd_1969121] using wordTrace_append hprefix tailTrace_1969121
  have hstable : (prefixWord ++ tailWord_1969121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969121).length < 2 ^ (prefixWord ++ tailWord_1969121).sum := by decide
  have hdescent : baseEnd_1969121 < baseStart_1969121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969131 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 6, 6]
def baseStart_1969131 : Nat := 118140960795 + 1969131 * 2 ^ 59
def prefixEnd_1969131 : Nat := 4983230072969 + 3 ^ 40 * 1969131 * 2
def baseEnd_1969131 : Nat := 337036891556213499868879

theorem tailTrace_1969131 : CollatzResearch.WordTrace tailWord_1969131 prefixEnd_1969131 337036891556213499868879 := by
  unfold tailWord_1969131
  simp only [CollatzResearch.WordTrace]
  refine ⟨71820107829182162645635247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47880071886121441763756831 71820107829182162645635247)
  ·
    refine ⟨107730161743773243968452871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71820107829182162645635247 107730161743773243968452871)
    ·
      refine ⟨161595242615659865952679307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107730161743773243968452871 161595242615659865952679307)
      ·
        refine ⟨242392863923489798929018961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161595242615659865952679307 242392863923489798929018961)
        ·
          refine ⟨181794647942617349196764221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242392863923489798929018961 181794647942617349196764221)
          ·
            refine ⟨68172992978481505948786583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181794647942617349196764221 68172992978481505948786583)
            ·
              refine ⟨102259489467722258923179875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68172992978481505948786583 102259489467722258923179875)
              ·
                refine ⟨153389234201583388384769813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102259489467722258923179875 153389234201583388384769813)
                ·
                  refine ⟨7190120353199221330536085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153389234201583388384769813 7190120353199221330536085)
                  ·
                    refine ⟨337036891556213499868879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7190120353199221330536085 337036891556213499868879)
                    ·
                      rfl

theorem cell23_1969131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 6].length) (baseStart_1969131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969131 prefixEnd_1969131 := by exact prefixLift 1969131
  have htrace : WordTrace (prefixWord ++ tailWord_1969131) baseStart_1969131 baseEnd_1969131 := by
    simpa [prefixWord, tailWord_1969131, baseEnd_1969131] using wordTrace_append hprefix tailTrace_1969131
  have hstable : (prefixWord ++ tailWord_1969131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969131).length < 2 ^ (prefixWord ++ tailWord_1969131).sum := by decide
  have hdescent : baseEnd_1969131 < baseStart_1969131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969150 : List Nat := [4, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1969150 : Nat := 118140960795 + 1969150 * 2 ^ 59
def prefixEnd_1969150 : Nat := 4983230072969 + 3 ^ 40 * 1969150 * 2
def baseEnd_1969150 : Nat := 1011120430801075925269051

theorem tailTrace_1969150 : CollatzResearch.WordTrace tailWord_1969150 prefixEnd_1969150 1011120430801075925269051 := by
  unfold tailWord_1969150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977600102014166111322113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47880533877408885927051269 8977600102014166111322113)
  ·
    refine ⟨6733200076510624583491585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8977600102014166111322113 6733200076510624583491585)
    ·
      refine ⟨5049900057382968437618689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6733200076510624583491585 5049900057382968437618689)
      ·
        refine ⟨3787425043037226328214017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5049900057382968437618689 3787425043037226328214017)
        ·
          refine ⟨2840568782277919746160513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787425043037226328214017 2840568782277919746160513)
          ·
            refine ⟨2130426586708439809620385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840568782277919746160513 2130426586708439809620385)
            ·
              refine ⟨1597819940031329857215289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130426586708439809620385 1597819940031329857215289)
              ·
                refine ⟨1198364955023497392911467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597819940031329857215289 1198364955023497392911467)
                ·
                  refine ⟨1797547432535246089367201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198364955023497392911467 1797547432535246089367201)
                  ·
                    refine ⟨1348160574401434567025401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1797547432535246089367201 1348160574401434567025401)
                    ·
                      refine ⟨1011120430801075925269051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348160574401434567025401 1011120430801075925269051)
                      ·
                        rfl

theorem cell23_1969150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1969150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969150 prefixEnd_1969150 := by exact prefixLift 1969150
  have htrace : WordTrace (prefixWord ++ tailWord_1969150) baseStart_1969150 baseEnd_1969150 := by
    simpa [prefixWord, tailWord_1969150, baseEnd_1969150] using wordTrace_append hprefix tailTrace_1969150
  have hstable : (prefixWord ++ tailWord_1969150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969150).length < 2 ^ (prefixWord ++ tailWord_1969150).sum := by decide
  have hdescent : baseEnd_1969150 < baseStart_1969150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969151 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_1969151 : Nat := 118140960795 + 1969151 * 2 ^ 59
def prefixEnd_1969151 : Nat := 4983230072969 + 3 ^ 40 * 1969151 * 2
def baseEnd_1969151 : Nat := 1011120944281730421356545

theorem tailTrace_1969151 : CollatzResearch.WordTrace tailWord_1969151 prefixEnd_1969151 1011120944281730421356545 := by
  unfold tailWord_1969151
  simp only [CollatzResearch.WordTrace]
  refine ⟨71820837289109706061363307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47880558192739804040908871 71820837289109706061363307)
  ·
    refine ⟨107731255933664559092044961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71820837289109706061363307 107731255933664559092044961)
    ·
      refine ⟨80798441950248419319033721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107731255933664559092044961 80798441950248419319033721)
      ·
        refine ⟨60598831462686314489275291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80798441950248419319033721 60598831462686314489275291)
        ·
          refine ⟨90898247194029471733912937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60598831462686314489275291 90898247194029471733912937)
          ·
            refine ⟨68173685395522103800434703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90898247194029471733912937 68173685395522103800434703)
            ·
              refine ⟨102260528093283155700652055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68173685395522103800434703 102260528093283155700652055)
              ·
                refine ⟨153390792139924733550978083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102260528093283155700652055 153390792139924733550978083)
                ·
                  refine ⟨230086188209887100326467125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153390792139924733550978083 230086188209887100326467125)
                  ·
                    refine ⟨21570580144676915655606293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 230086188209887100326467125 21570580144676915655606293)
                    ·
                      refine ⟨1011120944281730421356545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21570580144676915655606293 1011120944281730421356545)
                      ·
                        rfl

theorem cell23_1969151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_1969151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969151 prefixEnd_1969151 := by exact prefixLift 1969151
  have htrace : WordTrace (prefixWord ++ tailWord_1969151) baseStart_1969151 baseEnd_1969151 := by
    simpa [prefixWord, tailWord_1969151, baseEnd_1969151] using wordTrace_append hprefix tailTrace_1969151
  have hstable : (prefixWord ++ tailWord_1969151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969151).length < 2 ^ (prefixWord ++ tailWord_1969151).sum := by decide
  have hdescent : baseEnd_1969151 < baseStart_1969151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969161 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 11]
def baseStart_1969161 : Nat := 118140960795 + 1969161 * 2 ^ 59
def prefixEnd_1969161 : Nat := 4983230072969 + 3 ^ 40 * 1969161 * 2
def baseEnd_1969161 : Nat := 112347342120919486914611

theorem tailTrace_1969161 : CollatzResearch.WordTrace tailWord_1969161 prefixEnd_1969161 112347342120919486914611 := by
  unfold tailWord_1969161
  simp only [CollatzResearch.WordTrace]
  refine ⟨71821202019073477769227337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47880801346048985179484891 71821202019073477769227337)
  ·
    refine ⟨53865901514305108326920503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71821202019073477769227337 53865901514305108326920503)
    ·
      refine ⟨80798852271457662490380755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53865901514305108326920503 80798852271457662490380755)
      ·
        refine ⟨121198278407186493735571133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80798852271457662490380755 121198278407186493735571133)
        ·
          refine ⟨45449354402694935150839175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121198278407186493735571133 45449354402694935150839175)
          ·
            refine ⟨68174031604042402726258763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45449354402694935150839175 68174031604042402726258763)
            ·
              refine ⟨102261047406063604089388145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68174031604042402726258763 102261047406063604089388145)
              ·
                refine ⟨76695785554547703067041109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102261047406063604089388145 76695785554547703067041109)
                ·
                  refine ⟨112347342120919486914611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 76695785554547703067041109 112347342120919486914611)
                  ·
                    rfl

theorem cell23_1969161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 11].length) (baseStart_1969161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969161 prefixEnd_1969161 := by exact prefixLift 1969161
  have htrace : WordTrace (prefixWord ++ tailWord_1969161) baseStart_1969161 baseEnd_1969161 := by
    simpa [prefixWord, tailWord_1969161, baseEnd_1969161] using wordTrace_append hprefix tailTrace_1969161
  have hstable : (prefixWord ++ tailWord_1969161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969161).length < 2 ^ (prefixWord ++ tailWord_1969161).sum := by decide
  have hdescent : baseEnd_1969161 < baseStart_1969161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969178 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 7]
def baseStart_1969178 : Nat := 118140960795 + 1969178 * 2 ^ 59
def prefixEnd_1969178 : Nat := 4983230072969 + 3 ^ 40 * 1969178 * 2
def baseEnd_1969178 : Nat := 112348312028822423968769

theorem tailTrace_1969178 : CollatzResearch.WordTrace tailWord_1969178 prefixEnd_1969178 112348312028822423968769 := by
  unfold tailWord_1969178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17955455515002972418149047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47881214706674593115064125 17955455515002972418149047)
  ·
    refine ⟨26933183272504458627223571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17955455515002972418149047 26933183272504458627223571)
    ·
      refine ⟨40399774908756687940835357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26933183272504458627223571 40399774908756687940835357)
      ·
        refine ⟨15149915590783757977813259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40399774908756687940835357 15149915590783757977813259)
        ·
          refine ⟨22724873386175636966719889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15149915590783757977813259 22724873386175636966719889)
          ·
            refine ⟨17043655039631727725039917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22724873386175636966719889 17043655039631727725039917)
            ·
              refine ⟨6391370639861897896889969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17043655039631727725039917 6391370639861897896889969)
              ·
                refine ⟨4793527979896423422667477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391370639861897896889969 4793527979896423422667477)
                ·
                  refine ⟨112348312028822423968769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4793527979896423422667477 112348312028822423968769)
                  ·
                    rfl

theorem cell23_1969178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_1969178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969178 prefixEnd_1969178 := by exact prefixLift 1969178
  have htrace : WordTrace (prefixWord ++ tailWord_1969178) baseStart_1969178 baseEnd_1969178 := by
    simpa [prefixWord, tailWord_1969178, baseEnd_1969178] using wordTrace_append hprefix tailTrace_1969178
  have hstable : (prefixWord ++ tailWord_1969178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969178).length < 2 ^ (prefixWord ++ tailWord_1969178).sum := by decide
  have hdescent : baseEnd_1969178 < baseStart_1969178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969195 : List Nat := [1, 1, 1, 1, 2, 1, 8, 3, 5]
def baseStart_1969195 : Nat := 118140960795 + 1969195 * 2 ^ 59
def prefixEnd_1969195 : Nat := 4983230072969 + 3 ^ 40 * 1969195 * 2
def baseEnd_1969195 : Nat := 112349281936725361022927

theorem tailTrace_1969195 : CollatzResearch.WordTrace tailWord_1969195 prefixEnd_1969195 112349281936725361022927 := by
  unfold tailWord_1969195
  simp only [CollatzResearch.WordTrace]
  refine ⟨71822442100950301575965039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47881628067300201050643359 71822442100950301575965039)
  ·
    refine ⟨107733663151425452363947559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71822442100950301575965039 107733663151425452363947559)
    ·
      refine ⟨161600494727138178545921339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107733663151425452363947559 161600494727138178545921339)
      ·
        refine ⟨242400742090707267818882009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161600494727138178545921339 242400742090707267818882009)
        ·
          refine ⟨181800556568030450864161507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242400742090707267818882009 181800556568030450864161507)
          ·
            refine ⟨272700834852045676296242261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181800556568030450864161507 272700834852045676296242261)
            ·
              refine ⟨3195712908422410269096589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 272700834852045676296242261 3195712908422410269096589)
              ·
                refine ⟨1198392340658403850911221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3195712908422410269096589 1198392340658403850911221)
                ·
                  refine ⟨112349281936725361022927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1198392340658403850911221 112349281936725361022927)
                  ·
                    rfl

theorem cell23_1969195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 5].length) (baseStart_1969195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969195 prefixEnd_1969195 := by exact prefixLift 1969195
  have htrace : WordTrace (prefixWord ++ tailWord_1969195) baseStart_1969195 baseEnd_1969195 := by
    simpa [prefixWord, tailWord_1969195, baseEnd_1969195] using wordTrace_append hprefix tailTrace_1969195
  have hstable : (prefixWord ++ tailWord_1969195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969195).length < 2 ^ (prefixWord ++ tailWord_1969195).sum := by decide
  have hdescent : baseEnd_1969195 < baseStart_1969195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969206 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_1969206 : Nat := 118140960795 + 1969206 * 2 ^ 59
def prefixEnd_1969206 : Nat := 4983230072969 + 3 ^ 40 * 1969206 * 2
def baseEnd_1969206 : Nat := 1011149185717727706168793

theorem tailTrace_1969206 : CollatzResearch.WordTrace tailWord_1969206 prefixEnd_1969206 1011149185717727706168793 := by
  unfold tailWord_1969206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488927706494403153413467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47881895535940300303076981 4488927706494403153413467)
  ·
    refine ⟨6733391559741604730120201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4488927706494403153413467 6733391559741604730120201)
    ·
      refine ⟨5050043669806203547590151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6733391559741604730120201 5050043669806203547590151)
      ·
        refine ⟨7575065504709305321385227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050043669806203547590151 7575065504709305321385227)
        ·
          refine ⟨11362598257063957982077841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7575065504709305321385227 11362598257063957982077841)
          ·
            refine ⟨8521948692797968486558381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11362598257063957982077841 8521948692797968486558381)
            ·
              refine ⟨3195730759799238182459393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8521948692797968486558381 3195730759799238182459393)
              ·
                refine ⟨2396798069849428636844545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195730759799238182459393 2396798069849428636844545)
                ·
                  refine ⟨1797598552387071477633409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2396798069849428636844545 1797598552387071477633409)
                  ·
                    refine ⟨1348198914290303608225057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1797598552387071477633409 1348198914290303608225057)
                    ·
                      refine ⟨1011149185717727706168793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348198914290303608225057 1011149185717727706168793)
                      ·
                        rfl

theorem cell23_1969206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_1969206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969206 prefixEnd_1969206 := by exact prefixLift 1969206
  have htrace : WordTrace (prefixWord ++ tailWord_1969206) baseStart_1969206 baseEnd_1969206 := by
    simpa [prefixWord, tailWord_1969206, baseEnd_1969206] using wordTrace_append hprefix tailTrace_1969206
  have hstable : (prefixWord ++ tailWord_1969206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969206).length < 2 ^ (prefixWord ++ tailWord_1969206).sum := by decide
  have hdescent : baseEnd_1969206 < baseStart_1969206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969246 : List Nat := [4, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1969246 : Nat := 118140960795 + 1969246 * 2 ^ 59
def prefixEnd_1969246 : Nat := 4983230072969 + 3 ^ 40 * 1969246 * 2
def baseEnd_1969246 : Nat := 112352191660434172185401

theorem tailTrace_1969246 : CollatzResearch.WordTrace tailWord_1969246 prefixEnd_1969246 112352191660434172185401 := by
  unfold tailWord_1969246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8978037777970692160758949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47882868149177024857381061 8978037777970692160758949)
  ·
    refine ⟨1683382083369504780142303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8978037777970692160758949 1683382083369504780142303)
    ·
      refine ⟨2525073125054257170213455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683382083369504780142303 2525073125054257170213455)
      ·
        refine ⟨3787609687581385755320183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525073125054257170213455 3787609687581385755320183)
        ·
          refine ⟨5681414531372078632980275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787609687581385755320183 5681414531372078632980275)
          ·
            refine ⟨8522121797058117949470413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681414531372078632980275 8522121797058117949470413)
            ·
              refine ⟨3195795673896794231051405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8522121797058117949470413 3195795673896794231051405)
              ·
                refine ⟨1198423377711297836644277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3195795673896794231051405 1198423377711297836644277)
                ·
                  refine ⟨112352191660434172185401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1198423377711297836644277 112352191660434172185401)
                  ·
                    rfl

theorem cell23_1969246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1969246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969246 prefixEnd_1969246 := by exact prefixLift 1969246
  have htrace : WordTrace (prefixWord ++ tailWord_1969246) baseStart_1969246 baseEnd_1969246 := by
    simpa [prefixWord, tailWord_1969246, baseEnd_1969246] using wordTrace_append hprefix tailTrace_1969246
  have hstable : (prefixWord ++ tailWord_1969246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969246).length < 2 ^ (prefixWord ++ tailWord_1969246).sum := by decide
  have hdescent : baseEnd_1969246 < baseStart_1969246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969262 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1969262 : Nat := 118140960795 + 1969262 * 2 ^ 59
def prefixEnd_1969262 : Nat := 4983230072969 + 3 ^ 40 * 1969262 * 2
def baseEnd_1969262 : Nat := 1011177940634379487068535

theorem tailTrace_1969262 : CollatzResearch.WordTrace tailWord_1969262 prefixEnd_1969262 1011177940634379487068535 := by
  unfold tailWord_1969262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8978110723963446502331755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47883257194471714679102693 8978110723963446502331755)
  ·
    refine ⟨13467166085945169753497633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8978110723963446502331755 13467166085945169753497633)
    ·
      refine ⟨10100374564458877315123225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13467166085945169753497633 10100374564458877315123225)
      ·
        refine ⟨7575280923344157986342419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10100374564458877315123225 7575280923344157986342419)
        ·
          refine ⟨11362921385016236979513629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7575280923344157986342419 11362921385016236979513629)
          ·
            refine ⟨4261095519381088867317611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11362921385016236979513629 4261095519381088867317611)
            ·
              refine ⟨6391643279071633300976417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261095519381088867317611 6391643279071633300976417)
              ·
                refine ⟨4793732459303724975732313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391643279071633300976417 4793732459303724975732313)
                ·
                  refine ⟨3595299344477793731799235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4793732459303724975732313 3595299344477793731799235)
                  ·
                    refine ⟨5392949016716690597698853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3595299344477793731799235 5392949016716690597698853)
                    ·
                      refine ⟨1011177940634379487068535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5392949016716690597698853 1011177940634379487068535)
                      ·
                        rfl

theorem cell23_1969262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1969262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969262 prefixEnd_1969262 := by exact prefixLift 1969262
  have htrace : WordTrace (prefixWord ++ tailWord_1969262) baseStart_1969262 baseEnd_1969262 := by
    simpa [prefixWord, tailWord_1969262, baseEnd_1969262] using wordTrace_append hprefix tailTrace_1969262
  have hstable : (prefixWord ++ tailWord_1969262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969262).length < 2 ^ (prefixWord ++ tailWord_1969262).sum := by decide
  have hdescent : baseEnd_1969262 < baseStart_1969262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969272 : List Nat := [2, 1, 2, 1, 1, 1, 4, 6, 1, 4]
def baseStart_1969272 : Nat := 118140960795 + 1969272 * 2 ^ 59
def prefixEnd_1969272 : Nat := 4983230072969 + 3 ^ 40 * 1969272 * 2
def baseEnd_1969272 : Nat := 337061025146974815981163

theorem tailTrace_1969272 : CollatzResearch.WordTrace tailWord_1969272 prefixEnd_1969272 337061025146974815981163 := by
  unfold tailWord_1969272
  simp only [CollatzResearch.WordTrace]
  refine ⟨35912625260835671863259035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47883500347780895817678713 35912625260835671863259035)
  ·
    refine ⟨53868937891253507794888553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35912625260835671863259035 53868937891253507794888553)
    ·
      refine ⟨40401703418440130846166415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53868937891253507794888553 40401703418440130846166415)
      ·
        refine ⟨60602555127660196269249623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40401703418440130846166415 60602555127660196269249623)
        ·
          refine ⟨90903832691490294403874435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60602555127660196269249623 90903832691490294403874435)
          ·
            refine ⟨136355749037235441605811653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90903832691490294403874435 136355749037235441605811653)
            ·
              refine ⟨25566702944481645301089685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136355749037235441605811653 25566702944481645301089685)
              ·
                refine ⟨1198439200522577123488579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25566702944481645301089685 1198439200522577123488579)
                ·
                  refine ⟨1797658800783865685232869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198439200522577123488579 1797658800783865685232869)
                  ·
                    refine ⟨337061025146974815981163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797658800783865685232869 337061025146974815981163)
                    ·
                      rfl

theorem cell23_1969272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_1969272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969272 prefixEnd_1969272 := by exact prefixLift 1969272
  have htrace : WordTrace (prefixWord ++ tailWord_1969272) baseStart_1969272 baseEnd_1969272 := by
    simpa [prefixWord, tailWord_1969272, baseEnd_1969272] using wordTrace_append hprefix tailTrace_1969272
  have hstable : (prefixWord ++ tailWord_1969272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969272).length < 2 ^ (prefixWord ++ tailWord_1969272).sum := by decide
  have hdescent : baseEnd_1969272 < baseStart_1969272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969315 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 1, 5]
def baseStart_1969315 : Nat := 118140960795 + 1969315 * 2 ^ 59
def prefixEnd_1969315 : Nat := 4983230072969 + 3 ^ 40 * 1969315 * 2
def baseEnd_1969315 : Nat := 337068385036355926568597

theorem tailTrace_1969315 : CollatzResearch.WordTrace tailWord_1969315 prefixEnd_1969315 337068385036355926568597 := by
  unfold tailWord_1969315
  simp only [CollatzResearch.WordTrace]
  refine ⟨71826818860515562070333399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47884545907010374713555599 71826818860515562070333399)
  ·
    refine ⟨107740228290773343105500099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71826818860515562070333399 107740228290773343105500099)
    ·
      refine ⟨161610342436160014658250149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107740228290773343105500099 161610342436160014658250149)
      ·
        refine ⟨30301939206780002748421903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161610342436160014658250149 30301939206780002748421903)
        ·
          refine ⟨45452908810170004122632855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30301939206780002748421903 45452908810170004122632855)
          ·
            refine ⟨68179363215255006183949283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45452908810170004122632855 68179363215255006183949283)
            ·
              refine ⟨102269044822882509275923925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68179363215255006183949283 102269044822882509275923925)
              ·
                refine ⟨2396930738036308811154467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102269044822882509275923925 2396930738036308811154467)
                ·
                  refine ⟨3595396107054463216731701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396930738036308811154467 3595396107054463216731701)
                  ·
                    refine ⟨337068385036355926568597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3595396107054463216731701 337068385036355926568597)
                    ·
                      rfl

theorem cell23_1969315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 5].length) (baseStart_1969315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969315 prefixEnd_1969315 := by exact prefixLift 1969315
  have htrace : WordTrace (prefixWord ++ tailWord_1969315) baseStart_1969315 baseEnd_1969315 := by
    simpa [prefixWord, tailWord_1969315, baseEnd_1969315] using wordTrace_append hprefix tailTrace_1969315
  have hstable : (prefixWord ++ tailWord_1969315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969315).length < 2 ^ (prefixWord ++ tailWord_1969315).sum := by decide
  have hdescent : baseEnd_1969315 < baseStart_1969315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969335 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_1969335 : Nat := 118140960795 + 1969335 * 2 ^ 59
def prefixEnd_1969335 : Nat := 4983230072969 + 3 ^ 40 * 1969335 * 2
def baseEnd_1969335 : Nat := 1011215424722157701455699

theorem tailTrace_1969335 : CollatzResearch.WordTrace tailWord_1969335 prefixEnd_1969335 1011215424722157701455699 := by
  unfold tailWord_1969335
  simp only [CollatzResearch.WordTrace]
  refine ⟨71827548320443105486061459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47885032213628736990707639 71827548320443105486061459)
  ·
    refine ⟨107741322480664658229092189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71827548320443105486061459 107741322480664658229092189)
    ·
      refine ⟨40402995930249246835909571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107741322480664658229092189 40402995930249246835909571)
      ·
        refine ⟨60604493895373870253864357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40402995930249246835909571 60604493895373870253864357)
        ·
          refine ⟨11363342605382600672599567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60604493895373870253864357 11363342605382600672599567)
          ·
            refine ⟨17045013908073901008899351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11363342605382600672599567 17045013908073901008899351)
            ·
              refine ⟨25567520862110851513349027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17045013908073901008899351 25567520862110851513349027)
              ·
                refine ⟨38351281293166277270023541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25567520862110851513349027 38351281293166277270023541)
                ·
                  refine ⟨3595432621234338494064707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38351281293166277270023541 3595432621234338494064707)
                  ·
                    refine ⟨5393148931851507741097061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3595432621234338494064707 5393148931851507741097061)
                    ·
                      refine ⟨1011215424722157701455699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5393148931851507741097061 1011215424722157701455699)
                      ·
                        rfl

theorem cell23_1969335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_1969335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969335 prefixEnd_1969335 := by exact prefixLift 1969335
  have htrace : WordTrace (prefixWord ++ tailWord_1969335) baseStart_1969335 baseEnd_1969335 := by
    simpa [prefixWord, tailWord_1969335, baseEnd_1969335] using wordTrace_append hprefix tailTrace_1969335
  have hstable : (prefixWord ++ tailWord_1969335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969335).length < 2 ^ (prefixWord ++ tailWord_1969335).sum := by decide
  have hdescent : baseEnd_1969335 < baseStart_1969335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969350 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1969350 : Nat := 118140960795 + 1969350 * 2 ^ 59
def prefixEnd_1969350 : Nat := 4983230072969 + 3 ^ 40 * 1969350 * 2
def baseEnd_1969350 : Nat := 1011223126931975142768131

theorem tailTrace_1969350 : CollatzResearch.WordTrace tailWord_1969350 prefixEnd_1969350 1011223126931975142768131 := by
  unfold tailWord_1969350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244627981730898845245547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47885396943592508698571669 2244627981730898845245547)
  ·
    refine ⟨3366941972596348267868321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244627981730898845245547 3366941972596348267868321)
    ·
      refine ⟨2525206479447261200901241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3366941972596348267868321 2525206479447261200901241)
      ·
        refine ⟨1893904859585445900675931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2525206479447261200901241 1893904859585445900675931)
        ·
          refine ⟨2840857289378168851013897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893904859585445900675931 2840857289378168851013897)
          ·
            refine ⟨2130642967033626638260423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840857289378168851013897 2130642967033626638260423)
            ·
              refine ⟨3195964450550439957390635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130642967033626638260423 3195964450550439957390635)
              ·
                refine ⟨4793946675825659936085953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3195964450550439957390635 4793946675825659936085953)
                ·
                  refine ⟨3595460006869244952064465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4793946675825659936085953 3595460006869244952064465)
                  ·
                    refine ⟨2696595005151933714048349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3595460006869244952064465 2696595005151933714048349)
                    ·
                      refine ⟨1011223126931975142768131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2696595005151933714048349 1011223126931975142768131)
                      ·
                        rfl

theorem cell23_1969350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1969350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969350 prefixEnd_1969350 := by exact prefixLift 1969350
  have htrace : WordTrace (prefixWord ++ tailWord_1969350) baseStart_1969350 baseEnd_1969350 := by
    simpa [prefixWord, tailWord_1969350, baseEnd_1969350] using wordTrace_append hprefix tailTrace_1969350
  have hstable : (prefixWord ++ tailWord_1969350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969350).length < 2 ^ (prefixWord ++ tailWord_1969350).sum := by decide
  have hdescent : baseEnd_1969350 < baseStart_1969350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969362 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_1969362 : Nat := 118140960795 + 1969362 * 2 ^ 59
def prefixEnd_1969362 : Nat := 4983230072969 + 3 ^ 40 * 1969362 * 2
def baseEnd_1969362 : Nat := 337076429566609698606025

theorem tailTrace_1969362 : CollatzResearch.WordTrace tailWord_1969362 prefixEnd_1969362 337076429566609698606025 := by
  unfold tailWord_1969362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957133272836322274323585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47885688727563526064862893 17957133272836322274323585)
  ·
    refine ⟨13467849954627241705742689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17957133272836322274323585 13467849954627241705742689)
    ·
      refine ⟨10100887465970431279307017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13467849954627241705742689 10100887465970431279307017)
      ·
        refine ⟨7575665599477823459480263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10100887465970431279307017 7575665599477823459480263)
        ·
          refine ⟨11363498399216735189220395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7575665599477823459480263 11363498399216735189220395)
          ·
            refine ⟨17045247598825102783830593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11363498399216735189220395 17045247598825102783830593)
            ·
              refine ⟨12783935699118827087872945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17045247598825102783830593 12783935699118827087872945)
              ·
                refine ⟨9587951774339120315904709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12783935699118827087872945 9587951774339120315904709)
                ·
                  refine ⟨1797740957688585059232133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9587951774339120315904709 1797740957688585059232133)
                  ·
                    refine ⟨337076429566609698606025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797740957688585059232133 337076429566609698606025)
                    ·
                      rfl

theorem cell23_1969362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_1969362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969362 prefixEnd_1969362 := by exact prefixLift 1969362
  have htrace : WordTrace (prefixWord ++ tailWord_1969362) baseStart_1969362 baseEnd_1969362 := by
    simpa [prefixWord, tailWord_1969362, baseEnd_1969362] using wordTrace_append hprefix tailTrace_1969362
  have hstable : (prefixWord ++ tailWord_1969362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969362).length < 2 ^ (prefixWord ++ tailWord_1969362).sum := by decide
  have hdescent : baseEnd_1969362 < baseStart_1969362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969366 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1969366 : Nat := 118140960795 + 1969366 * 2 ^ 59
def prefixEnd_1969366 : Nat := 4983230072969 + 3 ^ 40 * 1969366 * 2
def baseEnd_1969366 : Nat := 337077114207482360056019

theorem tailTrace_1969366 : CollatzResearch.WordTrace tailWord_1969366 prefixEnd_1969366 337077114207482360056019 := by
  unfold tailWord_1969366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4489292436458174861277497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47885785988887198520293301 4489292436458174861277497)
  ·
    refine ⟨3366969327343631145958123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4489292436458174861277497 3366969327343631145958123)
    ·
      refine ⟨5050453991015446718937185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3366969327343631145958123 5050453991015446718937185)
      ·
        refine ⟨3787840493261585039202889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5050453991015446718937185 3787840493261585039202889)
        ·
          refine ⟨2840880369946188779402167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787840493261585039202889 2840880369946188779402167)
          ·
            refine ⟨4261320554919283169103251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840880369946188779402167 4261320554919283169103251)
            ·
              refine ⟨6391980832378924753654877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261320554919283169103251 6391980832378924753654877)
              ·
                refine ⟨2396992812142096782620579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6391980832378924753654877 2396992812142096782620579)
                ·
                  refine ⟨3595489218213145173930869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396992812142096782620579 3595489218213145173930869)
                  ·
                    refine ⟨337077114207482360056019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3595489218213145173930869 337077114207482360056019)
                    ·
                      rfl

theorem cell23_1969366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1969366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969366 prefixEnd_1969366 := by exact prefixLift 1969366
  have htrace : WordTrace (prefixWord ++ tailWord_1969366) baseStart_1969366 baseEnd_1969366 := by
    simpa [prefixWord, tailWord_1969366, baseEnd_1969366] using wordTrace_append hprefix tailTrace_1969366
  have hstable : (prefixWord ++ tailWord_1969366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969366).length < 2 ^ (prefixWord ++ tailWord_1969366).sum := by decide
  have hdescent : baseEnd_1969366 < baseStart_1969366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969386 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_1969386 : Nat := 118140960795 + 1969386 * 2 ^ 59
def prefixEnd_1969386 : Nat := 4983230072969 + 3 ^ 40 * 1969386 * 2
def baseEnd_1969386 : Nat := 1011241612235537001917965

theorem tailTrace_1969386 : CollatzResearch.WordTrace tailWord_1969386 prefixEnd_1969386 1011241612235537001917965 := by
  unfold tailWord_1969386
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957352110814585299042003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47886272295505560797445341 17957352110814585299042003)
  ·
    refine ⟨26936028166221877948563005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17957352110814585299042003 26936028166221877948563005)
    ·
      refine ⟨10101010562333204230711127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26936028166221877948563005 10101010562333204230711127)
      ·
        refine ⟨15151515843499806346066691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10101010562333204230711127 15151515843499806346066691)
        ·
          refine ⟨22727273765249709519100037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15151515843499806346066691 22727273765249709519100037)
          ·
            refine ⟨4261363830984320534831257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22727273765249709519100037 4261363830984320534831257)
            ·
              refine ⟨3196022873238240401123443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261363830984320534831257 3196022873238240401123443)
              ·
                refine ⟨4794034309857360601685165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196022873238240401123443 4794034309857360601685165)
                ·
                  refine ⟨1797762866196510225631937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4794034309857360601685165 1797762866196510225631937)
                  ·
                    refine ⟨1348322149647382669223953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1797762866196510225631937 1348322149647382669223953)
                    ·
                      refine ⟨1011241612235537001917965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348322149647382669223953 1011241612235537001917965)
                      ·
                        rfl

theorem cell23_1969386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_1969386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969386 prefixEnd_1969386 := by exact prefixLift 1969386
  have htrace : WordTrace (prefixWord ++ tailWord_1969386) baseStart_1969386 baseEnd_1969386 := by
    simpa [prefixWord, tailWord_1969386, baseEnd_1969386] using wordTrace_append hprefix tailTrace_1969386
  have hstable : (prefixWord ++ tailWord_1969386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969386).length < 2 ^ (prefixWord ++ tailWord_1969386).sum := by decide
  have hdescent : baseEnd_1969386 < baseStart_1969386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969406 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1969406 : Nat := 118140960795 + 1969406 * 2 ^ 59
def prefixEnd_1969406 : Nat := 4983230072969 + 3 ^ 40 * 1969406 * 2
def baseEnd_1969406 : Nat := 1011251881848626923667873

theorem tailTrace_1969406 : CollatzResearch.WordTrace tailWord_1969406 prefixEnd_1969406 1011251881848626923667873 := by
  unfold tailWord_1969406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8978767237898235576487009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47886758602123923074597381 8978767237898235576487009)
  ·
    refine ⟨6734075428423676682365257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8978767237898235576487009 6734075428423676682365257)
    ·
      refine ⟨5050556571317757511773943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6734075428423676682365257 5050556571317757511773943)
      ·
        refine ⟨7575834856976636267660915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050556571317757511773943 7575834856976636267660915)
        ·
          refine ⟨11363752285464954401491373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7575834856976636267660915 11363752285464954401491373)
          ·
            refine ⟨4261407107049357900559265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11363752285464954401491373 4261407107049357900559265)
            ·
              refine ⟨3196055330287018425419449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261407107049357900559265 3196055330287018425419449)
              ·
                refine ⟨2397041497715263819064587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3196055330287018425419449 2397041497715263819064587)
                ·
                  refine ⟨3595562246572895728596881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397041497715263819064587 3595562246572895728596881)
                  ·
                    refine ⟨2696671684929671796447661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3595562246572895728596881 2696671684929671796447661)
                    ·
                      refine ⟨1011251881848626923667873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2696671684929671796447661 1011251881848626923667873)
                      ·
                        rfl

theorem cell23_1969406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1969406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969406 prefixEnd_1969406 := by exact prefixLift 1969406
  have htrace : WordTrace (prefixWord ++ tailWord_1969406) baseStart_1969406 baseEnd_1969406 := by
    simpa [prefixWord, tailWord_1969406, baseEnd_1969406] using wordTrace_append hprefix tailTrace_1969406
  have hstable : (prefixWord ++ tailWord_1969406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969406).length < 2 ^ (prefixWord ++ tailWord_1969406).sum := by decide
  have hdescent : baseEnd_1969406 < baseStart_1969406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969426 : List Nat := [3, 2, 4, 2, 2, 1, 9]
def baseStart_1969426 : Nat := 118140960795 + 1969426 * 2 ^ 59
def prefixEnd_1969426 : Nat := 4983230072969 + 3 ^ 40 * 1969426 * 2
def baseEnd_1969426 : Nat := 12484717919280454881701

theorem tailTrace_1969426 : CollatzResearch.WordTrace tailWord_1969426 prefixEnd_1969426 12484717919280454881701 := by
  unfold tailWord_1969426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957716840778357006906033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47887244908742285351749421 17957716840778357006906033)
  ·
    refine ⟨13468287630583767755179525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17957716840778357006906033 13468287630583767755179525)
    ·
      refine ⟨2525303930734456454096161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13468287630583767755179525 2525303930734456454096161)
      ·
        refine ⟨1893977948050842340572121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2525303930734456454096161 1893977948050842340572121)
        ·
          refine ⟨1420483461038131755429091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1893977948050842340572121 1420483461038131755429091)
          ·
            refine ⟨2130725191557197633143637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420483461038131755429091 2130725191557197633143637)
            ·
              refine ⟨12484717919280454881701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2130725191557197633143637 12484717919280454881701)
              ·
                rfl

theorem cell23_1969426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 9].length) (baseStart_1969426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969426 prefixEnd_1969426 := by exact prefixLift 1969426
  have htrace : WordTrace (prefixWord ++ tailWord_1969426) baseStart_1969426 baseEnd_1969426 := by
    simpa [prefixWord, tailWord_1969426, baseEnd_1969426] using wordTrace_append hprefix tailTrace_1969426
  have hstable : (prefixWord ++ tailWord_1969426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969426).length < 2 ^ (prefixWord ++ tailWord_1969426).sum := by decide
  have hdescent : baseEnd_1969426 < baseStart_1969426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969453 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1969453 : Nat := 118140960795 + 1969453 * 2 ^ 59
def prefixEnd_1969453 : Nat := 4983230072969 + 3 ^ 40 * 1969453 * 2
def baseEnd_1969453 : Nat := 1011276015439388239780157

theorem tailTrace_1969453 : CollatzResearch.WordTrace tailWord_1969453 prefixEnd_1969453 1011276015439388239780157 := by
  unfold tailWord_1969453
  simp only [CollatzResearch.WordTrace]
  refine ⟨71831852134015611638857013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47887901422677074425904675 71831852134015611638857013)
  ·
    refine ⟨6734236137563963591142845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71831852134015611638857013 6734236137563963591142845)
    ·
      refine ⟨2525338551586486346678567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6734236137563963591142845 2525338551586486346678567)
      ·
        refine ⟨3788007827379729520017851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525338551586486346678567 3788007827379729520017851)
        ·
          refine ⟨5682011741069594280026777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788007827379729520017851 5682011741069594280026777)
          ·
            refine ⟨4261508805802195710020083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5682011741069594280026777 4261508805802195710020083)
            ·
              refine ⟨6392263208703293565030125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261508805802195710020083 6392263208703293565030125)
              ·
                refine ⟨2397098703263735086886297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6392263208703293565030125 2397098703263735086886297)
                ·
                  refine ⟨1797824027447801315164723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2397098703263735086886297 1797824027447801315164723)
                  ·
                    refine ⟨2696736041171701972747085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1797824027447801315164723 2696736041171701972747085)
                    ·
                      refine ⟨1011276015439388239780157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2696736041171701972747085 1011276015439388239780157)
                      ·
                        rfl

theorem cell23_1969453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1969453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969453 prefixEnd_1969453 := by exact prefixLift 1969453
  have htrace : WordTrace (prefixWord ++ tailWord_1969453) baseStart_1969453 baseEnd_1969453 := by
    simpa [prefixWord, tailWord_1969453, baseEnd_1969453] using wordTrace_append hprefix tailTrace_1969453
  have hstable : (prefixWord ++ tailWord_1969453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969453).length < 2 ^ (prefixWord ++ tailWord_1969453).sum := by decide
  have hdescent : baseEnd_1969453 < baseStart_1969453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969455 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_1969455 : Nat := 118140960795 + 1969455 * 2 ^ 59
def prefixEnd_1969455 : Nat := 4983230072969 + 3 ^ 40 * 1969455 * 2
def baseEnd_1969455 : Nat := 1011277042400697231955147

theorem tailTrace_1969455 : CollatzResearch.WordTrace tailWord_1969455 prefixEnd_1969455 1011277042400697231955147 := by
  unfold tailWord_1969455
  simp only [CollatzResearch.WordTrace]
  refine ⟨71831925080008365980429819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47887950053338910653619879 71831925080008365980429819)
  ·
    refine ⟨107747887620012548970644729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71831925080008365980429819 107747887620012548970644729)
    ·
      refine ⟨80810915715009411727983547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107747887620012548970644729 80810915715009411727983547)
      ·
        refine ⟨121216373572514117591975321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80810915715009411727983547 121216373572514117591975321)
        ·
          refine ⟨90912280179385588193981491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121216373572514117591975321 90912280179385588193981491)
          ·
            refine ⟨136368420269078382290972237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90912280179385588193981491 136368420269078382290972237)
            ·
              refine ⟨51138157600904393359114589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136368420269078382290972237 51138157600904393359114589)
              ·
                refine ⟨19176809100339147509667971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51138157600904393359114589 19176809100339147509667971)
                ·
                  refine ⟨28765213650508721264501957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19176809100339147509667971 28765213650508721264501957)
                  ·
                    refine ⟨5393477559470385237094117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28765213650508721264501957 5393477559470385237094117)
                    ·
                      refine ⟨1011277042400697231955147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5393477559470385237094117 1011277042400697231955147)
                      ·
                        rfl

theorem cell23_1969455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_1969455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969455 prefixEnd_1969455 := by exact prefixLift 1969455
  have htrace : WordTrace (prefixWord ++ tailWord_1969455) baseStart_1969455 baseEnd_1969455 := by
    simpa [prefixWord, tailWord_1969455, baseEnd_1969455] using wordTrace_append hprefix tailTrace_1969455
  have hstable : (prefixWord ++ tailWord_1969455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969455).length < 2 ^ (prefixWord ++ tailWord_1969455).sum := by decide
  have hdescent : baseEnd_1969455 < baseStart_1969455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969476 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1969476 : Nat := 118140960795 + 1969476 * 2 ^ 59
def prefixEnd_1969476 : Nat := 4983230072969 + 3 ^ 40 * 1969476 * 2
def baseEnd_1969476 : Nat := 1011287825494441649792551

theorem tailTrace_1969476 : CollatzResearch.WordTrace tailWord_1969476 prefixEnd_1969476 1011287825494441649792551 := by
  unfold tailWord_1969476
  simp only [CollatzResearch.WordTrace]
  refine ⟨35916345506466143283472141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47888460675288191044629521 35916345506466143283472141)
  ·
    refine ⟨13468629564924803731302053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35916345506466143283472141 13468629564924803731302053)
    ·
      refine ⟨2525368043423400699619135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13468629564924803731302053 2525368043423400699619135)
      ·
        refine ⟨3788052065135101049428703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525368043423400699619135 3788052065135101049428703)
        ·
          refine ⟨5682078097702651574143055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788052065135101049428703 5682078097702651574143055)
          ·
            refine ⟨8523117146553977361214583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5682078097702651574143055 8523117146553977361214583)
            ·
              refine ⟨12784675719830966041821875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8523117146553977361214583 12784675719830966041821875)
              ·
                refine ⟨19177013579746449062732813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784675719830966041821875 19177013579746449062732813)
                ·
                  refine ⟨7191380092404918398524805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19177013579746449062732813 7191380092404918398524805)
                  ·
                    refine ⟨1348383767325922199723401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191380092404918398524805 1348383767325922199723401)
                    ·
                      refine ⟨1011287825494441649792551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348383767325922199723401 1011287825494441649792551)
                      ·
                        rfl

theorem cell23_1969476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1969476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969476 prefixEnd_1969476 := by exact prefixLift 1969476
  have htrace : WordTrace (prefixWord ++ tailWord_1969476) baseStart_1969476 baseEnd_1969476 := by
    simpa [prefixWord, tailWord_1969476, baseEnd_1969476] using wordTrace_append hprefix tailTrace_1969476
  have hstable : (prefixWord ++ tailWord_1969476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969476).length < 2 ^ (prefixWord ++ tailWord_1969476).sum := by decide
  have hdescent : baseEnd_1969476 < baseStart_1969476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969493 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_1969493 : Nat := 118140960795 + 1969493 * 2 ^ 59
def prefixEnd_1969493 : Nat := 4983230072969 + 3 ^ 40 * 1969493 * 2
def baseEnd_1969493 : Nat := 1011296554665568083279973

theorem tailTrace_1969493 : CollatzResearch.WordTrace tailWord_1969493 prefixEnd_1969493 1011296554665568083279973 := by
  unfold tailWord_1969493
  simp only [CollatzResearch.WordTrace]
  refine ⟨71833311053870698470313133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47888874035913798980208755 71833311053870698470313133)
  ·
    refine ⟨26937491645201511926367425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71833311053870698470313133 26937491645201511926367425)
    ·
      refine ⟨20203118733901133944775569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26937491645201511926367425 20203118733901133944775569)
      ·
        refine ⟨15152339050425850458581677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20203118733901133944775569 15152339050425850458581677)
        ·
          refine ⟨5682127143909693921968129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15152339050425850458581677 5682127143909693921968129)
          ·
            refine ⟨4261595357932270441476097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5682127143909693921968129 4261595357932270441476097)
            ·
              refine ⟨3196196518449202831107073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261595357932270441476097 3196196518449202831107073)
              ·
                refine ⟨2397147388836902123330305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3196196518449202831107073 2397147388836902123330305)
                ·
                  refine ⟨1797860541627676592497729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2397147388836902123330305 1797860541627676592497729)
                  ·
                    refine ⟨1348395406220757444373297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1797860541627676592497729 1348395406220757444373297)
                    ·
                      refine ⟨1011296554665568083279973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348395406220757444373297 1011296554665568083279973)
                      ·
                        rfl

theorem cell23_1969493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_1969493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969493 prefixEnd_1969493 := by exact prefixLift 1969493
  have htrace : WordTrace (prefixWord ++ tailWord_1969493) baseStart_1969493 baseEnd_1969493 := by
    simpa [prefixWord, tailWord_1969493, baseEnd_1969493] using wordTrace_append hprefix tailTrace_1969493
  have hstable : (prefixWord ++ tailWord_1969493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969493).length < 2 ^ (prefixWord ++ tailWord_1969493).sum := by decide
  have hdescent : baseEnd_1969493 < baseStart_1969493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969532 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1969532 : Nat := 118140960795 + 1969532 * 2 ^ 59
def prefixEnd_1969532 : Nat := 4983230072969 + 3 ^ 40 * 1969532 * 2
def baseEnd_1969532 : Nat := 1011316580411093430692293

theorem tailTrace_1969532 : CollatzResearch.WordTrace tailWord_1969532 prefixEnd_1969532 1011316580411093430692293 := by
  unfold tailWord_1969532
  simp only [CollatzResearch.WordTrace]
  refine ⟨35917366750364704065491425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47889822333819605420655233 35917366750364704065491425)
  ·
    refine ⟨26938025062773528049118569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35917366750364704065491425 26938025062773528049118569)
    ·
      refine ⟨20203518797080146036838927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26938025062773528049118569 20203518797080146036838927)
      ·
        refine ⟨30305278195620219055258391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20203518797080146036838927 30305278195620219055258391)
        ·
          refine ⟨45457917293430328582887587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30305278195620219055258391 45457917293430328582887587)
          ·
            refine ⟨68186875940145492874331381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45457917293430328582887587 68186875940145492874331381)
            ·
              refine ⟨6392519619388639956968567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68186875940145492874331381 6392519619388639956968567)
              ·
                refine ⟨9588779429082959935452851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6392519619388639956968567 9588779429082959935452851)
                ·
                  refine ⟨14383169143624439903179277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9588779429082959935452851 14383169143624439903179277)
                  ·
                    refine ⟨5393688428859164963692229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14383169143624439903179277 5393688428859164963692229)
                    ·
                      refine ⟨1011316580411093430692293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5393688428859164963692229 1011316580411093430692293)
                      ·
                        rfl

theorem cell23_1969532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1969532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969532 prefixEnd_1969532 := by exact prefixLift 1969532
  have htrace : WordTrace (prefixWord ++ tailWord_1969532) baseStart_1969532 baseEnd_1969532 := by
    simpa [prefixWord, tailWord_1969532, baseEnd_1969532] using wordTrace_append hprefix tailTrace_1969532
  have hstable : (prefixWord ++ tailWord_1969532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969532).length < 2 ^ (prefixWord ++ tailWord_1969532).sum := by decide
  have hdescent : baseEnd_1969532 < baseStart_1969532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969535 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_1969535 : Nat := 118140960795 + 1969535 * 2 ^ 59
def prefixEnd_1969535 : Nat := 4983230072969 + 3 ^ 40 * 1969535 * 2
def baseEnd_1969535 : Nat := 1011318120853056918954779

theorem tailTrace_1969535 : CollatzResearch.WordTrace tailWord_1969535 prefixEnd_1969535 1011318120853056918954779 := by
  unfold tailWord_1969535
  simp only [CollatzResearch.WordTrace]
  refine ⟨71834842919718539643342059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47889895279812359762228039 71834842919718539643342059)
  ·
    refine ⟨107752264379577809465013089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71834842919718539643342059 107752264379577809465013089)
    ·
      refine ⟨80814198284683357098759817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107752264379577809465013089 80814198284683357098759817)
      ·
        refine ⟨60610648713512517824069863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80814198284683357098759817 60610648713512517824069863)
        ·
          refine ⟨90915973070268776736104795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60610648713512517824069863 90915973070268776736104795)
          ·
            refine ⟨136373959605403165104157193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90915973070268776736104795 136373959605403165104157193)
            ·
              refine ⟨102280469704052373828117895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136373959605403165104157193 102280469704052373828117895)
              ·
                refine ⟨153420704556078560742176843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102280469704052373828117895 153420704556078560742176843)
                ·
                  refine ⟨230131056834117841113265265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153420704556078560742176843 230131056834117841113265265)
                  ·
                    refine ⟨172598292625588380834948949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230131056834117841113265265 172598292625588380834948949)
                    ·
                      refine ⟨1011318120853056918954779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 172598292625588380834948949 1011318120853056918954779)
                      ·
                        rfl

theorem cell23_1969535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_1969535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969535 prefixEnd_1969535 := by exact prefixLift 1969535
  have htrace : WordTrace (prefixWord ++ tailWord_1969535) baseStart_1969535 baseEnd_1969535 := by
    simpa [prefixWord, tailWord_1969535, baseEnd_1969535] using wordTrace_append hprefix tailTrace_1969535
  have hstable : (prefixWord ++ tailWord_1969535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969535).length < 2 ^ (prefixWord ++ tailWord_1969535).sum := by decide
  have hdescent : baseEnd_1969535 < baseStart_1969535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969562 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1969562 : Nat := 118140960795 + 1969562 * 2 ^ 59
def prefixEnd_1969562 : Nat := 4983230072969 + 3 ^ 40 * 1969562 * 2
def baseEnd_1969562 : Nat := 1011331984830728313317155

theorem tailTrace_1969562 : CollatzResearch.WordTrace tailWord_1969562 prefixEnd_1969562 1011331984830728313317155 := by
  unfold tailWord_1969562
  simp only [CollatzResearch.WordTrace]
  refine ⟨17958956922655180813643735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47890551793747148836383293 17958956922655180813643735)
  ·
    refine ⟨26938435383982771220465603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17958956922655180813643735 26938435383982771220465603)
    ·
      refine ⟨40407653075974156830698405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26938435383982771220465603 40407653075974156830698405)
      ·
        refine ⟨7576434951745154405755951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40407653075974156830698405 7576434951745154405755951)
        ·
          refine ⟨11364652427617731608633927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7576434951745154405755951 11364652427617731608633927)
          ·
            refine ⟨17046978641426597412950891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11364652427617731608633927 17046978641426597412950891)
            ·
              refine ⟨25570467962139896119426337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17046978641426597412950891 25570467962139896119426337)
              ·
                refine ⟨19177850971604922089569753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25570467962139896119426337 19177850971604922089569753)
                ·
                  refine ⟨14383388228703691567177315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19177850971604922089569753 14383388228703691567177315)
                  ·
                    refine ⟨21575082343055537350765973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14383388228703691567177315 21575082343055537350765973)
                    ·
                      refine ⟨1011331984830728313317155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21575082343055537350765973 1011331984830728313317155)
                      ·
                        rfl

theorem cell23_1969562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1969562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969562 prefixEnd_1969562 := by exact prefixLift 1969562
  have htrace : WordTrace (prefixWord ++ tailWord_1969562) baseStart_1969562 baseEnd_1969562 := by
    simpa [prefixWord, tailWord_1969562, baseEnd_1969562] using wordTrace_append hprefix tailTrace_1969562
  have hstable : (prefixWord ++ tailWord_1969562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969562).length < 2 ^ (prefixWord ++ tailWord_1969562).sum := by decide
  have hdescent : baseEnd_1969562 < baseStart_1969562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969599 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 3]
def baseStart_1969599 : Nat := 118140960795 + 1969599 * 2 ^ 59
def prefixEnd_1969599 : Nat := 4983230072969 + 3 ^ 40 * 1969599 * 2
def baseEnd_1969599 : Nat := 1011350983614944668554485

theorem tailTrace_1969599 : CollatzResearch.WordTrace tailWord_1969599 prefixEnd_1969599 1011350983614944668554485 := by
  unfold tailWord_1969599
  simp only [CollatzResearch.WordTrace]
  refine ⟨71837177191486678573671851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47891451460991119049114567 71837177191486678573671851)
  ·
    refine ⟨107755765787230017860507777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71837177191486678573671851 107755765787230017860507777)
    ·
      refine ⟨80816824340422513395380833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107755765787230017860507777 80816824340422513395380833)
      ·
        refine ⟨60612618255316885046535625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80816824340422513395380833 60612618255316885046535625)
        ·
          refine ⟨45459463691487663784901719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60612618255316885046535625 45459463691487663784901719)
          ·
            refine ⟨68189195537231495677352579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45459463691487663784901719 68189195537231495677352579)
            ·
              refine ⟨102283793305847243516028869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68189195537231495677352579 102283793305847243516028869)
              ·
                refine ⟨19178211244846358159255413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102283793305847243516028869 19178211244846358159255413)
                ·
                  refine ⟨1797957304204346077430195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19178211244846358159255413 1797957304204346077430195)
                  ·
                    refine ⟨2696935956306519116145293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1797957304204346077430195 2696935956306519116145293)
                    ·
                      refine ⟨1011350983614944668554485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2696935956306519116145293 1011350983614944668554485)
                      ·
                        rfl

theorem cell23_1969599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_1969599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969599 prefixEnd_1969599 := by exact prefixLift 1969599
  have htrace : WordTrace (prefixWord ++ tailWord_1969599) baseStart_1969599 baseEnd_1969599 := by
    simpa [prefixWord, tailWord_1969599, baseEnd_1969599] using wordTrace_append hprefix tailTrace_1969599
  have hstable : (prefixWord ++ tailWord_1969599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969599).length < 2 ^ (prefixWord ++ tailWord_1969599).sum := by decide
  have hdescent : baseEnd_1969599 < baseStart_1969599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969649 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 1, 6]
def baseStart_1969649 : Nat := 118140960795 + 1969649 * 2 ^ 59
def prefixEnd_1969649 : Nat := 4983230072969 + 3 ^ 40 * 1969649 * 2
def baseEnd_1969649 : Nat := 337125552549223157643085

theorem tailTrace_1969649 : CollatzResearch.WordTrace tailWord_1969649 prefixEnd_1969649 337125552549223157643085 := by
  unfold tailWord_1969649
  simp only [CollatzResearch.WordTrace]
  refine ⟨71839000841305537112992001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47892667227537024741994667 71839000841305537112992001)
  ·
    refine ⟨53879250630979152834744001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71839000841305537112992001 53879250630979152834744001)
    ·
      refine ⟨40409437973234364626058001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53879250630979152834744001 40409437973234364626058001)
      ·
        refine ⟨30307078479925773469543501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40409437973234364626058001 30307078479925773469543501)
        ·
          refine ⟨11365154429972165051078813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30307078479925773469543501 11365154429972165051078813)
          ·
            refine ⟨4261932911239561894154555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11365154429972165051078813 4261932911239561894154555)
            ·
              refine ⟨6392899366859342841231833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261932911239561894154555 6392899366859342841231833)
              ·
                refine ⟨4794674525144507130923875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6392899366859342841231833 4794674525144507130923875)
                ·
                  refine ⟨7192011787716760696385813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794674525144507130923875 7192011787716760696385813)
                  ·
                    refine ⟨337125552549223157643085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7192011787716760696385813 337125552549223157643085)
                    ·
                      rfl

theorem cell23_1969649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_1969649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969649 prefixEnd_1969649 := by exact prefixLift 1969649
  have htrace : WordTrace (prefixWord ++ tailWord_1969649) baseStart_1969649 baseEnd_1969649 := by
    simpa [prefixWord, tailWord_1969649, baseEnd_1969649] using wordTrace_append hprefix tailTrace_1969649
  have hstable : (prefixWord ++ tailWord_1969649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969649).length < 2 ^ (prefixWord ++ tailWord_1969649).sum := by decide
  have hdescent : baseEnd_1969649 < baseStart_1969649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969696 : List Nat := [2, 1, 1, 6, 1, 2, 3, 7]
def baseStart_1969696 : Nat := 118140960795 + 1969696 * 2 ^ 59
def prefixEnd_1969696 : Nat := 4983230072969 + 3 ^ 40 * 1969696 * 2
def baseEnd_1969696 : Nat := 37459288564386325520057

theorem tailTrace_1969696 : CollatzResearch.WordTrace tailWord_1969696 prefixEnd_1969696 37459288564386325520057 := by
  unfold tailWord_1969696
  simp only [CollatzResearch.WordTrace]
  refine ⟨35920357536067632069976471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47893810048090176093301961 35920357536067632069976471)
  ·
    refine ⟨53880536304101448104964707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35920357536067632069976471 53880536304101448104964707)
    ·
      refine ⟨80820804456152172157447061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53880536304101448104964707 80820804456152172157447061)
      ·
        refine ⟨3788475208882133069880331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80820804456152172157447061 3788475208882133069880331)
        ·
          refine ⟨5682712813323199604820497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788475208882133069880331 5682712813323199604820497)
          ·
            refine ⟨4262034609992399703615373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5682712813323199604820497 4262034609992399703615373)
            ·
              refine ⟨1598262978747149888855765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4262034609992399703615373 1598262978747149888855765)
              ·
                refine ⟨37459288564386325520057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1598262978747149888855765 37459288564386325520057)
                ·
                  rfl

theorem cell23_1969696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 7].length) (baseStart_1969696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969696 prefixEnd_1969696 := by exact prefixLift 1969696
  have htrace : WordTrace (prefixWord ++ tailWord_1969696) baseStart_1969696 baseEnd_1969696 := by
    simpa [prefixWord, tailWord_1969696, baseEnd_1969696] using wordTrace_append hprefix tailTrace_1969696
  have hstable : (prefixWord ++ tailWord_1969696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969696).length < 2 ^ (prefixWord ++ tailWord_1969696).sum := by decide
  have hdescent : baseEnd_1969696 < baseStart_1969696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969706 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1969706 : Nat := 118140960795 + 1969706 * 2 ^ 59
def prefixEnd_1969706 : Nat := 4983230072969 + 3 ^ 40 * 1969706 * 2
def baseEnd_1969706 : Nat := 1011405926044975749916493

theorem tailTrace_1969706 : CollatzResearch.WordTrace tailWord_1969706 prefixEnd_1969706 1011405926044975749916493 := by
  unfold tailWord_1969706
  simp only [CollatzResearch.WordTrace]
  refine ⟨17960269950524758961954243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47894053201399357231877981 17960269950524758961954243)
  ·
    refine ⟨26940404925787138442931365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17960269950524758961954243 26940404925787138442931365)
    ·
      refine ⟨5051325923585088458049631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26940404925787138442931365 5051325923585088458049631)
      ·
        refine ⟨7576988885377632687074447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5051325923585088458049631 7576988885377632687074447)
        ·
          refine ⟨11365483328066449030611671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7576988885377632687074447 11365483328066449030611671)
          ·
            refine ⟨17048224992099673545917507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11365483328066449030611671 17048224992099673545917507)
            ·
              refine ⟨25572337488149510318876261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17048224992099673545917507 25572337488149510318876261)
              ·
                refine ⟨4794813279028033184789299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25572337488149510318876261 4794813279028033184789299)
                ·
                  refine ⟨7192219918542049777183949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794813279028033184789299 7192219918542049777183949)
                  ·
                    refine ⟨2697082469453268666443981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7192219918542049777183949 2697082469453268666443981)
                    ·
                      refine ⟨1011405926044975749916493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697082469453268666443981 1011405926044975749916493)
                      ·
                        rfl

theorem cell23_1969706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1969706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969706 prefixEnd_1969706 := by exact prefixLift 1969706
  have htrace : WordTrace (prefixWord ++ tailWord_1969706) baseStart_1969706 baseEnd_1969706 := by
    simpa [prefixWord, tailWord_1969706, baseEnd_1969706] using wordTrace_append hprefix tailTrace_1969706
  have hstable : (prefixWord ++ tailWord_1969706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969706).length < 2 ^ (prefixWord ++ tailWord_1969706).sum := by decide
  have hdescent : baseEnd_1969706 < baseStart_1969706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969710 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_1969710 : Nat := 118140960795 + 1969710 * 2 ^ 59
def prefixEnd_1969710 : Nat := 4983230072969 + 3 ^ 40 * 1969710 * 2
def baseEnd_1969710 : Nat := 1011407979967593734266475

theorem tailTrace_1969710 : CollatzResearch.WordTrace tailWord_1969710 prefixEnd_1969710 1011407979967593734266475 := by
  unfold tailWord_1969710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8980153211760568066370323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47894150462723029687308389 8980153211760568066370323)
  ·
    refine ⟨13470229817640852099555485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8980153211760568066370323 13470229817640852099555485)
    ·
      refine ⟨5051336181615319537333307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13470229817640852099555485 5051336181615319537333307)
      ·
        refine ⟨7577004272422979305999961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5051336181615319537333307 7577004272422979305999961)
        ·
          refine ⟨5682753204317234479499971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7577004272422979305999961 5682753204317234479499971)
          ·
            refine ⟨8524129806475851719249957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5682753204317234479499971 8524129806475851719249957)
            ·
              refine ⟨1598274338714222197359367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8524129806475851719249957 1598274338714222197359367)
              ·
                refine ⟨2397411508071333296039051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598274338714222197359367 2397411508071333296039051)
                ·
                  refine ⟨3596117262106999944058577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397411508071333296039051 3596117262106999944058577)
                  ·
                    refine ⟨2697087946580249958043933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3596117262106999944058577 2697087946580249958043933)
                    ·
                      refine ⟨1011407979967593734266475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697087946580249958043933 1011407979967593734266475)
                      ·
                        rfl

theorem cell23_1969710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_1969710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969710 prefixEnd_1969710 := by exact prefixLift 1969710
  have htrace : WordTrace (prefixWord ++ tailWord_1969710) baseStart_1969710 baseEnd_1969710 := by
    simpa [prefixWord, tailWord_1969710, baseEnd_1969710] using wordTrace_append hprefix tailTrace_1969710
  have hstable : (prefixWord ++ tailWord_1969710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969710).length < 2 ^ (prefixWord ++ tailWord_1969710).sum := by decide
  have hdescent : baseEnd_1969710 < baseStart_1969710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969740 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 2, 1, 3]
def baseStart_1969740 : Nat := 118140960795 + 1969740 * 2 ^ 59
def prefixEnd_1969740 : Nat := 4983230072969 + 3 ^ 40 * 1969740 * 2
def baseEnd_1969740 : Nat := 1011423384387228616891337

theorem tailTrace_1969740 : CollatzResearch.WordTrace tailWord_1969740 prefixEnd_1969740 1011423384387228616891337 := by
  unfold tailWord_1969740
  simp only [CollatzResearch.WordTrace]
  refine ⟨35921159941987929827277337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47894879922650573103036449 35921159941987929827277337)
  ·
    refine ⟨26940869956490947370458003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35921159941987929827277337 26940869956490947370458003)
    ·
      refine ⟨40411304934736421055687005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26940869956490947370458003 40411304934736421055687005)
      ·
        refine ⟨15154239350526157895882627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40411304934736421055687005 15154239350526157895882627)
        ·
          refine ⟨22731359025789236843823941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15154239350526157895882627 22731359025789236843823941)
          ·
            refine ⟨4262129817335481908216989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22731359025789236843823941 4262129817335481908216989)
            ·
              refine ⟨1598298681500805715581371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4262129817335481908216989 1598298681500805715581371)
              ·
                refine ⟨2397448022251208573372057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598298681500805715581371 2397448022251208573372057)
                ·
                  refine ⟨1798086016688406430029043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2397448022251208573372057 1798086016688406430029043)
                  ·
                    refine ⟨2697129025032609645043565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1798086016688406430029043 2697129025032609645043565)
                    ·
                      refine ⟨1011423384387228616891337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697129025032609645043565 1011423384387228616891337)
                      ·
                        rfl

theorem cell23_1969740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_1969740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969740 prefixEnd_1969740 := by exact prefixLift 1969740
  have htrace : WordTrace (prefixWord ++ tailWord_1969740) baseStart_1969740 baseEnd_1969740 := by
    simpa [prefixWord, tailWord_1969740, baseEnd_1969740] using wordTrace_append hprefix tailTrace_1969740
  have hstable : (prefixWord ++ tailWord_1969740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969740).length < 2 ^ (prefixWord ++ tailWord_1969740).sum := by decide
  have hdescent : baseEnd_1969740 < baseStart_1969740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969749 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1969749 : Nat := 118140960795 + 1969749 * 2 ^ 59
def prefixEnd_1969749 : Nat := 4983230072969 + 3 ^ 40 * 1969749 * 2
def baseEnd_1969749 : Nat := 1011428005713119081678795

theorem tailTrace_1969749 : CollatzResearch.WordTrace tailWord_1969749 prefixEnd_1969749 1011428005713119081678795 := by
  unfold tailWord_1969749
  simp only [CollatzResearch.WordTrace]
  refine ⟨71842648140943254191632301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47895098760628836127754867 71842648140943254191632301)
  ·
    refine ⟨26940993052853720321862113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71842648140943254191632301 26940993052853720321862113)
    ·
      refine ⟨20205744789640290241396585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26940993052853720321862113 20205744789640290241396585)
      ·
        refine ⟨15154308592230217681047439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20205744789640290241396585 15154308592230217681047439)
        ·
          refine ⟨22731462888345326521571159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15154308592230217681047439 22731462888345326521571159)
          ·
            refine ⟨34097194332517989782356739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22731462888345326521571159 34097194332517989782356739)
            ·
              refine ⟨51145791498776984673535109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34097194332517989782356739 51145791498776984673535109)
              ·
                refine ⟨9589835906020684626287833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51145791498776984673535109 9589835906020684626287833)
                ·
                  refine ⟨7192376929515513469715875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9589835906020684626287833 7192376929515513469715875)
                  ·
                    refine ⟨10788565394273270204573813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7192376929515513469715875 10788565394273270204573813)
                    ·
                      refine ⟨1011428005713119081678795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10788565394273270204573813 1011428005713119081678795)
                      ·
                        rfl

theorem cell23_1969749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1969749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969749 prefixEnd_1969749 := by exact prefixLift 1969749
  have htrace : WordTrace (prefixWord ++ tailWord_1969749) baseStart_1969749 baseEnd_1969749 := by
    simpa [prefixWord, tailWord_1969749, baseEnd_1969749] using wordTrace_append hprefix tailTrace_1969749
  have hstable : (prefixWord ++ tailWord_1969749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969749).length < 2 ^ (prefixWord ++ tailWord_1969749).sum := by decide
  have hdescent : baseEnd_1969749 < baseStart_1969749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969763 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 4, 2, 2]
def baseStart_1969763 : Nat := 118140960795 + 1969763 * 2 ^ 59
def prefixEnd_1969763 : Nat := 4983230072969 + 3 ^ 40 * 1969763 * 2
def baseEnd_1969763 : Nat := 1011435194442282026903731

theorem tailTrace_1969763 : CollatzResearch.WordTrace tailWord_1969763 prefixEnd_1969763 1011435194442282026903731 := by
  unfold tailWord_1969763
  simp only [CollatzResearch.WordTrace]
  refine ⟨71843158762892534582641943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47895439175261689721761295 71843158762892534582641943)
  ·
    refine ⟨107764738144338801873962915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71843158762892534582641943 107764738144338801873962915)
    ·
      refine ⟨161647107216508202810944373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107764738144338801873962915 161647107216508202810944373)
      ·
        refine ⟨15154416301547644013526035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161647107216508202810944373 15154416301547644013526035)
        ·
          refine ⟨22731624452321466020289053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15154416301547644013526035 22731624452321466020289053)
          ·
            refine ⟨8524359169620549757608395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22731624452321466020289053 8524359169620549757608395)
            ·
              refine ⟨12786538754430824636412593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524359169620549757608395 12786538754430824636412593)
              ·
                refine ⟨9589904065823118477309445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12786538754430824636412593 9589904065823118477309445)
                ·
                  refine ⟨1798107012341834714495521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9589904065823118477309445 1798107012341834714495521)
                  ·
                    refine ⟨1348580259256376035871641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1798107012341834714495521 1348580259256376035871641)
                    ·
                      refine ⟨1011435194442282026903731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348580259256376035871641 1011435194442282026903731)
                      ·
                        rfl

theorem cell23_1969763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_1969763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969763 prefixEnd_1969763 := by exact prefixLift 1969763
  have htrace : WordTrace (prefixWord ++ tailWord_1969763) baseStart_1969763 baseEnd_1969763 := by
    simpa [prefixWord, tailWord_1969763, baseEnd_1969763] using wordTrace_append hprefix tailTrace_1969763
  have hstable : (prefixWord ++ tailWord_1969763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969763).length < 2 ^ (prefixWord ++ tailWord_1969763).sum := by decide
  have hdescent : baseEnd_1969763 < baseStart_1969763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969816 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 2, 5]
def baseStart_1969816 : Nat := 118140960795 + 1969816 * 2 ^ 59
def prefixEnd_1969816 : Nat := 4983230072969 + 3 ^ 40 * 1969816 * 2
def baseEnd_1969816 : Nat := 337154136305656773180329

theorem tailTrace_1969816 : CollatzResearch.WordTrace tailWord_1969816 prefixEnd_1969816 337154136305656773180329 := by
  unfold tailWord_1969816
  simp only [CollatzResearch.WordTrace]
  refine ⟨35922545915850262317160651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47896727887800349756214201 35922545915850262317160651)
  ·
    refine ⟨53883818873775393475740977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35922545915850262317160651 53883818873775393475740977)
    ·
      refine ⟨40412864155331545106805733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53883818873775393475740977 40412864155331545106805733)
      ·
        refine ⟨7577412029124664707526075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40412864155331545106805733 7577412029124664707526075)
        ·
          refine ⟨11366118043686997061289113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7577412029124664707526075 11366118043686997061289113)
          ·
            refine ⟨8524588532765247795966835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11366118043686997061289113 8524588532765247795966835)
            ·
              refine ⟨12786882799147871693950253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524588532765247795966835 12786882799147871693950253)
              ·
                refine ⟨4795081049680451885231345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12786882799147871693950253 4795081049680451885231345)
                ·
                  refine ⟨3596310787260338913923509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4795081049680451885231345 3596310787260338913923509)
                  ·
                    refine ⟨337154136305656773180329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3596310787260338913923509 337154136305656773180329)
                    ·
                      rfl

theorem cell23_1969816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_1969816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969816 prefixEnd_1969816 := by exact prefixLift 1969816
  have htrace : WordTrace (prefixWord ++ tailWord_1969816) baseStart_1969816 baseEnd_1969816 := by
    simpa [prefixWord, tailWord_1969816, baseEnd_1969816] using wordTrace_append hprefix tailTrace_1969816
  have hstable : (prefixWord ++ tailWord_1969816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969816).length < 2 ^ (prefixWord ++ tailWord_1969816).sum := by decide
  have hdescent : baseEnd_1969816 < baseStart_1969816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969836 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 5, 6, 2]
def baseStart_1969836 : Nat := 118140960795 + 1969836 * 2 ^ 59
def prefixEnd_1969836 : Nat := 4983230072969 + 3 ^ 40 * 1969836 * 2
def baseEnd_1969836 : Nat := 1011472678530060241290895

theorem tailTrace_1969836 : CollatzResearch.WordTrace tailWord_1969836 prefixEnd_1969836 1011472678530060241290895 := by
  unfold tailWord_1969836
  simp only [CollatzResearch.WordTrace]
  refine ⟨35922910645814034025024681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47897214194418712033366241 35922910645814034025024681)
  ·
    refine ⟨26942182984360525518768511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35922910645814034025024681 26942182984360525518768511)
    ·
      refine ⟨40413274476540788278152767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26942182984360525518768511 40413274476540788278152767)
      ·
        refine ⟨60619911714811182417229151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40413274476540788278152767 60619911714811182417229151)
        ·
          refine ⟨90929867572216773625843727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60619911714811182417229151 90929867572216773625843727)
          ·
            refine ⟨136394801358325160438765591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90929867572216773625843727 136394801358325160438765591)
            ·
              refine ⟨204592202037487740658148387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136394801358325160438765591 204592202037487740658148387)
              ·
                refine ⟨306888303056231610987222581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204592202037487740658148387 306888303056231610987222581)
                ·
                  refine ⟨28770778411521713530052117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306888303056231610987222581 28770778411521713530052117)
                  ·
                    refine ⟨1348630238040080321721193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28770778411521713530052117 1348630238040080321721193)
                    ·
                      refine ⟨1011472678530060241290895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348630238040080321721193 1011472678530060241290895)
                      ·
                        rfl

theorem cell23_1969836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_1969836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969836 prefixEnd_1969836 := by exact prefixLift 1969836
  have htrace : WordTrace (prefixWord ++ tailWord_1969836) baseStart_1969836 baseEnd_1969836 := by
    simpa [prefixWord, tailWord_1969836, baseEnd_1969836] using wordTrace_append hprefix tailTrace_1969836
  have hstable : (prefixWord ++ tailWord_1969836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969836).length < 2 ^ (prefixWord ++ tailWord_1969836).sum := by decide
  have hdescent : baseEnd_1969836 < baseStart_1969836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969839 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_1969839 : Nat := 118140960795 + 1969839 * 2 ^ 59
def prefixEnd_1969839 : Nat := 4983230072969 + 3 ^ 40 * 1969839 * 2
def baseEnd_1969839 : Nat := 1011474218972023729553381

theorem tailTrace_1969839 : CollatzResearch.WordTrace tailWord_1969839 prefixEnd_1969839 1011474218972023729553381 := by
  unfold tailWord_1969839
  simp only [CollatzResearch.WordTrace]
  refine ⟨71845930710617199562408571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47897287140411466374939047 71845930710617199562408571)
  ·
    refine ⟨107768896065925799343612857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71845930710617199562408571 107768896065925799343612857)
    ·
      refine ⟨80826672049444349507709643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107768896065925799343612857 80826672049444349507709643)
      ·
        refine ⟨121240008074166524261564465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80826672049444349507709643 121240008074166524261564465)
        ·
          refine ⟨90930006055624893196173349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121240008074166524261564465 90930006055624893196173349)
          ·
            refine ⟨17049376135429667474282503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90930006055624893196173349 17049376135429667474282503)
            ·
              refine ⟨25574064203144501211423755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17049376135429667474282503 25574064203144501211423755)
              ·
                refine ⟨38361096304716751817135633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25574064203144501211423755 38361096304716751817135633)
                ·
                  refine ⟨28770822228537563862851725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38361096304716751817135633 28770822228537563862851725)
                  ·
                    refine ⟨10789058335701586448569397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28770822228537563862851725 10789058335701586448569397)
                    ·
                      refine ⟨1011474218972023729553381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10789058335701586448569397 1011474218972023729553381)
                      ·
                        rfl

theorem cell23_1969839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_1969839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969839 prefixEnd_1969839 := by exact prefixLift 1969839
  have htrace : WordTrace (prefixWord ++ tailWord_1969839) baseStart_1969839 baseEnd_1969839 := by
    simpa [prefixWord, tailWord_1969839, baseEnd_1969839] using wordTrace_append hprefix tailTrace_1969839
  have hstable : (prefixWord ++ tailWord_1969839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969839).length < 2 ^ (prefixWord ++ tailWord_1969839).sum := by decide
  have hdescent : baseEnd_1969839 < baseStart_1969839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969853 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_1969853 : Nat := 118140960795 + 1969853 * 2 ^ 59
def prefixEnd_1969853 : Nat := 4983230072969 + 3 ^ 40 * 1969853 * 2
def baseEnd_1969853 : Nat := 1011481407701186674778317

theorem tailTrace_1969853 : CollatzResearch.WordTrace tailWord_1969853 prefixEnd_1969853 1011481407701186674778317 := by
  unfold tailWord_1969853
  simp only [CollatzResearch.WordTrace]
  refine ⟨71846441332566479953418213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47897627555044319968945475 71846441332566479953418213)
  ·
    refine ⟨13471207749856214991265915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71846441332566479953418213 13471207749856214991265915)
    ·
      refine ⟨20206811624784322486898873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13471207749856214991265915 20206811624784322486898873)
      ·
        refine ⟨15155108718588241865174155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20206811624784322486898873 15155108718588241865174155)
        ·
          refine ⟨22732663077882362797761233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15155108718588241865174155 22732663077882362797761233)
          ·
            refine ⟨17049497308411772098320925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22732663077882362797761233 17049497308411772098320925)
            ·
              refine ⟨6393561490654414536870347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17049497308411772098320925 6393561490654414536870347)
              ·
                refine ⟨9590342235981621805305521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6393561490654414536870347 9590342235981621805305521)
                ·
                  refine ⟨7192756676986216353979141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9590342235981621805305521 7192756676986216353979141)
                  ·
                    refine ⟨1348641876934915566371089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7192756676986216353979141 1348641876934915566371089)
                    ·
                      refine ⟨1011481407701186674778317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348641876934915566371089 1011481407701186674778317)
                      ·
                        rfl

theorem cell23_1969853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_1969853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969853 prefixEnd_1969853 := by exact prefixLift 1969853
  have htrace : WordTrace (prefixWord ++ tailWord_1969853) baseStart_1969853 baseEnd_1969853 := by
    simpa [prefixWord, tailWord_1969853, baseEnd_1969853] using wordTrace_append hprefix tailTrace_1969853
  have hstable : (prefixWord ++ tailWord_1969853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969853).length < 2 ^ (prefixWord ++ tailWord_1969853).sum := by decide
  have hdescent : baseEnd_1969853 < baseStart_1969853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969856 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 3]
def baseStart_1969856 : Nat := 118140960795 + 1969856 * 2 ^ 59
def prefixEnd_1969856 : Nat := 4983230072969 + 3 ^ 40 * 1969856 * 2
def baseEnd_1969856 : Nat := 1011482948143150163040803

theorem tailTrace_1969856 : CollatzResearch.WordTrace tailWord_1969856 prefixEnd_1969856 1011482948143150163040803 := by
  unfold tailWord_1969856
  simp only [CollatzResearch.WordTrace]
  refine ⟨35923275375777805732888711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47897700501037074310518281 35923275375777805732888711)
  ·
    refine ⟨53884913063666708599333067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35923275375777805732888711 53884913063666708599333067)
    ·
      refine ⟨80827369595500062898999601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53884913063666708599333067 80827369595500062898999601)
      ·
        refine ⟨60620527196625047174249701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80827369595500062898999601 60620527196625047174249701)
        ·
          refine ⟨11366348849367196345171819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60620527196625047174249701 11366348849367196345171819)
          ·
            refine ⟨17049523274050794517757729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11366348849367196345171819 17049523274050794517757729)
            ·
              refine ⟨12787142455538095888318297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17049523274050794517757729 12787142455538095888318297)
              ·
                refine ⟨9590356841653571916238723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12787142455538095888318297 9590356841653571916238723)
                ·
                  refine ⟨14385535262480357874358085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590356841653571916238723 14385535262480357874358085)
                  ·
                    refine ⟨2697287861715067101442141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14385535262480357874358085 2697287861715067101442141)
                    ·
                      refine ⟨1011482948143150163040803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697287861715067101442141 1011482948143150163040803)
                      ·
                        rfl

theorem cell23_1969856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_1969856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969856 prefixEnd_1969856 := by exact prefixLift 1969856
  have htrace : WordTrace (prefixWord ++ tailWord_1969856) baseStart_1969856 baseEnd_1969856 := by
    simpa [prefixWord, tailWord_1969856, baseEnd_1969856] using wordTrace_append hprefix tailTrace_1969856
  have hstable : (prefixWord ++ tailWord_1969856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969856).length < 2 ^ (prefixWord ++ tailWord_1969856).sum := by decide
  have hdescent : baseEnd_1969856 < baseStart_1969856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969873 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_1969873 : Nat := 118140960795 + 1969873 * 2 ^ 59
def prefixEnd_1969873 : Nat := 4983230072969 + 3 ^ 40 * 1969873 * 2
def baseEnd_1969873 : Nat := 1011491677314276596528225

theorem tailTrace_1969873 : CollatzResearch.WordTrace tailWord_1969873 prefixEnd_1969873 1011491677314276596528225 := by
  unfold tailWord_1969873
  simp only [CollatzResearch.WordTrace]
  refine ⟨71847170792494023369146273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47898113861662682246097515 71847170792494023369146273)
  ·
    refine ⟨53885378094370517526859705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71847170792494023369146273 53885378094370517526859705)
    ·
      refine ⟨40414033570777888145144779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53885378094370517526859705 40414033570777888145144779)
      ·
        refine ⟨60621050356166832217717169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40414033570777888145144779 60621050356166832217717169)
        ·
          refine ⟨45465787767125124163287877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60621050356166832217717169 45465787767125124163287877)
          ·
            refine ⟨8524835206335960780616477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45465787767125124163287877 8524835206335960780616477)
            ·
              refine ⟨3196813202375985292731179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8524835206335960780616477 3196813202375985292731179)
              ·
                refine ⟨4795219803563977939096769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196813202375985292731179 4795219803563977939096769)
                ·
                  refine ⟨3596414852672983454322577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4795219803563977939096769 3596414852672983454322577)
                  ·
                    refine ⟨2697311139504737590741933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3596414852672983454322577 2697311139504737590741933)
                    ·
                      refine ⟨1011491677314276596528225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697311139504737590741933 1011491677314276596528225)
                      ·
                        rfl

theorem cell23_1969873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_1969873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969873 prefixEnd_1969873 := by exact prefixLift 1969873
  have htrace : WordTrace (prefixWord ++ tailWord_1969873) baseStart_1969873 baseEnd_1969873 := by
    simpa [prefixWord, tailWord_1969873, baseEnd_1969873] using wordTrace_append hprefix tailTrace_1969873
  have hstable : (prefixWord ++ tailWord_1969873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969873).length < 2 ^ (prefixWord ++ tailWord_1969873).sum := by decide
  have hdescent : baseEnd_1969873 < baseStart_1969873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969880 : List Nat := [2, 1, 2, 2, 3, 1, 4, 3, 1, 4]
def baseStart_1969880 : Nat := 118140960795 + 1969880 * 2 ^ 59
def prefixEnd_1969880 : Nat := 4983230072969 + 3 ^ 40 * 1969880 * 2
def baseEnd_1969880 : Nat := 337165090559619356380231

theorem tailTrace_1969880 : CollatzResearch.WordTrace tailWord_1969880 prefixEnd_1969880 337165090559619356380231 := by
  unfold tailWord_1969880
  simp only [CollatzResearch.WordTrace]
  refine ⟨35923713051734331782325547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47898284068979109043100729 35923713051734331782325547)
  ·
    refine ⟨53885569577601497673488321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35923713051734331782325547 53885569577601497673488321)
    ·
      refine ⟨40414177183201123255116241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53885569577601497673488321 40414177183201123255116241)
      ·
        refine ⟨30310632887400842441337181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40414177183201123255116241 30310632887400842441337181)
        ·
          refine ⟨11366487332775315915501443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30310632887400842441337181 11366487332775315915501443)
          ·
            refine ⟨17049730999162973873252165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11366487332775315915501443 17049730999162973873252165)
            ·
              refine ⟨3196824562343057601234781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17049730999162973873252165 3196824562343057601234781)
              ·
                refine ⟨1198809210878646600463043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3196824562343057601234781 1198809210878646600463043)
                ·
                  refine ⟨1798213816317969900694565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198809210878646600463043 1798213816317969900694565)
                  ·
                    refine ⟨337165090559619356380231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1798213816317969900694565 337165090559619356380231)
                    ·
                      rfl

theorem cell23_1969880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_1969880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969880 prefixEnd_1969880 := by exact prefixLift 1969880
  have htrace : WordTrace (prefixWord ++ tailWord_1969880) baseStart_1969880 baseEnd_1969880 := by
    simpa [prefixWord, tailWord_1969880, baseEnd_1969880] using wordTrace_append hprefix tailTrace_1969880
  have hstable : (prefixWord ++ tailWord_1969880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969880).length < 2 ^ (prefixWord ++ tailWord_1969880).sum := by decide
  have hdescent : baseEnd_1969880 < baseStart_1969880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969896 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1969896 : Nat := 118140960795 + 1969896 * 2 ^ 59
def prefixEnd_1969896 : Nat := 4983230072969 + 3 ^ 40 * 1969896 * 2
def baseEnd_1969896 : Nat := 1011503487369330006540619

theorem tailTrace_1969896 : CollatzResearch.WordTrace tailWord_1969896 prefixEnd_1969896 1011503487369330006540619 := by
  unfold tailWord_1969896
  simp only [CollatzResearch.WordTrace]
  refine ⟨35924004835705349148616771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47898673114273798864822361 35924004835705349148616771)
  ·
    refine ⟨53886007253558023722925157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35924004835705349148616771 53886007253558023722925157)
    ·
      refine ⟨10103626360042129448048467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53886007253558023722925157 10103626360042129448048467)
      ·
        refine ⟨15155439540063194172072701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103626360042129448048467 15155439540063194172072701)
        ·
          refine ⟨5683289827523697814527263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15155439540063194172072701 5683289827523697814527263)
          ·
            refine ⟨8524934741285546721790895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5683289827523697814527263 8524934741285546721790895)
            ·
              refine ⟨12787402111928320082686343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524934741285546721790895 12787402111928320082686343)
              ·
                refine ⟨19181103167892480124029515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12787402111928320082686343 19181103167892480124029515)
                ·
                  refine ⟨28771654751838720186044273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19181103167892480124029515 28771654751838720186044273)
                  ·
                    refine ⟨21578741063879040139533205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28771654751838720186044273 21578741063879040139533205)
                    ·
                      refine ⟨1011503487369330006540619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21578741063879040139533205 1011503487369330006540619)
                      ·
                        rfl

theorem cell23_1969896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1969896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969896 prefixEnd_1969896 := by exact prefixLift 1969896
  have htrace : WordTrace (prefixWord ++ tailWord_1969896) baseStart_1969896 baseEnd_1969896 := by
    simpa [prefixWord, tailWord_1969896, baseEnd_1969896] using wordTrace_append hprefix tailTrace_1969896
  have hstable : (prefixWord ++ tailWord_1969896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969896).length < 2 ^ (prefixWord ++ tailWord_1969896).sum := by decide
  have hdescent : baseEnd_1969896 < baseStart_1969896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969910 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_1969910 : Nat := 118140960795 + 1969910 * 2 ^ 59
def prefixEnd_1969910 : Nat := 4983230072969 + 3 ^ 40 * 1969910 * 2
def baseEnd_1969910 : Nat := 112390075122054772418395

theorem tailTrace_1969910 : CollatzResearch.WordTrace tailWord_1969910 prefixEnd_1969910 112390075122054772418395 := by
  unfold tailWord_1969910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490532518334998668015199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47899013528906652458828789 4490532518334998668015199)
  ·
    refine ⟨6735798777502498002022799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4490532518334998668015199 6735798777502498002022799)
    ·
      refine ⟨10103698166253747003034199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6735798777502498002022799 10103698166253747003034199)
      ·
        refine ⟨15155547249380620504551299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103698166253747003034199 15155547249380620504551299)
        ·
          refine ⟨22733320874070930756826949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15155547249380620504551299 22733320874070930756826949)
          ·
            refine ⟨4262497663888299516905053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22733320874070930756826949 4262497663888299516905053)
            ·
              refine ⟨1598436623958112318839395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4262497663888299516905053 1598436623958112318839395)
              ·
                refine ⟨2397654935937168478259093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598436623958112318839395 2397654935937168478259093)
                ·
                  refine ⟨112390075122054772418395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2397654935937168478259093 112390075122054772418395)
                  ·
                    rfl

theorem cell23_1969910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_1969910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969910 prefixEnd_1969910 := by exact prefixLift 1969910
  have htrace : WordTrace (prefixWord ++ tailWord_1969910) baseStart_1969910 baseEnd_1969910 := by
    simpa [prefixWord, tailWord_1969910, baseEnd_1969910] using wordTrace_append hprefix tailTrace_1969910
  have hstable : (prefixWord ++ tailWord_1969910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969910).length < 2 ^ (prefixWord ++ tailWord_1969910).sum := by decide
  have hdescent : baseEnd_1969910 < baseStart_1969910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969953 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 4, 4]
def baseStart_1969953 : Nat := 118140960795 + 1969953 * 2 ^ 59
def prefixEnd_1969953 : Nat := 4983230072969 + 3 ^ 40 * 1969953 * 2
def baseEnd_1969953 : Nat := 337177585255545427842619

theorem tailTrace_1969953 : CollatzResearch.WordTrace tailWord_1969953 prefixEnd_1969953 337177585255545427842619 := by
  unfold tailWord_1969953
  simp only [CollatzResearch.WordTrace]
  refine ⟨71850088632204197032058513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47900059088136131354705675 71850088632204197032058513)
  ·
    refine ⟨53887566474153147774043885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71850088632204197032058513 53887566474153147774043885)
    ·
      refine ⟨20207837427807430415266457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53887566474153147774043885 20207837427807430415266457)
      ·
        refine ⟨15155878070855572811449843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20207837427807430415266457 15155878070855572811449843)
        ·
          refine ⟨22733817106283359217174765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15155878070855572811449843 22733817106283359217174765)
          ·
            refine ⟨8525181414856259706440537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22733817106283359217174765 8525181414856259706440537)
            ·
              refine ⟨6393886061142194779830403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8525181414856259706440537 6393886061142194779830403)
              ·
                refine ⟨9590829091713292169745605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6393886061142194779830403 9590829091713292169745605)
                ·
                  refine ⟨1798280454696242281827301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9590829091713292169745605 1798280454696242281827301)
                  ·
                    refine ⟨337177585255545427842619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1798280454696242281827301 337177585255545427842619)
                    ·
                      rfl

theorem cell23_1969953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_1969953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969953 prefixEnd_1969953 := by exact prefixLift 1969953
  have htrace : WordTrace (prefixWord ++ tailWord_1969953) baseStart_1969953 baseEnd_1969953 := by
    simpa [prefixWord, tailWord_1969953, baseEnd_1969953] using wordTrace_append hprefix tailTrace_1969953
  have hstable : (prefixWord ++ tailWord_1969953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969953).length < 2 ^ (prefixWord ++ tailWord_1969953).sum := by decide
  have hdescent : baseEnd_1969953 < baseStart_1969953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969954 : List Nat := [3, 3, 1, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_1969954 : Nat := 118140960795 + 1969954 * 2 ^ 59
def prefixEnd_1969954 : Nat := 4983230072969 + 3 ^ 40 * 1969954 * 2
def baseEnd_1969954 : Nat := 1011533269247290779615353

theorem tailTrace_1969954 : CollatzResearch.WordTrace tailWord_1969954 prefixEnd_1969954 1011533269247290779615353 := by
  unfold tailWord_1969954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17962531276300143550711229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47900083403467049468563277 17962531276300143550711229)
  ·
    refine ⟨6735949228612553831516711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17962531276300143550711229 6735949228612553831516711)
    ·
      refine ⟨10103923842918830747275067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6735949228612553831516711 10103923842918830747275067)
      ·
        refine ⟨15155885764378246120912601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103923842918830747275067 15155885764378246120912601)
        ·
          refine ⟨11366914323283684590684451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15155885764378246120912601 11366914323283684590684451)
          ·
            refine ⟨17050371484925526886026677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11366914323283684590684451 17050371484925526886026677)
            ·
              refine ⟨1598472326711768145565001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17050371484925526886026677 1598472326711768145565001)
              ·
                refine ⟨1198854245033826109173751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598472326711768145565001 1198854245033826109173751)
                ·
                  refine ⟨1798281367550739163760627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198854245033826109173751 1798281367550739163760627)
                  ·
                    refine ⟨2697422051326108745640941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1798281367550739163760627 2697422051326108745640941)
                    ·
                      refine ⟨1011533269247290779615353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697422051326108745640941 1011533269247290779615353)
                      ·
                        rfl

theorem cell23_1969954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_1969954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969954 prefixEnd_1969954 := by exact prefixLift 1969954
  have htrace : WordTrace (prefixWord ++ tailWord_1969954) baseStart_1969954 baseEnd_1969954 := by
    simpa [prefixWord, tailWord_1969954, baseEnd_1969954] using wordTrace_append hprefix tailTrace_1969954
  have hstable : (prefixWord ++ tailWord_1969954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969954).length < 2 ^ (prefixWord ++ tailWord_1969954).sum := by decide
  have hdescent : baseEnd_1969954 < baseStart_1969954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969970 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_1969970 : Nat := 118140960795 + 1969970 * 2 ^ 59
def prefixEnd_1969970 : Nat := 4983230072969 + 3 ^ 40 * 1969970 * 2
def baseEnd_1969970 : Nat := 337180494979254239005093

theorem tailTrace_1969970 : CollatzResearch.WordTrace tailWord_1969970 prefixEnd_1969970 337180494979254239005093 := by
  unfold tailWord_1969970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17962677168285652233856841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47900472448761739290284909 17962677168285652233856841)
  ·
    refine ⟨13472007876214239175392631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17962677168285652233856841 13472007876214239175392631)
    ·
      refine ⟨20208011814321358763088947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13472007876214239175392631 20208011814321358763088947)
      ·
        refine ⟨30312017721482038144633421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20208011814321358763088947 30312017721482038144633421)
        ·
          refine ⟨11367006645555764304237533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30312017721482038144633421 11367006645555764304237533)
          ·
            refine ⟨4262627492083411614089075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11367006645555764304237533 4262627492083411614089075)
            ·
              refine ⟨6393941238125117421133613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262627492083411614089075 6393941238125117421133613)
              ·
                refine ⟨2397727964296919032925105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6393941238125117421133613 2397727964296919032925105)
                ·
                  refine ⟨1798295973222689274693829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2397727964296919032925105 1798295973222689274693829)
                  ·
                    refine ⟨337180494979254239005093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1798295973222689274693829 337180494979254239005093)
                    ·
                      rfl

theorem cell23_1969970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_1969970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969970 prefixEnd_1969970 := by exact prefixLift 1969970
  have htrace : WordTrace (prefixWord ++ tailWord_1969970) baseStart_1969970 baseEnd_1969970 := by
    simpa [prefixWord, tailWord_1969970, baseEnd_1969970] using wordTrace_append hprefix tailTrace_1969970
  have hstable : (prefixWord ++ tailWord_1969970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969970).length < 2 ^ (prefixWord ++ tailWord_1969970).sum := by decide
  have hdescent : baseEnd_1969970 < baseStart_1969970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969980 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1969980 : Nat := 118140960795 + 1969980 * 2 ^ 59
def prefixEnd_1969980 : Nat := 4983230072969 + 3 ^ 40 * 1969980 * 2
def baseEnd_1969980 : Nat := 1011546619744307677890233

theorem tailTrace_1969980 : CollatzResearch.WordTrace tailWord_1969980 prefixEnd_1969980 1011546619744307677890233 := by
  unfold tailWord_1969980
  simp only [CollatzResearch.WordTrace]
  refine ⟨35925536701553190321645697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47900715602070920428860929 35925536701553190321645697)
  ·
    refine ⟨26944152526164892741234273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35925536701553190321645697 26944152526164892741234273)
    ·
      refine ⟨20208114394623669555925705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26944152526164892741234273 20208114394623669555925705)
      ·
        refine ⟨15156085795967752166944279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20208114394623669555925705 15156085795967752166944279)
        ·
          refine ⟨22734128693951628250416419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15156085795967752166944279 22734128693951628250416419)
          ·
            refine ⟨34101193040927442375624629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22734128693951628250416419 34101193040927442375624629)
            ·
              refine ⟨3196986847586947722714809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34101193040927442375624629 3196986847586947722714809)
              ·
                refine ⟨2397740135690210792036107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3196986847586947722714809 2397740135690210792036107)
                ·
                  refine ⟨3596610203535316188054161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397740135690210792036107 3596610203535316188054161)
                  ·
                    refine ⟨2697457652651487141040621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3596610203535316188054161 2697457652651487141040621)
                    ·
                      refine ⟨1011546619744307677890233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697457652651487141040621 1011546619744307677890233)
                      ·
                        rfl

theorem cell23_1969980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1969980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969980 prefixEnd_1969980 := by exact prefixLift 1969980
  have htrace : WordTrace (prefixWord ++ tailWord_1969980) baseStart_1969980 baseEnd_1969980 := by
    simpa [prefixWord, tailWord_1969980, baseEnd_1969980] using wordTrace_append hprefix tailTrace_1969980
  have hstable : (prefixWord ++ tailWord_1969980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969980).length < 2 ^ (prefixWord ++ tailWord_1969980).sum := by decide
  have hdescent : baseEnd_1969980 < baseStart_1969980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969993 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 3]
def baseStart_1969993 : Nat := 118140960795 + 1969993 * 2 ^ 59
def prefixEnd_1969993 : Nat := 4983230072969 + 3 ^ 40 * 1969993 * 2
def baseEnd_1969993 : Nat := 1011553294992816127027673

theorem tailTrace_1969993 : CollatzResearch.WordTrace tailWord_1969993 prefixEnd_1969993 1011553294992816127027673 := by
  unfold tailWord_1969993
  simp only [CollatzResearch.WordTrace]
  refine ⟨71851547552059283863514633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47901031701372855909009755 71851547552059283863514633)
  ·
    refine ⟨53888660664044462897635975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71851547552059283863514633 53888660664044462897635975)
    ·
      refine ⟨80832990996066694346453963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53888660664044462897635975 80832990996066694346453963)
      ·
        refine ⟨121249486494100041519680945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80832990996066694346453963 121249486494100041519680945)
        ·
          refine ⟨90937114870575031139760709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121249486494100041519680945 90937114870575031139760709)
          ·
            refine ⟨17050709038232818338705133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90937114870575031139760709 17050709038232818338705133)
            ·
              refine ⟨6394015889337306877014425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17050709038232818338705133 6394015889337306877014425)
              ·
                refine ⟨4795511917002980157760819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6394015889337306877014425 4795511917002980157760819)
                ·
                  refine ⟨7193267875504470236641229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795511917002980157760819 7193267875504470236641229)
                  ·
                    refine ⟨2697475453314176338740461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7193267875504470236641229 2697475453314176338740461)
                    ·
                      refine ⟨1011553294992816127027673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697475453314176338740461 1011553294992816127027673)
                      ·
                        rfl

theorem cell23_1969993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_1969993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969993 prefixEnd_1969993 := by exact prefixLift 1969993
  have htrace : WordTrace (prefixWord ++ tailWord_1969993) baseStart_1969993 baseEnd_1969993 := by
    simpa [prefixWord, tailWord_1969993, baseEnd_1969993] using wordTrace_append hprefix tailTrace_1969993
  have hstable : (prefixWord ++ tailWord_1969993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969993).length < 2 ^ (prefixWord ++ tailWord_1969993).sum := by decide
  have hdescent : baseEnd_1969993 < baseStart_1969993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969997 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1969997 : Nat := 118140960795 + 1969997 * 2 ^ 59
def prefixEnd_1969997 : Nat := 4983230072969 + 3 ^ 40 * 1969997 * 2
def baseEnd_1969997 : Nat := 1011555348915434111377655

theorem tailTrace_1969997 : CollatzResearch.WordTrace tailWord_1969997 prefixEnd_1969997 1011555348915434111377655 := by
  unfold tailWord_1969997
  simp only [CollatzResearch.WordTrace]
  refine ⟨71851693444044792546660245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47901128962696528364440163 71851693444044792546660245)
  ·
    refine ⟨3368048130189599650624699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71851693444044792546660245 3368048130189599650624699)
    ·
      refine ⟨5052072195284399475937049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3368048130189599650624699 5052072195284399475937049)
      ·
        refine ⟨3789054146463299606952787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5052072195284399475937049 3789054146463299606952787)
        ·
          refine ⟨5683581219694949410429181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789054146463299606952787 5683581219694949410429181)
          ·
            refine ⟨2131342957385606028910943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5683581219694949410429181 2131342957385606028910943)
            ·
              refine ⟨3197014436078409043366415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131342957385606028910943 3197014436078409043366415)
              ·
                refine ⟨4795521654117613565049623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197014436078409043366415 4795521654117613565049623)
                ·
                  refine ⟨7193282481176420347574435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795521654117613565049623 7193282481176420347574435)
                  ·
                    refine ⟨10789923721764630521361653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7193282481176420347574435 10789923721764630521361653)
                    ·
                      refine ⟨1011555348915434111377655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10789923721764630521361653 1011555348915434111377655)
                      ·
                        rfl

theorem cell23_1969997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1969997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1969997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1969997 prefixEnd_1969997 := by exact prefixLift 1969997
  have htrace : WordTrace (prefixWord ++ tailWord_1969997) baseStart_1969997 baseEnd_1969997 := by
    simpa [prefixWord, tailWord_1969997, baseEnd_1969997] using wordTrace_append hprefix tailTrace_1969997
  have hstable : (prefixWord ++ tailWord_1969997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969997).length < 2 ^ (prefixWord ++ tailWord_1969997).sum := by decide
  have hdescent : baseEnd_1969997 < baseStart_1969997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970037 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_1970037 : Nat := 118140960795 + 1970037 * 2 ^ 59
def prefixEnd_1970037 : Nat := 4983230072969 + 3 ^ 40 * 1970037 * 2
def baseEnd_1970037 : Nat := 1011575888141613954877471

theorem tailTrace_1970037 : CollatzResearch.WordTrace tailWord_1970037 prefixEnd_1970037 1011575888141613954877471 := by
  unfold tailWord_1970037
  simp only [CollatzResearch.WordTrace]
  refine ⟨71853152363899879378116365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47902101575933252918744243 71853152363899879378116365)
  ·
    refine ⟨26944932136462454766793637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71853152363899879378116365 26944932136462454766793637)
    ·
      refine ⟨5052174775586710268773807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26944932136462454766793637 5052174775586710268773807)
      ·
        refine ⟨7578262163380065403160711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5052174775586710268773807 7578262163380065403160711)
        ·
          refine ⟨11367393245070098104741067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578262163380065403160711 11367393245070098104741067)
          ·
            refine ⟨17051089867605147157111601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367393245070098104741067 17051089867605147157111601)
            ·
              refine ⟨12788317400703860367833701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17051089867605147157111601 12788317400703860367833701)
              ·
                refine ⟨2397809512631973818968819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12788317400703860367833701 2397809512631973818968819)
                ·
                  refine ⟨3596714268947960728453229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397809512631973818968819 3596714268947960728453229)
                  ·
                    refine ⟨1348767850855485273169961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3596714268947960728453229 1348767850855485273169961)
                    ·
                      refine ⟨1011575888141613954877471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348767850855485273169961 1011575888141613954877471)
                      ·
                        rfl

theorem cell23_1970037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_1970037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970037 prefixEnd_1970037 := by exact prefixLift 1970037
  have htrace : WordTrace (prefixWord ++ tailWord_1970037) baseStart_1970037 baseEnd_1970037 := by
    simpa [prefixWord, tailWord_1970037, baseEnd_1970037] using wordTrace_append hprefix tailTrace_1970037
  have hstable : (prefixWord ++ tailWord_1970037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970037).length < 2 ^ (prefixWord ++ tailWord_1970037).sum := by decide
  have hdescent : baseEnd_1970037 < baseStart_1970037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970078 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1970078 : Nat := 118140960795 + 1970078 * 2 ^ 59
def prefixEnd_1970078 : Nat := 4983230072969 + 3 ^ 40 * 1970078 * 2
def baseEnd_1970078 : Nat := 1011596940848448294464783

theorem tailTrace_1970078 : CollatzResearch.WordTrace tailWord_1970078 prefixEnd_1970078 1011596940848448294464783 := by
  unfold tailWord_1970078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8981830969593917922544861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47903098504500895586905925 8981830969593917922544861)
  ·
    refine ⟨3368186613597719220954323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8981830969593917922544861 3368186613597719220954323)
    ·
      refine ⟨5052279920396578831431485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3368186613597719220954323 5052279920396578831431485)
      ·
        refine ⟨1894604970148717061786807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5052279920396578831431485 1894604970148717061786807)
        ·
          refine ⟨2841907455223075592680211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894604970148717061786807 2841907455223075592680211)
          ·
            refine ⟨4262861182834613389020317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841907455223075592680211 4262861182834613389020317)
            ·
              refine ⟨1598572943562980020882619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4262861182834613389020317 1598572943562980020882619)
              ·
                refine ⟨2397859415344470031323929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598572943562980020882619 2397859415344470031323929)
                ·
                  refine ⟨1798394561508352523492947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2397859415344470031323929 1798394561508352523492947)
                  ·
                    refine ⟨2697591842262528785239421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1798394561508352523492947 2697591842262528785239421)
                    ·
                      refine ⟨1011596940848448294464783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697591842262528785239421 1011596940848448294464783)
                      ·
                        rfl

theorem cell23_1970078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1970078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970078 prefixEnd_1970078 := by exact prefixLift 1970078
  have htrace : WordTrace (prefixWord ++ tailWord_1970078) baseStart_1970078 baseEnd_1970078 := by
    simpa [prefixWord, tailWord_1970078, baseEnd_1970078] using wordTrace_append hprefix tailTrace_1970078
  have hstable : (prefixWord ++ tailWord_1970078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970078).length < 2 ^ (prefixWord ++ tailWord_1970078).sum := by decide
  have hdescent : baseEnd_1970078 < baseStart_1970078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970103 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 2, 5]
def baseStart_1970103 : Nat := 118140960795 + 1970103 * 2 ^ 59
def prefixEnd_1970103 : Nat := 4983230072969 + 3 ^ 40 * 1970103 * 2
def baseEnd_1970103 : Nat := 337203259288270232217389

theorem tailTrace_1970103 : CollatzResearch.WordTrace tailWord_1970103 prefixEnd_1970103 337203259288270232217389 := by
  unfold tailWord_1970103
  simp only [CollatzResearch.WordTrace]
  refine ⟨71855559581660772650018963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47903706387773848433345975 71855559581660772650018963)
  ·
    refine ⟨107783339372491158975028445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71855559581660772650018963 107783339372491158975028445)
    ·
      refine ⟨40418752264684184615635667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107783339372491158975028445 40418752264684184615635667)
      ·
        refine ⟨60628128397026276923453501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40418752264684184615635667 60628128397026276923453501)
        ·
          refine ⟨22735548148884853846295063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60628128397026276923453501 22735548148884853846295063)
          ·
            refine ⟨34103322223327280769442595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22735548148884853846295063 34103322223327280769442595)
            ·
              refine ⟨51154983334990921154163893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34103322223327280769442595 51154983334990921154163893)
              ·
                refine ⟨4795779687655398858202865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51154983334990921154163893 4795779687655398858202865)
                ·
                  refine ⟨3596834765741549143652149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4795779687655398858202865 3596834765741549143652149)
                  ·
                    refine ⟨337203259288270232217389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3596834765741549143652149 337203259288270232217389)
                    ·
                      rfl

theorem cell23_1970103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_1970103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970103 prefixEnd_1970103 := by exact prefixLift 1970103
  have htrace : WordTrace (prefixWord ++ tailWord_1970103) baseStart_1970103 baseEnd_1970103 := by
    simpa [prefixWord, tailWord_1970103, baseEnd_1970103] using wordTrace_append hprefix tailTrace_1970103
  have hstable : (prefixWord ++ tailWord_1970103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970103).length < 2 ^ (prefixWord ++ tailWord_1970103).sum := by decide
  have hdescent : baseEnd_1970103 < baseStart_1970103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970120 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 2, 5]
def baseStart_1970120 : Nat := 118140960795 + 1970120 * 2 ^ 59
def prefixEnd_1970120 : Nat := 4983230072969 + 3 ^ 40 * 1970120 * 2
def baseEnd_1970120 : Nat := 337206169011979043379863

theorem tailTrace_1970120 : CollatzResearch.WordTrace tailWord_1970120 prefixEnd_1970120 337206169011979043379863 := by
  unfold tailWord_1970120
  simp only [CollatzResearch.WordTrace]
  refine ⟨35928089811299592276693907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47904119748399456368925209 35928089811299592276693907)
  ·
    refine ⟨53892134716949388415040861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35928089811299592276693907 53892134716949388415040861)
    ·
      refine ⟨20209550518856020655640323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53892134716949388415040861 20209550518856020655640323)
      ·
        refine ⟨30314325778284030983460485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20209550518856020655640323 30314325778284030983460485)
        ·
          refine ⟨5683936083428255809398841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30314325778284030983460485 5683936083428255809398841)
          ·
            refine ⟨4262952062571191857049131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5683936083428255809398841 4262952062571191857049131)
            ·
              refine ⟨6394428093856787785573697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262952062571191857049131 6394428093856787785573697)
              ·
                refine ⟨4795821070392590839180273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6394428093856787785573697 4795821070392590839180273)
                ·
                  refine ⟨3596865802794443129385205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4795821070392590839180273 3596865802794443129385205)
                  ·
                    refine ⟨337206169011979043379863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3596865802794443129385205 337206169011979043379863)
                    ·
                      rfl

theorem cell23_1970120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_1970120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970120 prefixEnd_1970120 := by exact prefixLift 1970120
  have htrace : WordTrace (prefixWord ++ tailWord_1970120) baseStart_1970120 baseEnd_1970120 := by
    simpa [prefixWord, tailWord_1970120, baseEnd_1970120] using wordTrace_append hprefix tailTrace_1970120
  have hstable : (prefixWord ++ tailWord_1970120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970120).length < 2 ^ (prefixWord ++ tailWord_1970120).sum := by decide
  have hdescent : baseEnd_1970120 < baseStart_1970120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970160 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 3]
def baseStart_1970160 : Nat := 118140960795 + 1970160 * 2 ^ 59
def prefixEnd_1970160 : Nat := 4983230072969 + 3 ^ 40 * 1970160 * 2
def baseEnd_1970160 : Nat := 1011639046262116973639405

theorem tailTrace_1970160 : CollatzResearch.WordTrace tailWord_1970160 prefixEnd_1970160 1011639046262116973639405 := by
  unfold tailWord_1970160
  simp only [CollatzResearch.WordTrace]
  refine ⟨35928819271227135692421967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47905092361636180923229289 35928819271227135692421967)
  ·
    refine ⟨53893228906840703538632951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35928819271227135692421967 53893228906840703538632951)
    ·
      refine ⟨80839843360261055307949427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53893228906840703538632951 80839843360261055307949427)
      ·
        refine ⟨121259765040391582961924141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80839843360261055307949427 121259765040391582961924141)
        ·
          refine ⟨45472411890146843610721553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121259765040391582961924141 45472411890146843610721553)
          ·
            refine ⟨34104308917610132708041165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45472411890146843610721553 34104308917610132708041165)
            ·
              refine ⟨12789115844103799765515437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34104308917610132708041165 12789115844103799765515437)
              ·
                refine ⟨4795918441538924912068289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12789115844103799765515437 4795918441538924912068289)
                ·
                  refine ⟨3596938831154193684051217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4795918441538924912068289 3596938831154193684051217)
                  ·
                    refine ⟨2697704123365645263038413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3596938831154193684051217 2697704123365645263038413)
                    ·
                      refine ⟨1011639046262116973639405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697704123365645263038413 1011639046262116973639405)
                      ·
                        rfl

theorem cell23_1970160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_1970160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970160 prefixEnd_1970160 := by exact prefixLift 1970160
  have htrace : WordTrace (prefixWord ++ tailWord_1970160) baseStart_1970160 baseEnd_1970160 := by
    simpa [prefixWord, tailWord_1970160, baseEnd_1970160] using wordTrace_append hprefix tailTrace_1970160
  have hstable : (prefixWord ++ tailWord_1970160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970160).length < 2 ^ (prefixWord ++ tailWord_1970160).sum := by decide
  have hdescent : baseEnd_1970160 < baseStart_1970160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970207 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 3]
def baseStart_1970207 : Nat := 118140960795 + 1970207 * 2 ^ 59
def prefixEnd_1970207 : Nat := 4983230072969 + 3 ^ 40 * 1970207 * 2
def baseEnd_1970207 : Nat := 1011663179852878289751689

theorem tailTrace_1970207 : CollatzResearch.WordTrace tailWord_1970207 prefixEnd_1970207 1011663179852878289751689 := by
  unfold tailWord_1970207
  simp only [CollatzResearch.WordTrace]
  refine ⟨71859352773283998411804875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47906235182189332274536583 71859352773283998411804875)
  ·
    refine ⟨107789029159925997617707313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71859352773283998411804875 107789029159925997617707313)
    ·
      refine ⟨80841771869944498213280485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107789029159925997617707313 80841771869944498213280485)
      ·
        refine ⟨15157832225614593414990091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80841771869944498213280485 15157832225614593414990091)
        ·
          refine ⟨22736748338421890122485137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15157832225614593414990091 22736748338421890122485137)
          ·
            refine ⟨17052561253816417591863853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22736748338421890122485137 17052561253816417591863853)
            ·
              refine ⟨6394710470181156596948945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17052561253816417591863853 6394710470181156596948945)
              ·
                refine ⟨4796032852635867447711709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6394710470181156596948945 4796032852635867447711709)
                ·
                  refine ⟨1798512319738450292891891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4796032852635867447711709 1798512319738450292891891)
                  ·
                    refine ⟨2697768479607675439337837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1798512319738450292891891 2697768479607675439337837)
                    ·
                      refine ⟨1011663179852878289751689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697768479607675439337837 1011663179852878289751689)
                      ·
                        rfl

theorem cell23_1970207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_1970207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970207 prefixEnd_1970207 := by exact prefixLift 1970207
  have htrace : WordTrace (prefixWord ++ tailWord_1970207) baseStart_1970207 baseEnd_1970207 := by
    simpa [prefixWord, tailWord_1970207, baseEnd_1970207] using wordTrace_append hprefix tailTrace_1970207
  have hstable : (prefixWord ++ tailWord_1970207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970207).length < 2 ^ (prefixWord ++ tailWord_1970207).sum := by decide
  have hdescent : baseEnd_1970207 < baseStart_1970207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970210 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1970210 : Nat := 118140960795 + 1970210 * 2 ^ 59
def prefixEnd_1970210 : Nat := 4983230072969 + 3 ^ 40 * 1970210 * 2
def baseEnd_1970210 : Nat := 337221573431613926004725

theorem tailTrace_1970210 : CollatzResearch.WordTrace tailWord_1970210 prefixEnd_1970210 337221573431613926004725 := by
  unfold tailWord_1970210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17964865548068282481041021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47906308128182086616109389 17964865548068282481041021)
  ·
    refine ⟨6736824580525605930390383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17964865548068282481041021 6736824580525605930390383)
    ·
      refine ⟨10105236870788408895585575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6736824580525605930390383 10105236870788408895585575)
      ·
        refine ⟨15157855306182613343378363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10105236870788408895585575 15157855306182613343378363)
        ·
          refine ⟨22736782959273920015067545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15157855306182613343378363 22736782959273920015067545)
          ·
            refine ⟨17052587219455440011300659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22736782959273920015067545 17052587219455440011300659)
            ·
              refine ⟨25578880829183160016950989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17052587219455440011300659 25578880829183160016950989)
              ·
                refine ⟨9592080310943685006356621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25578880829183160016950989 9592080310943685006356621)
                ·
                  refine ⟨3597030116603881877383733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9592080310943685006356621 3597030116603881877383733)
                  ·
                    refine ⟨337221573431613926004725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3597030116603881877383733 337221573431613926004725)
                    ·
                      rfl

theorem cell23_1970210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1970210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970210 prefixEnd_1970210 := by exact prefixLift 1970210
  have htrace : WordTrace (prefixWord ++ tailWord_1970210) baseStart_1970210 baseEnd_1970210 := by
    simpa [prefixWord, tailWord_1970210, baseEnd_1970210] using wordTrace_append hprefix tailTrace_1970210
  have hstable : (prefixWord ++ tailWord_1970210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970210).length < 2 ^ (prefixWord ++ tailWord_1970210).sum := by decide
  have hdescent : baseEnd_1970210 < baseStart_1970210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970223 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 3, 6]
def baseStart_1970223 : Nat := 118140960795 + 1970223 * 2 ^ 59
def prefixEnd_1970223 : Nat := 4983230072969 + 3 ^ 40 * 1970223 * 2
def baseEnd_1970223 : Nat := 337223798514450075717205

theorem tailTrace_1970223 : CollatzResearch.WordTrace tailWord_1970223 prefixEnd_1970223 337223798514450075717205 := by
  unfold tailWord_1970223
  simp only [CollatzResearch.WordTrace]
  refine ⟨71859936341226033144387323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47906624227484022096258215 71859936341226033144387323)
  ·
    refine ⟨107789904511839049716580985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71859936341226033144387323 107789904511839049716580985)
    ·
      refine ⟨80842428383879287287435739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107789904511839049716580985 80842428383879287287435739)
      ·
        refine ⟨121263642575818930931153609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80842428383879287287435739 121263642575818930931153609)
        ·
          refine ⟨90947731931864198198365207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121263642575818930931153609 90947731931864198198365207)
          ·
            refine ⟨136421597897796297297547811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90947731931864198198365207 136421597897796297297547811)
            ·
              refine ⟨204632396846694445946321717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136421597897796297297547811 204632396846694445946321717)
              ·
                refine ⟨19184287204377604307467661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204632396846694445946321717 19184287204377604307467661)
                ·
                  refine ⟨7194107701641601615300373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19184287204377604307467661 7194107701641601615300373)
                  ·
                    refine ⟨337223798514450075717205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7194107701641601615300373 337223798514450075717205)
                    ·
                      rfl

theorem cell23_1970223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_1970223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970223 prefixEnd_1970223 := by exact prefixLift 1970223
  have htrace : WordTrace (prefixWord ++ tailWord_1970223) baseStart_1970223 baseEnd_1970223 := by
    simpa [prefixWord, tailWord_1970223, baseEnd_1970223] using wordTrace_append hprefix tailTrace_1970223
  have hstable : (prefixWord ++ tailWord_1970223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970223).length < 2 ^ (prefixWord ++ tailWord_1970223).sum := by decide
  have hdescent : baseEnd_1970223 < baseStart_1970223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970224 : List Nat := [2, 1, 1, 1, 2, 5, 1, 5, 1, 1, 3]
def baseStart_1970224 : Nat := 118140960795 + 1970224 * 2 ^ 59
def prefixEnd_1970224 : Nat := 4983230072969 + 3 ^ 40 * 1970224 * 2
def baseEnd_1970224 : Nat := 1011671909024004723239111

theorem tailTrace_1970224 : CollatzResearch.WordTrace tailWord_1970224 prefixEnd_1970224 1011671909024004723239111 := by
  unfold tailWord_1970224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35929986407111205157586863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47906648542814940210115817 35929986407111205157586863)
  ·
    refine ⟨53894979610666807736380295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35929986407111205157586863 53894979610666807736380295)
    ·
      refine ⟨80842469416000211604570443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53894979610666807736380295 80842469416000211604570443)
      ·
        refine ⟨121263704124000317406855665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80842469416000211604570443 121263704124000317406855665)
        ·
          refine ⟨90947778093000238055141749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121263704124000317406855665 90947778093000238055141749)
          ·
            refine ⟨8526354196218772317669539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90947778093000238055141749 8526354196218772317669539)
            ·
              refine ⟨12789531294328158476504309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8526354196218772317669539 12789531294328158476504309)
              ·
                refine ⟨1199018558843264857172279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12789531294328158476504309 1199018558843264857172279)
                ·
                  refine ⟨1798527838264897285758419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199018558843264857172279 1798527838264897285758419)
                  ·
                    refine ⟨2697791757397345928637629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1798527838264897285758419 2697791757397345928637629)
                    ·
                      refine ⟨1011671909024004723239111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697791757397345928637629 1011671909024004723239111)
                      ·
                        rfl

theorem cell23_1970224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 1, 3].length) (baseStart_1970224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970224 prefixEnd_1970224 := by exact prefixLift 1970224
  have htrace : WordTrace (prefixWord ++ tailWord_1970224) baseStart_1970224 baseEnd_1970224 := by
    simpa [prefixWord, tailWord_1970224, baseEnd_1970224] using wordTrace_append hprefix tailTrace_1970224
  have hstable : (prefixWord ++ tailWord_1970224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970224).length < 2 ^ (prefixWord ++ tailWord_1970224).sum := by decide
  have hdescent : baseEnd_1970224 < baseStart_1970224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970227 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 1, 5]
def baseStart_1970227 : Nat := 118140960795 + 1970227 * 2 ^ 59
def prefixEnd_1970227 : Nat := 4983230072969 + 3 ^ 40 * 1970227 * 2
def baseEnd_1970227 : Nat := 337224483155322737167199

theorem tailTrace_1970227 : CollatzResearch.WordTrace tailWord_1970227 prefixEnd_1970227 337224483155322737167199 := by
  unfold tailWord_1970227
  simp only [CollatzResearch.WordTrace]
  refine ⟨71860082233211541827532935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47906721488807694551688623 71860082233211541827532935)
  ·
    refine ⟨107790123349817312741299403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71860082233211541827532935 107790123349817312741299403)
    ·
      refine ⟨161685185024725969111949105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107790123349817312741299403 161685185024725969111949105)
      ·
        refine ⟨121263888768544476833961829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161685185024725969111949105 121263888768544476833961829)
        ·
          refine ⟨22736979144102089406367843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121263888768544476833961829 22736979144102089406367843)
          ·
            refine ⟨34105468716153134109551765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22736979144102089406367843 34105468716153134109551765)
            ·
              refine ⟨1598693846069678161385239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34105468716153134109551765 1598693846069678161385239)
              ·
                refine ⟨2398040769104517242077859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598693846069678161385239 2398040769104517242077859)
                ·
                  refine ⟨3597061153656775863116789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398040769104517242077859 3597061153656775863116789)
                  ·
                    refine ⟨337224483155322737167199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3597061153656775863116789 337224483155322737167199)
                    ·
                      rfl

theorem cell23_1970227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 5].length) (baseStart_1970227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970227 prefixEnd_1970227 := by exact prefixLift 1970227
  have htrace : WordTrace (prefixWord ++ tailWord_1970227) baseStart_1970227 baseEnd_1970227 := by
    simpa [prefixWord, tailWord_1970227, baseEnd_1970227] using wordTrace_append hprefix tailTrace_1970227
  have hstable : (prefixWord ++ tailWord_1970227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970227).length < 2 ^ (prefixWord ++ tailWord_1970227).sum := by decide
  have hdescent : baseEnd_1970227 < baseStart_1970227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970241 : List Nat := [1, 2, 5, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_1970241 : Nat := 118140960795 + 1970241 * 2 ^ 59
def prefixEnd_1970241 : Nat := 4983230072969 + 3 ^ 40 * 1970241 * 2
def baseEnd_1970241 : Nat := 1011680638195131156726533

theorem tailTrace_1970241 : CollatzResearch.WordTrace tailWord_1970241 prefixEnd_1970241 1011680638195131156726533 := by
  unfold tailWord_1970241
  simp only [CollatzResearch.WordTrace]
  refine ⟨71860592855160822218542577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47907061903440548145695051 71860592855160822218542577)
  ·
    refine ⟨53895444641370616663906933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71860592855160822218542577 53895444641370616663906933)
    ·
      refine ⟨5052697935128495312241275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53895444641370616663906933 5052697935128495312241275)
      ·
        refine ⟨7579046902692742968361913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5052697935128495312241275 7579046902692742968361913)
        ·
          refine ⟨5684285177019557226271435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7579046902692742968361913 5684285177019557226271435)
          ·
            refine ⟨8526427765529335839407153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684285177019557226271435 8526427765529335839407153)
            ·
              refine ⟨6394820824147001879555365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8526427765529335839407153 6394820824147001879555365)
              ·
                refine ⟨1199028904527562852416631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6394820824147001879555365 1199028904527562852416631)
                ·
                  refine ⟨1798543356791344278624947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199028904527562852416631 1798543356791344278624947)
                  ·
                    refine ⟨2697815035187016417937421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1798543356791344278624947 2697815035187016417937421)
                    ·
                      refine ⟨1011680638195131156726533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697815035187016417937421 1011680638195131156726533)
                      ·
                        rfl

theorem cell23_1970241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_1970241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970241 prefixEnd_1970241 := by exact prefixLift 1970241
  have htrace : WordTrace (prefixWord ++ tailWord_1970241) baseStart_1970241 baseEnd_1970241 := by
    simpa [prefixWord, tailWord_1970241, baseEnd_1970241] using wordTrace_append hprefix tailTrace_1970241
  have hstable : (prefixWord ++ tailWord_1970241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970241).length < 2 ^ (prefixWord ++ tailWord_1970241).sum := by decide
  have hdescent : baseEnd_1970241 < baseStart_1970241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970264 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 3, 2, 2]
def baseStart_1970264 : Nat := 118140960795 + 1970264 * 2 ^ 59
def prefixEnd_1970264 : Nat := 4983230072969 + 3 ^ 40 * 1970264 * 2
def baseEnd_1970264 : Nat := 1011692448250184566738927

theorem tailTrace_1970264 : CollatzResearch.WordTrace tailWord_1970264 prefixEnd_1970264 1011692448250184566738927 := by
  unfold tailWord_1970264
  simp only [CollatzResearch.WordTrace]
  refine ⟨35930715867038748573314923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47907621156051664764419897 35930715867038748573314923)
  ·
    refine ⟨53896073800558122859972385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35930715867038748573314923 53896073800558122859972385)
    ·
      refine ⟨40422055350418592144979289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53896073800558122859972385 40422055350418592144979289)
      ·
        refine ⟨30316541512813944108734467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40422055350418592144979289 30316541512813944108734467)
        ·
          refine ⟨45474812269220916163101701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30316541512813944108734467 45474812269220916163101701)
          ·
            refine ⟨8526527300478921780581569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45474812269220916163101701 8526527300478921780581569)
            ·
              refine ⟨6394895475359191335436177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8526527300478921780581569 6394895475359191335436177)
              ·
                refine ⟨4796171606519393501577133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6394895475359191335436177 4796171606519393501577133)
                ·
                  refine ⟨1798564352444772563091425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4796171606519393501577133 1798564352444772563091425)
                  ·
                    refine ⟨1348923264333579422318569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1798564352444772563091425 1348923264333579422318569)
                    ·
                      refine ⟨1011692448250184566738927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348923264333579422318569 1011692448250184566738927)
                      ·
                        rfl

theorem cell23_1970264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_1970264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970264 prefixEnd_1970264 := by exact prefixLift 1970264
  have htrace : WordTrace (prefixWord ++ tailWord_1970264) baseStart_1970264 baseEnd_1970264 := by
    simpa [prefixWord, tailWord_1970264, baseEnd_1970264] using wordTrace_append hprefix tailTrace_1970264
  have hstable : (prefixWord ++ tailWord_1970264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970264).length < 2 ^ (prefixWord ++ tailWord_1970264).sum := by decide
  have hdescent : baseEnd_1970264 < baseStart_1970264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970318 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_1970318 : Nat := 118140960795 + 1970318 * 2 ^ 59
def prefixEnd_1970318 : Nat := 4983230072969 + 3 ^ 40 * 1970318 * 2
def baseEnd_1970318 : Nat := 1011720176205527355463679

theorem tailTrace_1970318 : CollatzResearch.WordTrace tailWord_1970318 prefixEnd_1970318 1011720176205527355463679 := by
  unfold tailWord_1970318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8982925159485233046136951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47908934183921242912730405 8982925159485233046136951)
  ·
    refine ⟨13474387739227849569205427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8982925159485233046136951 13474387739227849569205427)
    ·
      refine ⟨20211581608841774353808141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13474387739227849569205427 20211581608841774353808141)
      ·
        refine ⟨7579343103315665382678053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20211581608841774353808141 7579343103315665382678053)
        ·
          refine ⟨1421126831871687259252135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7579343103315665382678053 1421126831871687259252135)
          ·
            refine ⟨2131690247807530888878203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421126831871687259252135 2131690247807530888878203)
            ·
              refine ⟨3197535371711296333317305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131690247807530888878203 3197535371711296333317305)
              ·
                refine ⟨2398151528783472249987979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197535371711296333317305 2398151528783472249987979)
                ·
                  refine ⟨3597227293175208374981969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398151528783472249987979 3597227293175208374981969)
                  ·
                    refine ⟨2697920469881406281236477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3597227293175208374981969 2697920469881406281236477)
                    ·
                      refine ⟨1011720176205527355463679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2697920469881406281236477 1011720176205527355463679)
                      ·
                        rfl

theorem cell23_1970318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_1970318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970318 prefixEnd_1970318 := by exact prefixLift 1970318
  have htrace : WordTrace (prefixWord ++ tailWord_1970318) baseStart_1970318 baseEnd_1970318 := by
    simpa [prefixWord, tailWord_1970318, baseEnd_1970318] using wordTrace_append hprefix tailTrace_1970318
  have hstable : (prefixWord ++ tailWord_1970318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970318).length < 2 ^ (prefixWord ++ tailWord_1970318).sum := by decide
  have hdescent : baseEnd_1970318 < baseStart_1970318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970341 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 1, 3, 2]
def baseStart_1970341 : Nat := 118140960795 + 1970341 * 2 ^ 59
def prefixEnd_1970341 : Nat := 4983230072969 + 3 ^ 40 * 1970341 * 2
def baseEnd_1970341 : Nat := 1011731986260580765476073

theorem tailTrace_1970341 : CollatzResearch.WordTrace tailWord_1970341 prefixEnd_1970341 1011731986260580765476073 := by
  unfold tailWord_1970341
  simp only [CollatzResearch.WordTrace]
  refine ⟨71864240154798539297182877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47909493436532359531455251 71864240154798539297182877)
  ·
    refine ⟨26949090058049452236443579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71864240154798539297182877 26949090058049452236443579)
    ·
      refine ⟨40423635087074178354665369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26949090058049452236443579 40423635087074178354665369)
      ·
        refine ⟨30317726315305633765999027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40423635087074178354665369 30317726315305633765999027)
        ·
          refine ⟨45476589472958450648998541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30317726315305633765999027 45476589472958450648998541)
          ·
            refine ⟨17053721052359418993374453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45476589472958450648998541 17053721052359418993374453)
            ·
              refine ⟨1598786348658695530628855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17053721052359418993374453 1598786348658695530628855)
              ·
                refine ⟨2398179522988043295943283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598786348658695530628855 2398179522988043295943283)
                ·
                  refine ⟨3597269284482064943914925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398179522988043295943283 3597269284482064943914925)
                  ·
                    refine ⟨1348975981680774353968097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3597269284482064943914925 1348975981680774353968097)
                    ·
                      refine ⟨1011731986260580765476073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1348975981680774353968097 1011731986260580765476073)
                      ·
                        rfl

theorem cell23_1970341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_1970341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970341 prefixEnd_1970341 := by exact prefixLift 1970341
  have htrace : WordTrace (prefixWord ++ tailWord_1970341) baseStart_1970341 baseEnd_1970341 := by
    simpa [prefixWord, tailWord_1970341, baseEnd_1970341] using wordTrace_append hprefix tailTrace_1970341
  have hstable : (prefixWord ++ tailWord_1970341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970341).length < 2 ^ (prefixWord ++ tailWord_1970341).sum := by decide
  have hdescent : baseEnd_1970341 < baseStart_1970341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970360 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 7]
def baseStart_1970360 : Nat := 118140960795 + 1970360 * 2 ^ 59
def prefixEnd_1970360 : Nat := 4983230072969 + 3 ^ 40 * 1970360 * 2
def baseEnd_1970360 : Nat := 112415749154779576793165

theorem tailTrace_1970360 : CollatzResearch.WordTrace tailWord_1970360 prefixEnd_1970360 112415749154779576793165 := by
  unfold tailWord_1970360
  simp only [CollatzResearch.WordTrace]
  refine ⟨35932466570864852771062267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47909955427819803694749689 35932466570864852771062267)
  ·
    refine ⟨53898699856297279156593401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35932466570864852771062267 53898699856297279156593401)
    ·
      refine ⟨40424024892222959367445051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53898699856297279156593401 40424024892222959367445051)
      ·
        refine ⟨60636037338334439051167577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40424024892222959367445051 60636037338334439051167577)
        ·
          refine ⟨45477028003750829288375683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60636037338334439051167577 45477028003750829288375683)
          ·
            refine ⟨68215542005626243932563525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45477028003750829288375683 68215542005626243932563525)
            ·
              refine ⟨12790414126054920737355661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68215542005626243932563525 12790414126054920737355661)
              ·
                refine ⟨4796405297270595276508373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12790414126054920737355661 4796405297270595276508373)
                ·
                  refine ⟨112415749154779576793165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4796405297270595276508373 112415749154779576793165)
                  ·
                    rfl

theorem cell23_1970360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 7].length) (baseStart_1970360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970360 prefixEnd_1970360 := by exact prefixLift 1970360
  have htrace : WordTrace (prefixWord ++ tailWord_1970360) baseStart_1970360 baseEnd_1970360 := by
    simpa [prefixWord, tailWord_1970360, baseEnd_1970360] using wordTrace_append hprefix tailTrace_1970360
  have hstable : (prefixWord ++ tailWord_1970360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970360).length < 2 ^ (prefixWord ++ tailWord_1970360).sum := by decide
  have hdescent : baseEnd_1970360 < baseStart_1970360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970437 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_1970437 : Nat := 118140960795 + 1970437 * 2 ^ 59
def prefixEnd_1970437 : Nat := 4983230072969 + 3 ^ 40 * 1970437 * 2
def baseEnd_1970437 : Nat := 337260426801137463291877

theorem tailTrace_1970437 : CollatzResearch.WordTrace tailWord_1970437 prefixEnd_1970437 337260426801137463291877 := by
  unfold tailWord_1970437
  simp only [CollatzResearch.WordTrace]
  refine ⟨71867741562450747692677565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47911827708300498461785043 71867741562450747692677565)
  ·
    refine ⟨26950403085919030384754087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71867741562450747692677565 26950403085919030384754087)
    ·
      refine ⟨40425604628878545577131131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26950403085919030384754087 40425604628878545577131131)
      ·
        refine ⟨60638406943317818365696697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40425604628878545577131131 60638406943317818365696697)
        ·
          refine ⟨45478805207488363774272523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60638406943317818365696697 45478805207488363774272523)
          ·
            refine ⟨68218207811232545661408785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45478805207488363774272523 68218207811232545661408785)
            ·
              refine ⟨51163655858424409246056589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68218207811232545661408785 51163655858424409246056589)
              ·
                refine ⟨19186370946909153467271221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51163655858424409246056589 19186370946909153467271221)
                ·
                  refine ⟨1798722276272733137556677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19186370946909153467271221 1798722276272733137556677)
                  ·
                    refine ⟨337260426801137463291877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1798722276272733137556677 337260426801137463291877)
                    ·
                      rfl

theorem cell23_1970437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_1970437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970437 prefixEnd_1970437 := by exact prefixLift 1970437
  have htrace : WordTrace (prefixWord ++ tailWord_1970437) baseStart_1970437 baseEnd_1970437 := by
    simpa [prefixWord, tailWord_1970437, baseEnd_1970437] using wordTrace_append hprefix tailTrace_1970437
  have hstable : (prefixWord ++ tailWord_1970437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970437).length < 2 ^ (prefixWord ++ tailWord_1970437).sum := by decide
  have hdescent : baseEnd_1970437 < baseStart_1970437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970447 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 3]
def baseStart_1970447 : Nat := 118140960795 + 1970447 * 2 ^ 59
def prefixEnd_1970447 : Nat := 4983230072969 + 3 ^ 40 * 1970447 * 2
def baseEnd_1970447 : Nat := 1011786415209957350750585

theorem tailTrace_1970447 : CollatzResearch.WordTrace tailWord_1970447 prefixEnd_1970447 1011786415209957350750585 := by
  unfold tailWord_1970447
  simp only [CollatzResearch.WordTrace]
  refine ⟨71868106292414519400541595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47912070861609679600361063 71868106292414519400541595)
  ·
    refine ⟨107802159438621779100812393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71868106292414519400541595 107802159438621779100812393)
    ·
      refine ⟨80851619578966334325609295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107802159438621779100812393 80851619578966334325609295)
      ·
        refine ⟨121277429368449501488413943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80851619578966334325609295 121277429368449501488413943)
        ·
          refine ⟨181916144052674252232620915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121277429368449501488413943 181916144052674252232620915)
          ·
            refine ⟨272874216079011378348931373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181916144052674252232620915 272874216079011378348931373)
            ·
              refine ⟨102327831029629266880849265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272874216079011378348931373 102327831029629266880849265)
              ·
                refine ⟨76745873272221950160636949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102327831029629266880849265 76745873272221950160636949)
                ·
                  refine ⟨3597462809635403913779857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76745873272221950160636949 3597462809635403913779857)
                  ·
                    refine ⟨2698097107226552935334893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3597462809635403913779857 2698097107226552935334893)
                    ·
                      refine ⟨1011786415209957350750585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2698097107226552935334893 1011786415209957350750585)
                      ·
                        rfl

theorem cell23_1970447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_1970447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970447 prefixEnd_1970447 := by exact prefixLift 1970447
  have htrace : WordTrace (prefixWord ++ tailWord_1970447) baseStart_1970447 baseEnd_1970447 := by
    simpa [prefixWord, tailWord_1970447, baseEnd_1970447] using wordTrace_append hprefix tailTrace_1970447
  have hstable : (prefixWord ++ tailWord_1970447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970447).length < 2 ^ (prefixWord ++ tailWord_1970447).sum := by decide
  have hdescent : baseEnd_1970447 < baseStart_1970447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970461 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1970461 : Nat := 118140960795 + 1970461 * 2 ^ 59
def prefixEnd_1970461 : Nat := 4983230072969 + 3 ^ 40 * 1970461 * 2
def baseEnd_1970461 : Nat := 1011793603939120295975521

theorem tailTrace_1970461 : CollatzResearch.WordTrace tailWord_1970461 prefixEnd_1970461 1011793603939120295975521 := by
  unfold tailWord_1970461
  simp only [CollatzResearch.WordTrace]
  refine ⟨71868616914363799791551237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47912411276242533194367491 71868616914363799791551237)
  ·
    refine ⟨13475365671443212460915857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71868616914363799791551237 13475365671443212460915857)
    ·
      refine ⟨10106524253582409345686893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13475365671443212460915857 10106524253582409345686893)
      ·
        refine ⟨3789946595093403504632585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10106524253582409345686893 3789946595093403504632585)
        ·
          refine ⟨2842459946320052628474439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3789946595093403504632585 2842459946320052628474439)
          ·
            refine ⟨4263689919480078942711659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842459946320052628474439 4263689919480078942711659)
            ·
              refine ⟨6395534879220118414067489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4263689919480078942711659 6395534879220118414067489)
              ·
                refine ⟨4796651159415088810550617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6395534879220118414067489 4796651159415088810550617)
                ·
                  refine ⟨3597488369561316607912963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4796651159415088810550617 3597488369561316607912963)
                  ·
                    refine ⟨5396232554341974911869445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3597488369561316607912963 5396232554341974911869445)
                    ·
                      refine ⟨1011793603939120295975521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5396232554341974911869445 1011793603939120295975521)
                      ·
                        rfl

theorem cell23_1970461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1970461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970461 prefixEnd_1970461 := by exact prefixLift 1970461
  have htrace : WordTrace (prefixWord ++ tailWord_1970461) baseStart_1970461 baseEnd_1970461 := by
    simpa [prefixWord, tailWord_1970461, baseEnd_1970461] using wordTrace_append hprefix tailTrace_1970461
  have hstable : (prefixWord ++ tailWord_1970461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970461).length < 2 ^ (prefixWord ++ tailWord_1970461).sum := by decide
  have hdescent : baseEnd_1970461 < baseStart_1970461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970464 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1970464 : Nat := 118140960795 + 1970464 * 2 ^ 59
def prefixEnd_1970464 : Nat := 4983230072969 + 3 ^ 40 * 1970464 * 2
def baseEnd_1970464 : Nat := 1011795144381083784238007

theorem tailTrace_1970464 : CollatzResearch.WordTrace tailWord_1970464 prefixEnd_1970464 1011795144381083784238007 := by
  unfold tailWord_1970464
  simp only [CollatzResearch.WordTrace]
  refine ⟨35934363166676465651955223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47912484222235287535940297 35934363166676465651955223)
  ·
    refine ⟨53901544750014698477932835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35934363166676465651955223 53901544750014698477932835)
    ·
      refine ⟨80852317125022047716899253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53901544750014698477932835 80852317125022047716899253)
      ·
        refine ⟨7579904730470816973459305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80852317125022047716899253 7579904730470816973459305)
        ·
          refine ⟨5684928547853112730094479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7579904730470816973459305 5684928547853112730094479)
          ·
            refine ⟨8527392821779669095141719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684928547853112730094479 8527392821779669095141719)
            ·
              refine ⟨12791089232669503642712579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8527392821779669095141719 12791089232669503642712579)
              ·
                refine ⟨19186633849004255464068869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12791089232669503642712579 19186633849004255464068869)
                ·
                  refine ⟨3597493846688297899512913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19186633849004255464068869 3597493846688297899512913)
                  ·
                    refine ⟨2698120385016223424634685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3597493846688297899512913 2698120385016223424634685)
                    ·
                      refine ⟨1011795144381083784238007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2698120385016223424634685 1011795144381083784238007)
                      ·
                        rfl

theorem cell23_1970464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1970464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970464 prefixEnd_1970464 := by exact prefixLift 1970464
  have htrace : WordTrace (prefixWord ++ tailWord_1970464) baseStart_1970464 baseEnd_1970464 := by
    simpa [prefixWord, tailWord_1970464, baseEnd_1970464] using wordTrace_append hprefix tailTrace_1970464
  have hstable : (prefixWord ++ tailWord_1970464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970464).length < 2 ^ (prefixWord ++ tailWord_1970464).sum := by decide
  have hdescent : baseEnd_1970464 < baseStart_1970464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970467 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 6]
def baseStart_1970467 : Nat := 118140960795 + 1970467 * 2 ^ 59
def prefixEnd_1970467 : Nat := 4983230072969 + 3 ^ 40 * 1970467 * 2
def baseEnd_1970467 : Nat := 112421853869227474722277

theorem tailTrace_1970467 : CollatzResearch.WordTrace tailWord_1970467 prefixEnd_1970467 112421853869227474722277 := by
  unfold tailWord_1970467
  simp only [CollatzResearch.WordTrace]
  refine ⟨71868835752342062816269655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47912557168228041877513103 71868835752342062816269655)
  ·
    refine ⟨107803253628513094224404483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71868835752342062816269655 107803253628513094224404483)
    ·
      refine ⟨161704880442769641336606725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107803253628513094224404483 161704880442769641336606725)
      ·
        refine ⟨30319665083019307750613761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161704880442769641336606725 30319665083019307750613761)
        ·
          refine ⟨22739748812264480812960321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30319665083019307750613761 22739748812264480812960321)
          ·
            refine ⟨17054811609198360609720241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22739748812264480812960321 17054811609198360609720241)
            ·
              refine ⟨12791108706898770457290181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17054811609198360609720241 12791108706898770457290181)
              ·
                refine ⟨2398332882543519460741909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12791108706898770457290181 2398332882543519460741909)
                ·
                  refine ⟨112421853869227474722277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2398332882543519460741909 112421853869227474722277)
                  ·
                    rfl

theorem cell23_1970467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 6].length) (baseStart_1970467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970467 prefixEnd_1970467 := by exact prefixLift 1970467
  have htrace : WordTrace (prefixWord ++ tailWord_1970467) baseStart_1970467 baseEnd_1970467 := by
    simpa [prefixWord, tailWord_1970467, baseEnd_1970467] using wordTrace_append hprefix tailTrace_1970467
  have hstable : (prefixWord ++ tailWord_1970467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970467).length < 2 ^ (prefixWord ++ tailWord_1970467).sum := by decide
  have hdescent : baseEnd_1970467 < baseStart_1970467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970504 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_1970504 : Nat := 118140960795 + 1970504 * 2 ^ 59
def prefixEnd_1970504 : Nat := 4983230072969 + 3 ^ 40 * 1970504 * 2
def baseEnd_1970504 : Nat := 1011815683607263627737823

theorem tailTrace_1970504 : CollatzResearch.WordTrace tailWord_1970504 prefixEnd_1970504 1011815683607263627737823 := by
  unfold tailWord_1970504
  simp only [CollatzResearch.WordTrace]
  refine ⟨35935092626604009067683283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47913456835472012090244377 35935092626604009067683283)
  ·
    refine ⟨53902638939906013601524925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35935092626604009067683283 53902638939906013601524925)
    ·
      refine ⟨20213489602464755100571847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53902638939906013601524925 20213489602464755100571847)
      ·
        refine ⟨30320234403697132650857771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20213489602464755100571847 30320234403697132650857771)
        ·
          refine ⟨45480351605545698976286657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30320234403697132650857771 45480351605545698976286657)
          ·
            refine ⟨34110263704159274232214993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45480351605545698976286657 34110263704159274232214993)
            ·
              refine ⟨25582697778119455674161245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34110263704159274232214993 25582697778119455674161245)
              ·
                refine ⟨9593511666794795877810467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25582697778119455674161245 9593511666794795877810467)
                ·
                  refine ⟨14390267500192193816715701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9593511666794795877810467 14390267500192193816715701)
                  ·
                    refine ⟨1349087578143018170317097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14390267500192193816715701 1349087578143018170317097)
                    ·
                      refine ⟨1011815683607263627737823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349087578143018170317097 1011815683607263627737823)
                      ·
                        rfl

theorem cell23_1970504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_1970504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970504 prefixEnd_1970504 := by exact prefixLift 1970504
  have htrace : WordTrace (prefixWord ++ tailWord_1970504) baseStart_1970504 baseEnd_1970504 := by
    simpa [prefixWord, tailWord_1970504, baseEnd_1970504] using wordTrace_append hprefix tailTrace_1970504
  have hstable : (prefixWord ++ tailWord_1970504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970504).length < 2 ^ (prefixWord ++ tailWord_1970504).sum := by decide
  have hdescent : baseEnd_1970504 < baseStart_1970504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970514 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_1970514 : Nat := 118140960795 + 1970514 * 2 ^ 59
def prefixEnd_1970514 : Nat := 4983230072969 + 3 ^ 40 * 1970514 * 2
def baseEnd_1970514 : Nat := 337273606137936196204259

theorem tailTrace_1970514 : CollatzResearch.WordTrace tailWord_1970514 prefixEnd_1970514 337273606137936196204259 := by
  unfold tailWord_1970514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17967637495792947460807649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47913699988781193228820397 17967637495792947460807649)
  ·
    refine ⟨13475728121844710595605737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17967637495792947460807649 13475728121844710595605737)
    ·
      refine ⟨10106796091383532946704303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13475728121844710595605737 10106796091383532946704303)
      ·
        refine ⟨15160194137075299420056455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106796091383532946704303 15160194137075299420056455)
        ·
          refine ⟨22740291205612949130084683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15160194137075299420056455 22740291205612949130084683)
          ·
            refine ⟨34110436808419423695127025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22740291205612949130084683 34110436808419423695127025)
            ·
              refine ⟨25582827606314567771345269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34110436808419423695127025 25582827606314567771345269)
              ·
                refine ⟨2398390088091990728563619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25582827606314567771345269 2398390088091990728563619)
                ·
                  refine ⟨3597585132137986092845429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398390088091990728563619 3597585132137986092845429)
                  ·
                    refine ⟨337273606137936196204259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3597585132137986092845429 337273606137936196204259)
                    ·
                      rfl

theorem cell23_1970514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_1970514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970514 prefixEnd_1970514 := by exact prefixLift 1970514
  have htrace : WordTrace (prefixWord ++ tailWord_1970514) baseStart_1970514 baseEnd_1970514 := by
    simpa [prefixWord, tailWord_1970514, baseEnd_1970514] using wordTrace_append hprefix tailTrace_1970514
  have hstable : (prefixWord ++ tailWord_1970514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970514).length < 2 ^ (prefixWord ++ tailWord_1970514).sum := by decide
  have hdescent : baseEnd_1970514 < baseStart_1970514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970537 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_1970537 : Nat := 118140960795 + 1970537 * 2 ^ 59
def prefixEnd_1970537 : Nat := 4983230072969 + 3 ^ 40 * 1970537 * 2
def baseEnd_1970537 : Nat := 1011832628468861998625171

theorem tailTrace_1970537 : CollatzResearch.WordTrace tailWord_1970537 prefixEnd_1970537 1011832628468861998625171 := by
  unfold tailWord_1970537
  simp only [CollatzResearch.WordTrace]
  refine ⟨71871388862088464771317865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47914259241392309847545243 71871388862088464771317865)
  ·
    refine ⟨53903541646566348578488399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71871388862088464771317865 53903541646566348578488399)
    ·
      refine ⟨80855312469849522867732599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53903541646566348578488399 80855312469849522867732599)
      ·
        refine ⟨121282968704774284301598899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80855312469849522867732599 121282968704774284301598899)
        ·
          refine ⟨181924453057161426452398349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121282968704774284301598899 181924453057161426452398349)
          ·
            refine ⟨68221669896435534919649381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181924453057161426452398349 68221669896435534919649381)
            ·
              refine ⟨12791563105581662797434259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68221669896435534919649381 12791563105581662797434259)
              ·
                refine ⟨19187344658372494196151389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12791563105581662797434259 19187344658372494196151389)
                ·
                  refine ⟨7195254246889685323556771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19187344658372494196151389 7195254246889685323556771)
                  ·
                    refine ⟨10792881370334527985335157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7195254246889685323556771 10792881370334527985335157)
                    ·
                      refine ⟨1011832628468861998625171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10792881370334527985335157 1011832628468861998625171)
                      ·
                        rfl

theorem cell23_1970537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_1970537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970537 prefixEnd_1970537 := by exact prefixLift 1970537
  have htrace : WordTrace (prefixWord ++ tailWord_1970537) baseStart_1970537 baseEnd_1970537 := by
    simpa [prefixWord, tailWord_1970537, baseEnd_1970537] using wordTrace_append hprefix tailTrace_1970537
  have hstable : (prefixWord ++ tailWord_1970537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970537).length < 2 ^ (prefixWord ++ tailWord_1970537).sum := by decide
  have hdescent : baseEnd_1970537 < baseStart_1970537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970544 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 1, 6]
def baseStart_1970544 : Nat := 118140960795 + 1970544 * 2 ^ 59
def prefixEnd_1970544 : Nat := 4983230072969 + 3 ^ 40 * 1970544 * 2
def baseEnd_1970544 : Nat := 337278740944481157079213

theorem tailTrace_1970544 : CollatzResearch.WordTrace tailWord_1970544 prefixEnd_1970544 337278740944481157079213 := by
  unfold tailWord_1970544
  simp only [CollatzResearch.WordTrace]
  refine ⟨35935822086531552483411343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47914429448708736644548457 35935822086531552483411343)
  ·
    refine ⟨53903733129797328725117015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35935822086531552483411343 53903733129797328725117015)
    ·
      refine ⟨80855599694695993087675523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53903733129797328725117015 80855599694695993087675523)
      ·
        refine ⟨121283399542043989631513285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80855599694695993087675523 121283399542043989631513285)
        ·
          refine ⟨22740637414133248055908741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121283399542043989631513285 22740637414133248055908741)
          ·
            refine ⟨4263869515149984010482889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22740637414133248055908741 4263869515149984010482889)
            ·
              refine ⟨3197902136362488007862167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4263869515149984010482889 3197902136362488007862167)
              ·
                refine ⟨4796853204543732011793251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197902136362488007862167 4796853204543732011793251)
                ·
                  refine ⟨7195279806815598017689877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796853204543732011793251 7195279806815598017689877)
                  ·
                    refine ⟨337278740944481157079213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7195279806815598017689877 337278740944481157079213)
                    ·
                      rfl

theorem cell23_1970544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_1970544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970544 prefixEnd_1970544 := by exact prefixLift 1970544
  have htrace : WordTrace (prefixWord ++ tailWord_1970544) baseStart_1970544 baseEnd_1970544 := by
    simpa [prefixWord, tailWord_1970544, baseEnd_1970544] using wordTrace_append hprefix tailTrace_1970544
  have hstable : (prefixWord ++ tailWord_1970544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970544).length < 2 ^ (prefixWord ++ tailWord_1970544).sum := by decide
  have hdescent : baseEnd_1970544 < baseStart_1970544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970547 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 4]
def baseStart_1970547 : Nat := 118140960795 + 1970547 * 2 ^ 59
def prefixEnd_1970547 : Nat := 4983230072969 + 3 ^ 40 * 1970547 * 2
def baseEnd_1970547 : Nat := 1011837763275406959500125

theorem tailTrace_1970547 : CollatzResearch.WordTrace tailWord_1970547 prefixEnd_1970547 1011837763275406959500125 := by
  unfold tailWord_1970547
  simp only [CollatzResearch.WordTrace]
  refine ⟨71871753592052236479181895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47914502394701490986121263 71871753592052236479181895)
  ·
    refine ⟨107807630388078354718772843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71871753592052236479181895 107807630388078354718772843)
    ·
      refine ⟨161711445582117532078159265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107807630388078354718772843 161711445582117532078159265)
      ·
        refine ⟨121283584186588149058619449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161711445582117532078159265 121283584186588149058619449)
        ·
          refine ⟨90962688139941111793964587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121283584186588149058619449 90962688139941111793964587)
          ·
            refine ⟨136444032209911667690946881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90962688139941111793964587 136444032209911667690946881)
            ·
              refine ⟨102333024157433750768210161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136444032209911667690946881 102333024157433750768210161)
              ·
                refine ⟨76749768118075313076157621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102333024157433750768210161 76749768118075313076157621)
                ·
                  refine ⟨7195290761069560600889777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76749768118075313076157621 7195290761069560600889777)
                  ·
                    refine ⟨5396468070802170450667333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7195290761069560600889777 5396468070802170450667333)
                    ·
                      refine ⟨1011837763275406959500125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5396468070802170450667333 1011837763275406959500125)
                      ·
                        rfl

theorem cell23_1970547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_1970547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970547 prefixEnd_1970547 := by exact prefixLift 1970547
  have htrace : WordTrace (prefixWord ++ tailWord_1970547) baseStart_1970547 baseEnd_1970547 := by
    simpa [prefixWord, tailWord_1970547, baseEnd_1970547] using wordTrace_append hprefix tailTrace_1970547
  have hstable : (prefixWord ++ tailWord_1970547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970547).length < 2 ^ (prefixWord ++ tailWord_1970547).sum := by decide
  have hdescent : baseEnd_1970547 < baseStart_1970547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970564 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1970564 : Nat := 118140960795 + 1970564 * 2 ^ 59
def prefixEnd_1970564 : Nat := 4983230072969 + 3 ^ 40 * 1970564 * 2
def baseEnd_1970564 : Nat := 1011846492446533392987547

theorem tailTrace_1970564 : CollatzResearch.WordTrace tailWord_1970564 prefixEnd_1970564 1011846492446533392987547 := by
  unfold tailWord_1970564
  simp only [CollatzResearch.WordTrace]
  refine ⟨35936186816495324191275373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47914915755327098921700497 35936186816495324191275373)
  ·
    refine ⟨13476070056185746571728265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35936186816495324191275373 13476070056185746571728265)
    ·
      refine ⟨10107052542139309928796199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13476070056185746571728265 10107052542139309928796199)
      ·
        refine ⟨15160578813208964893194299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10107052542139309928796199 15160578813208964893194299)
        ·
          refine ⟨22740868219813447339791449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15160578813208964893194299 22740868219813447339791449)
          ·
            refine ⟨17055651164860085504843587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22740868219813447339791449 17055651164860085504843587)
            ·
              refine ⟨25583476747290128257265381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17055651164860085504843587 25583476747290128257265381)
              ·
                refine ⟨4796901890116899048237259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25583476747290128257265381 4796901890116899048237259)
                ·
                  refine ⟨7195352835175348572355889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796901890116899048237259 7195352835175348572355889)
                  ·
                    refine ⟨5396514626381511429266917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7195352835175348572355889 5396514626381511429266917)
                    ·
                      refine ⟨1011846492446533392987547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5396514626381511429266917 1011846492446533392987547)
                      ·
                        rfl

theorem cell23_1970564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1970564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970564 prefixEnd_1970564 := by exact prefixLift 1970564
  have htrace : WordTrace (prefixWord ++ tailWord_1970564) baseStart_1970564 baseEnd_1970564 := by
    simpa [prefixWord, tailWord_1970564, baseEnd_1970564] using wordTrace_append hprefix tailTrace_1970564
  have hstable : (prefixWord ++ tailWord_1970564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970564).length < 2 ^ (prefixWord ++ tailWord_1970564).sum := by decide
  have hdescent : baseEnd_1970564 < baseStart_1970564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970571 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 3]
def baseStart_1970571 : Nat := 118140960795 + 1970571 * 2 ^ 59
def prefixEnd_1970571 : Nat := 4983230072969 + 3 ^ 40 * 1970571 * 2
def baseEnd_1970571 : Nat := 1011850086811114865600015

theorem tailTrace_1970571 : CollatzResearch.WordTrace tailWord_1970571 prefixEnd_1970571 1011850086811114865600015 := by
  unfold tailWord_1970571
  simp only [CollatzResearch.WordTrace]
  refine ⟨71872628943965288578055567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47915085962643525718703711 71872628943965288578055567)
  ·
    refine ⟨107808943415947932867083351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71872628943965288578055567 107808943415947932867083351)
    ·
      refine ⟨161713415123921899300625027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107808943415947932867083351 161713415123921899300625027)
      ·
        refine ⟨242570122685882848950937541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161713415123921899300625027 242570122685882848950937541)
        ·
          refine ⟨45481898003603034178300789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242570122685882848950937541 45481898003603034178300789)
          ·
            refine ⟨4263927937837784454215699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45481898003603034178300789 4263927937837784454215699)
            ·
              refine ⟨6395891906756676681323549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4263927937837784454215699 6395891906756676681323549)
              ·
                refine ⟨2398459465033753755496331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6395891906756676681323549 2398459465033753755496331)
                ·
                  refine ⟨3597689197550630633244497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398459465033753755496331 3597689197550630633244497)
                  ·
                    refine ⟨2698266898162972974933373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3597689197550630633244497 2698266898162972974933373)
                    ·
                      refine ⟨1011850086811114865600015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2698266898162972974933373 1011850086811114865600015)
                      ·
                        rfl

theorem cell23_1970571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 3].length) (baseStart_1970571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970571 prefixEnd_1970571 := by exact prefixLift 1970571
  have htrace : WordTrace (prefixWord ++ tailWord_1970571) baseStart_1970571 baseEnd_1970571 := by
    simpa [prefixWord, tailWord_1970571, baseEnd_1970571] using wordTrace_append hprefix tailTrace_1970571
  have hstable : (prefixWord ++ tailWord_1970571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970571).length < 2 ^ (prefixWord ++ tailWord_1970571).sum := by decide
  have hdescent : baseEnd_1970571 < baseStart_1970571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970574 : List Nat := [4, 1, 1, 4, 1, 2, 10]
def baseStart_1970574 : Nat := 118140960795 + 1970574 * 2 ^ 59
def prefixEnd_1970574 : Nat := 4983230072969 + 3 ^ 40 * 1970574 * 2
def baseEnd_1970574 : Nat := 12491995398186152516821

theorem tailTrace_1970574 : CollatzResearch.WordTrace tailWord_1970574 prefixEnd_1970574 12491995398186152516821 := by
  unfold tailWord_1970574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984092295369302511301847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47915158908636280060276517 8984092295369302511301847)
  ·
    refine ⟨13476138443053953766952771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8984092295369302511301847 13476138443053953766952771)
    ·
      refine ⟨20214207664580930650429157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13476138443053953766952771 20214207664580930650429157)
      ·
        refine ⟨3790163937108924496955467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20214207664580930650429157 3790163937108924496955467)
        ·
          refine ⟨5685245905663386745433201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790163937108924496955467 5685245905663386745433201)
          ·
            refine ⟨4263934429247540059074901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5685245905663386745433201 4263934429247540059074901)
            ·
              refine ⟨12491995398186152516821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4263934429247540059074901 12491995398186152516821)
              ·
                rfl

theorem cell23_1970574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 10].length) (baseStart_1970574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970574 prefixEnd_1970574 := by exact prefixLift 1970574
  have htrace : WordTrace (prefixWord ++ tailWord_1970574) baseStart_1970574 baseEnd_1970574 := by
    simpa [prefixWord, tailWord_1970574, baseEnd_1970574] using wordTrace_append hprefix tailTrace_1970574
  have hstable : (prefixWord ++ tailWord_1970574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970574).length < 2 ^ (prefixWord ++ tailWord_1970574).sum := by decide
  have hdescent : baseEnd_1970574 < baseStart_1970574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970601 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 3]
def baseStart_1970601 : Nat := 118140960795 + 1970601 * 2 ^ 59
def prefixEnd_1970601 : Nat := 4983230072969 + 3 ^ 40 * 1970601 * 2
def baseEnd_1970601 : Nat := 1011865491230749748224877

theorem tailTrace_1970601 : CollatzResearch.WordTrace tailWord_1970601 prefixEnd_1970601 1011865491230749748224877 := by
  unfold tailWord_1970601
  simp only [CollatzResearch.WordTrace]
  refine ⟨71873723133856603701647657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47915815422571069134431771 71873723133856603701647657)
  ·
    refine ⟨53905292350392452776235743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71873723133856603701647657 53905292350392452776235743)
    ·
      refine ⟨80857938525588679164353615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53905292350392452776235743 80857938525588679164353615)
      ·
        refine ⟨121286907788383018746530423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80857938525588679164353615 121286907788383018746530423)
        ·
          refine ⟨181930361682574528119795635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121286907788383018746530423 181930361682574528119795635)
          ·
            refine ⟨272895542523861792179693453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181930361682574528119795635 272895542523861792179693453)
            ·
              refine ⟨102335828446448172067385045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272895542523861792179693453 102335828446448172067385045)
              ·
                refine ⟨2398495979213629032829337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102335828446448172067385045 2398495979213629032829337)
                ·
                  refine ⟨1798871984410221774622003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2398495979213629032829337 1798871984410221774622003)
                  ·
                    refine ⟨2698307976615332661933005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1798871984410221774622003 2698307976615332661933005)
                    ·
                      refine ⟨1011865491230749748224877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2698307976615332661933005 1011865491230749748224877)
                      ·
                        rfl

theorem cell23_1970601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 3].length) (baseStart_1970601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970601 prefixEnd_1970601 := by exact prefixLift 1970601
  have htrace : WordTrace (prefixWord ++ tailWord_1970601) baseStart_1970601 baseEnd_1970601 := by
    simpa [prefixWord, tailWord_1970601, baseEnd_1970601] using wordTrace_append hprefix tailTrace_1970601
  have hstable : (prefixWord ++ tailWord_1970601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970601).length < 2 ^ (prefixWord ++ tailWord_1970601).sum := by decide
  have hdescent : baseEnd_1970601 < baseStart_1970601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970602 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1970602 : Nat := 118140960795 + 1970602 * 2 ^ 59
def prefixEnd_1970602 : Nat := 4983230072969 + 3 ^ 40 * 1970602 * 2
def baseEnd_1970602 : Nat := 1011866004711404244312373

theorem tailTrace_1970602 : CollatzResearch.WordTrace tailWord_1970602 prefixEnd_1970602 1011866004711404244312373 := by
  unfold tailWord_1970602
  simp only [CollatzResearch.WordTrace]
  refine ⟨17968439901713245218108515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47915839737901987248289373 17968439901713245218108515)
  ·
    refine ⟨26952659852569867827162773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17968439901713245218108515 26952659852569867827162773)
    ·
      refine ⟨1263405930589212554398255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26952659852569867827162773 1263405930589212554398255)
      ·
        refine ⟨1895108895883818831597383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263405930589212554398255 1895108895883818831597383)
        ·
          refine ⟨2842663343825728247396075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895108895883818831597383 2842663343825728247396075)
          ·
            refine ⟨4263995015738592371094113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842663343825728247396075 4263995015738592371094113)
            ·
              refine ⟨3197996261803944278320585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4263995015738592371094113 3197996261803944278320585)
              ·
                refine ⟨2398497196352958208740439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197996261803944278320585 2398497196352958208740439)
                ·
                  refine ⟨3597745794529437313110659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398497196352958208740439 3597745794529437313110659)
                  ·
                    refine ⟨5396618691794155969665989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3597745794529437313110659 5396618691794155969665989)
                    ·
                      refine ⟨1011866004711404244312373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5396618691794155969665989 1011866004711404244312373)
                      ·
                        rfl

theorem cell23_1970602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1970602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970602 prefixEnd_1970602 := by exact prefixLift 1970602
  have htrace : WordTrace (prefixWord ++ tailWord_1970602) baseStart_1970602 baseEnd_1970602 := by
    simpa [prefixWord, tailWord_1970602, baseEnd_1970602] using wordTrace_append hprefix tailTrace_1970602
  have hstable : (prefixWord ++ tailWord_1970602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970602).length < 2 ^ (prefixWord ++ tailWord_1970602).sum := by decide
  have hdescent : baseEnd_1970602 < baseStart_1970602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970605 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1970605 : Nat := 118140960795 + 1970605 * 2 ^ 59
def prefixEnd_1970605 : Nat := 4983230072969 + 3 ^ 40 * 1970605 * 2
def baseEnd_1970605 : Nat := 1011867545153367732574859

theorem tailTrace_1970605 : CollatzResearch.WordTrace tailWord_1970605 prefixEnd_1970605 1011867545153367732574859 := by
  unfold tailWord_1970605
  simp only [CollatzResearch.WordTrace]
  refine ⟨71873869025842112384793269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47915912683894741589862179 71873869025842112384793269)
  ·
    refine ⟨6738175221172698036074369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71873869025842112384793269 6738175221172698036074369)
    ·
      refine ⟨5053631415879523527055777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6738175221172698036074369 5053631415879523527055777)
      ·
        refine ⟨3790223561909642645291833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5053631415879523527055777 3790223561909642645291833)
        ·
          refine ⟨2842667671432231983968875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3790223561909642645291833 2842667671432231983968875)
          ·
            refine ⟨4264001507148347975953313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842667671432231983968875 4264001507148347975953313)
            ·
              refine ⟨3198001130361260981964985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264001507148347975953313 3198001130361260981964985)
              ·
                refine ⟨2398500847770945736473739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3198001130361260981964985 2398500847770945736473739)
                ·
                  refine ⟨3597751271656418604710609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398500847770945736473739 3597751271656418604710609)
                  ·
                    refine ⟨2698313453742313953532957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3597751271656418604710609 2698313453742313953532957)
                    ·
                      refine ⟨1011867545153367732574859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2698313453742313953532957 1011867545153367732574859)
                      ·
                        rfl

theorem cell23_1970605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1970605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970605 prefixEnd_1970605 := by exact prefixLift 1970605
  have htrace : WordTrace (prefixWord ++ tailWord_1970605) baseStart_1970605 baseEnd_1970605 := by
    simpa [prefixWord, tailWord_1970605, baseEnd_1970605] using wordTrace_append hprefix tailTrace_1970605
  have hstable : (prefixWord ++ tailWord_1970605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970605).length < 2 ^ (prefixWord ++ tailWord_1970605).sum := by decide
  have hdescent : baseEnd_1970605 < baseStart_1970605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970625 : List Nat := [1, 2, 7, 1, 2, 1, 9]
def baseStart_1970625 : Nat := 118140960795 + 1970625 * 2 ^ 59
def prefixEnd_1970625 : Nat := 4983230072969 + 3 ^ 40 * 1970625 * 2
def baseEnd_1970625 : Nat := 12492318700820464868207

theorem tailTrace_1970625 : CollatzResearch.WordTrace tailWord_1970625 prefixEnd_1970625 12492318700820464868207 := by
  unfold tailWord_1970625
  simp only [CollatzResearch.WordTrace]
  refine ⟨71874598485769655800521329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47916398990513103867014219 71874598485769655800521329)
  ·
    refine ⟨53905948864327241850390997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71874598485769655800521329 53905948864327241850390997)
    ·
      refine ⟨1263420676507669730868539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 53905948864327241850390997 1263420676507669730868539)
      ·
        refine ⟨1895131014761504596302809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263420676507669730868539 1895131014761504596302809)
        ·
          refine ⟨1421348261071128447227107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1895131014761504596302809 1421348261071128447227107)
          ·
            refine ⟨2132022391606692670840661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421348261071128447227107 2132022391606692670840661)
            ·
              refine ⟨12492318700820464868207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2132022391606692670840661 12492318700820464868207)
              ·
                rfl

theorem cell23_1970625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 9].length) (baseStart_1970625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970625 prefixEnd_1970625 := by exact prefixLift 1970625
  have htrace : WordTrace (prefixWord ++ tailWord_1970625) baseStart_1970625 baseEnd_1970625 := by
    simpa [prefixWord, tailWord_1970625, baseEnd_1970625] using wordTrace_append hprefix tailTrace_1970625
  have hstable : (prefixWord ++ tailWord_1970625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970625).length < 2 ^ (prefixWord ++ tailWord_1970625).sum := by decide
  have hdescent : baseEnd_1970625 < baseStart_1970625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970692 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_1970692 : Nat := 118140960795 + 1970692 * 2 ^ 59
def prefixEnd_1970692 : Nat := 4983230072969 + 3 ^ 40 * 1970692 * 2
def baseEnd_1970692 : Nat := 1011912217970308892186959

theorem tailTrace_1970692 : CollatzResearch.WordTrace tailWord_1970692 prefixEnd_1970692 1011912217970308892186959 := by
  unfold tailWord_1970692
  simp only [CollatzResearch.WordTrace]
  refine ⟨35938521088263463121605165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47918028117684617495473553 35938521088263463121605165)
  ·
    refine ⟨13476945408098798670601937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35938521088263463121605165 13476945408098798670601937)
    ·
      refine ⟨10107709056074099002951453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13476945408098798670601937 10107709056074099002951453)
      ·
        refine ⟨3790390896027787126106795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10107709056074099002951453 3790390896027787126106795)
        ·
          refine ⟨5685586344041680689160193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790390896027787126106795 5685586344041680689160193)
          ·
            refine ⟨4264189758031260516870145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5685586344041680689160193 4264189758031260516870145)
            ·
              refine ⟨3198142318523445387652609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264189758031260516870145 3198142318523445387652609)
              ·
                refine ⟨2398606738892584040739457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3198142318523445387652609 2398606738892584040739457)
                ·
                  refine ⟨1798955054169438030554593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2398606738892584040739457 1798955054169438030554593)
                  ·
                    refine ⟨1349216290627078522915945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1798955054169438030554593 1349216290627078522915945)
                    ·
                      refine ⟨1011912217970308892186959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349216290627078522915945 1011912217970308892186959)
                      ·
                        rfl

theorem cell23_1970692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_1970692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970692 prefixEnd_1970692 := by exact prefixLift 1970692
  have htrace : WordTrace (prefixWord ++ tailWord_1970692) baseStart_1970692 baseEnd_1970692 := by
    simpa [prefixWord, tailWord_1970692, baseEnd_1970692] using wordTrace_append hprefix tailTrace_1970692
  have hstable : (prefixWord ++ tailWord_1970692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970692).length < 2 ^ (prefixWord ++ tailWord_1970692).sum := by decide
  have hdescent : baseEnd_1970692 < baseStart_1970692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970708 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1970708 : Nat := 118140960795 + 1970708 * 2 ^ 59
def prefixEnd_1970708 : Nat := 4983230072969 + 3 ^ 40 * 1970708 * 2
def baseEnd_1970708 : Nat := 1011920433660780829586885

theorem tailTrace_1970708 : CollatzResearch.WordTrace tailWord_1970708 prefixEnd_1970708 1011920433660780829586885 := by
  unfold tailWord_1970708
  simp only [CollatzResearch.WordTrace]
  refine ⟨35938812872234480487896389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47918417162979307317195185 35938812872234480487896389)
  ·
    refine ⟨6738527413543965091480573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35938812872234480487896389 6738527413543965091480573)
    ·
      refine ⟨2526947780078986909305215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6738527413543965091480573 2526947780078986909305215)
      ·
        refine ⟨3790421670118480363957823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2526947780078986909305215 3790421670118480363957823)
        ·
          refine ⟨5685632505177720545936735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790421670118480363957823 5685632505177720545936735)
          ·
            refine ⟨8528448757766580818905103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685632505177720545936735 8528448757766580818905103)
            ·
              refine ⟨12792673136649871228357655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8528448757766580818905103 12792673136649871228357655)
              ·
                refine ⟨19189009704974806842536483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12792673136649871228357655 19189009704974806842536483)
                ·
                  refine ⟨28783514557462210263804725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19189009704974806842536483 28783514557462210263804725)
                  ·
                    refine ⟨2698454489762082212231693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28783514557462210263804725 2698454489762082212231693)
                    ·
                      refine ⟨1011920433660780829586885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2698454489762082212231693 1011920433660780829586885)
                      ·
                        rfl

theorem cell23_1970708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1970708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970708 prefixEnd_1970708 := by exact prefixLift 1970708
  have htrace : WordTrace (prefixWord ++ tailWord_1970708) baseStart_1970708 baseEnd_1970708 := by
    simpa [prefixWord, tailWord_1970708, baseEnd_1970708] using wordTrace_append hprefix tailTrace_1970708
  have hstable : (prefixWord ++ tailWord_1970708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970708).length < 2 ^ (prefixWord ++ tailWord_1970708).sum := by decide
  have hdescent : baseEnd_1970708 < baseStart_1970708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970728 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1970728 : Nat := 118140960795 + 1970728 * 2 ^ 59
def prefixEnd_1970728 : Nat := 4983230072969 + 3 ^ 40 * 1970728 * 2
def baseEnd_1970728 : Nat := 337310234424623583778931

theorem tailTrace_1970728 : CollatzResearch.WordTrace tailWord_1970728 prefixEnd_1970728 337310234424623583778931 := by
  unfold tailWord_1970728
  simp only [CollatzResearch.WordTrace]
  refine ⟨35939177602198252195760419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47918903469597669594347225 35939177602198252195760419)
  ·
    refine ⟨53908766403297378293640629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35939177602198252195760419 53908766403297378293640629)
    ·
      refine ⟨5053946850309129215028809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53908766403297378293640629 5053946850309129215028809)
      ·
        refine ⟨3790460137731846911271607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5053946850309129215028809 3790460137731846911271607)
        ·
          refine ⟨5685690206597770366907411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790460137731846911271607 5685690206597770366907411)
          ·
            refine ⟨8528535309896655550361117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685690206597770366907411 8528535309896655550361117)
            ·
              refine ⟨3198200741211245831385419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8528535309896655550361117 3198200741211245831385419)
              ·
                refine ⟨4797301111816868747078129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198200741211245831385419 4797301111816868747078129)
                ·
                  refine ⟨3597975833862651560308597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4797301111816868747078129 3597975833862651560308597)
                  ·
                    refine ⟨337310234424623583778931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3597975833862651560308597 337310234424623583778931)
                    ·
                      rfl

theorem cell23_1970728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1970728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970728 prefixEnd_1970728 := by exact prefixLift 1970728
  have htrace : WordTrace (prefixWord ++ tailWord_1970728) baseStart_1970728 baseEnd_1970728 := by
    simpa [prefixWord, tailWord_1970728, baseEnd_1970728] using wordTrace_append hprefix tailTrace_1970728
  have hstable : (prefixWord ++ tailWord_1970728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970728).length < 2 ^ (prefixWord ++ tailWord_1970728).sum := by decide
  have hdescent : baseEnd_1970728 < baseStart_1970728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970741 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1970741 : Nat := 118140960795 + 1970741 * 2 ^ 59
def prefixEnd_1970741 : Nat := 4983230072969 + 3 ^ 40 * 1970741 * 2
def baseEnd_1970741 : Nat := 337312459507459733491411

theorem tailTrace_1970741 : CollatzResearch.WordTrace tailWord_1970741 prefixEnd_1970741 337312459507459733491411 := by
  unfold tailWord_1970741
  simp only [CollatzResearch.WordTrace]
  refine ⟨71878829353349407611744077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47919219568899605074496051 71878829353349407611744077)
  ·
    refine ⟨26954561007506027854404029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71878829353349407611744077 26954561007506027854404029)
    ·
      refine ⟨10107960377814760445401511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26954561007506027854404029 10107960377814760445401511)
      ·
        refine ⟨15161940566722140668102267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10107960377814760445401511 15161940566722140668102267)
        ·
          refine ⟨22742910850083211002153401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15161940566722140668102267 22742910850083211002153401)
          ·
            refine ⟨17057183137562408251615051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22742910850083211002153401 17057183137562408251615051)
            ·
              refine ⟨25585774706343612377422577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17057183137562408251615051 25585774706343612377422577)
              ·
                refine ⟨19189331029757709283066933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25585774706343612377422577 19189331029757709283066933)
                ·
                  refine ⟨1798999784039785245287525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19189331029757709283066933 1798999784039785245287525)
                  ·
                    refine ⟨337312459507459733491411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1798999784039785245287525 337312459507459733491411)
                    ·
                      rfl

theorem cell23_1970741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1970741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970741 prefixEnd_1970741 := by exact prefixLift 1970741
  have htrace : WordTrace (prefixWord ++ tailWord_1970741) baseStart_1970741 baseEnd_1970741 := by
    simpa [prefixWord, tailWord_1970741, baseEnd_1970741] using wordTrace_append hprefix tailTrace_1970741
  have hstable : (prefixWord ++ tailWord_1970741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970741).length < 2 ^ (prefixWord ++ tailWord_1970741).sum := by decide
  have hdescent : baseEnd_1970741 < baseStart_1970741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970744 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_1970744 : Nat := 118140960795 + 1970744 * 2 ^ 59
def prefixEnd_1970744 : Nat := 4983230072969 + 3 ^ 40 * 1970744 * 2
def baseEnd_1970744 : Nat := 1011938918964342688736719

theorem tailTrace_1970744 : CollatzResearch.WordTrace tailWord_1970744 prefixEnd_1970744 1011938918964342688736719 := by
  unfold tailWord_1970744
  simp only [CollatzResearch.WordTrace]
  refine ⟨35939469386169269562051643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47919292514892359416068857 35939469386169269562051643)
  ·
    refine ⟨53909204079253904343077465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35939469386169269562051643 53909204079253904343077465)
    ·
      refine ⟨40431903059440428257308099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53909204079253904343077465 40431903059440428257308099)
      ·
        refine ⟨60647854589160642385962149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40431903059440428257308099 60647854589160642385962149)
        ·
          refine ⟨11371472735467620447367903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60647854589160642385962149 11371472735467620447367903)
          ·
            refine ⟨17057209103201430671051855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11371472735467620447367903 17057209103201430671051855)
            ·
              refine ⟨25585813654802146006577783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17057209103201430671051855 25585813654802146006577783)
              ·
                refine ⟨38378720482203219009866675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25585813654802146006577783 38378720482203219009866675)
                ·
                  refine ⟨57568080723304828514800013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38378720482203219009866675 57568080723304828514800013)
                  ·
                    refine ⟨21588030271239310693050005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57568080723304828514800013 21588030271239310693050005)
                    ·
                      refine ⟨1011938918964342688736719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21588030271239310693050005 1011938918964342688736719)
                      ·
                        rfl

theorem cell23_1970744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_1970744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970744 prefixEnd_1970744 := by exact prefixLift 1970744
  have htrace : WordTrace (prefixWord ++ tailWord_1970744) baseStart_1970744 baseEnd_1970744 := by
    simpa [prefixWord, tailWord_1970744, baseEnd_1970744] using wordTrace_append hprefix tailTrace_1970744
  have hstable : (prefixWord ++ tailWord_1970744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970744).length < 2 ^ (prefixWord ++ tailWord_1970744).sum := by decide
  have hdescent : baseEnd_1970744 < baseStart_1970744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970748 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_1970748 : Nat := 118140960795 + 1970748 * 2 ^ 59
def prefixEnd_1970748 : Nat := 4983230072969 + 3 ^ 40 * 1970748 * 2
def baseEnd_1970748 : Nat := 1011940972886960673086701

theorem tailTrace_1970748 : CollatzResearch.WordTrace tailWord_1970748 prefixEnd_1970748 1011940972886960673086701 := by
  unfold tailWord_1970748
  simp only [CollatzResearch.WordTrace]
  refine ⟨35939542332162023903624449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47919389776216031871499265 35939542332162023903624449)
  ·
    refine ⟨26954656749121517927718337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35939542332162023903624449 26954656749121517927718337)
    ·
      refine ⟨20215992561841138445788753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26954656749121517927718337 20215992561841138445788753)
      ·
        refine ⟨15161994421380853834341565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20215992561841138445788753 15161994421380853834341565)
        ·
          refine ⟨5685747908017820187878087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15161994421380853834341565 5685747908017820187878087)
          ·
            refine ⟨8528621862026730281817131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685747908017820187878087 8528621862026730281817131)
            ·
              refine ⟨12792932793040095422725697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8528621862026730281817131 12792932793040095422725697)
              ·
                refine ⟨9594699594780071567044273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12792932793040095422725697 9594699594780071567044273)
                ·
                  refine ⟨7196024696085053675283205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9594699594780071567044273 7196024696085053675283205)
                  ·
                    refine ⟨1349254630515947564115601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7196024696085053675283205 1349254630515947564115601)
                    ·
                      refine ⟨1011940972886960673086701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349254630515947564115601 1011940972886960673086701)
                      ·
                        rfl

theorem cell23_1970748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_1970748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970748 prefixEnd_1970748 := by exact prefixLift 1970748
  have htrace : WordTrace (prefixWord ++ tailWord_1970748) baseStart_1970748 baseEnd_1970748 := by
    simpa [prefixWord, tailWord_1970748, baseEnd_1970748] using wordTrace_append hprefix tailTrace_1970748
  have hstable : (prefixWord ++ tailWord_1970748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970748).length < 2 ^ (prefixWord ++ tailWord_1970748).sum := by decide
  have hdescent : baseEnd_1970748 < baseStart_1970748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970751 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 3]
def baseStart_1970751 : Nat := 118140960795 + 1970751 * 2 ^ 59
def prefixEnd_1970751 : Nat := 4983230072969 + 3 ^ 40 * 1970751 * 2
def baseEnd_1970751 : Nat := 1011942513328924161349187

theorem tailTrace_1970751 : CollatzResearch.WordTrace tailWord_1970751 prefixEnd_1970751 1011942513328924161349187 := by
  unfold tailWord_1970751
  simp only [CollatzResearch.WordTrace]
  refine ⟨71879194083313179319608107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47919462722208786213072071 71879194083313179319608107)
  ·
    refine ⟨107818791124969768979412161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71879194083313179319608107 107818791124969768979412161)
    ·
      refine ⟨80864093343727326734559121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107818791124969768979412161 80864093343727326734559121)
      ·
        refine ⟨60648070007795495050919341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80864093343727326734559121 60648070007795495050919341)
        ·
          refine ⟨22743026252923310644094753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60648070007795495050919341 22743026252923310644094753)
          ·
            refine ⟨17057269689692482983071065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22743026252923310644094753 17057269689692482983071065)
            ·
              refine ⟨12792952267269362237303299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17057269689692482983071065 12792952267269362237303299)
              ·
                refine ⟨19189428400904043355954949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12792952267269362237303299 19189428400904043355954949)
                ·
                  refine ⟨3598017825169508129241553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19189428400904043355954949 3598017825169508129241553)
                  ·
                    refine ⟨2698513368877131096931165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3598017825169508129241553 2698513368877131096931165)
                    ·
                      refine ⟨1011942513328924161349187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2698513368877131096931165 1011942513328924161349187)
                      ·
                        rfl

theorem cell23_1970751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_1970751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970751 prefixEnd_1970751 := by exact prefixLift 1970751
  have htrace : WordTrace (prefixWord ++ tailWord_1970751) baseStart_1970751 baseEnd_1970751 := by
    simpa [prefixWord, tailWord_1970751, baseEnd_1970751] using wordTrace_append hprefix tailTrace_1970751
  have hstable : (prefixWord ++ tailWord_1970751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970751).length < 2 ^ (prefixWord ++ tailWord_1970751).sum := by decide
  have hdescent : baseEnd_1970751 < baseStart_1970751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970765 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_1970765 : Nat := 118140960795 + 1970765 * 2 ^ 59
def prefixEnd_1970765 : Nat := 4983230072969 + 3 ^ 40 * 1970765 * 2
def baseEnd_1970765 : Nat := 1011949702058087106574123

theorem tailTrace_1970765 : CollatzResearch.WordTrace tailWord_1970765 prefixEnd_1970765 1011949702058087106574123 := by
  unfold tailWord_1970765
  simp only [CollatzResearch.WordTrace]
  refine ⟨71879704705262459710617749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47919803136841639807078499 71879704705262459710617749)
  ·
    refine ⟨3369361158059177798935207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71879704705262459710617749 3369361158059177798935207)
    ·
      refine ⟨5054041737088766698402811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3369361158059177798935207 5054041737088766698402811)
      ·
        refine ⟨7581062605633150047604217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5054041737088766698402811 7581062605633150047604217)
        ·
          refine ⟨5685796954224862535703163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7581062605633150047604217 5685796954224862535703163)
          ·
            refine ⟨8528695431337293803554745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685796954224862535703163 8528695431337293803554745)
            ·
              refine ⟨6396521573502970352666059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8528695431337293803554745 6396521573502970352666059)
              ·
                refine ⟨9594782360254455528999089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6396521573502970352666059 9594782360254455528999089)
                ·
                  refine ⟨7196086770190841646749317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9594782360254455528999089 7196086770190841646749317)
                  ·
                    refine ⟨1349266269410782808765497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7196086770190841646749317 1349266269410782808765497)
                    ·
                      refine ⟨1011949702058087106574123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349266269410782808765497 1011949702058087106574123)
                      ·
                        rfl

theorem cell23_1970765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_1970765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970765 prefixEnd_1970765 := by exact prefixLift 1970765
  have htrace : WordTrace (prefixWord ++ tailWord_1970765) baseStart_1970765 baseEnd_1970765 := by
    simpa [prefixWord, tailWord_1970765, baseEnd_1970765] using wordTrace_append hprefix tailTrace_1970765
  have hstable : (prefixWord ++ tailWord_1970765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970765).length < 2 ^ (prefixWord ++ tailWord_1970765).sum := by decide
  have hdescent : baseEnd_1970765 < baseStart_1970765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970808 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 2, 3, 2]
def baseStart_1970808 : Nat := 118140960795 + 1970808 * 2 ^ 59
def prefixEnd_1970808 : Nat := 4983230072969 + 3 ^ 40 * 1970808 * 2
def baseEnd_1970808 : Nat := 1011971781726230438336425

theorem tailTrace_1970808 : CollatzResearch.WordTrace tailWord_1970808 prefixEnd_1970808 1011971781726230438336425 := by
  unfold tailWord_1970808
  simp only [CollatzResearch.WordTrace]
  refine ⟨35940636522053339027216539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47920848696071118702955385 35940636522053339027216539)
  ·
    refine ⟨53910954783080008540824809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35940636522053339027216539 53910954783080008540824809)
    ·
      refine ⟨40433216087310006405618607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53910954783080008540824809 40433216087310006405618607)
      ·
        refine ⟨60649824130965009608427911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40433216087310006405618607 60649824130965009608427911)
        ·
          refine ⟨90974736196447514412641867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60649824130965009608427911 90974736196447514412641867)
          ·
            refine ⟨136462104294671271618962801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90974736196447514412641867 136462104294671271618962801)
            ·
              refine ⟨102346578221003453714222101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136462104294671271618962801 102346578221003453714222101)
              ·
                refine ⟨4797495854109536892854161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102346578221003453714222101 4797495854109536892854161)
                ·
                  refine ⟨3598121890582152669640621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4797495854109536892854161 3598121890582152669640621)
                  ·
                    refine ⟨1349295708968307251115233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3598121890582152669640621 1349295708968307251115233)
                    ·
                      refine ⟨1011971781726230438336425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349295708968307251115233 1011971781726230438336425)
                      ·
                        rfl

theorem cell23_1970808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_1970808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970808 prefixEnd_1970808 := by exact prefixLift 1970808
  have htrace : WordTrace (prefixWord ++ tailWord_1970808) baseStart_1970808 baseEnd_1970808 := by
    simpa [prefixWord, tailWord_1970808, baseEnd_1970808] using wordTrace_append hprefix tailTrace_1970808
  have hstable : (prefixWord ++ tailWord_1970808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970808).length < 2 ^ (prefixWord ++ tailWord_1970808).sum := by decide
  have hdescent : baseEnd_1970808 < baseStart_1970808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970848 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 1, 6]
def baseStart_1970848 : Nat := 118140960795 + 1970848 * 2 ^ 59
def prefixEnd_1970848 : Nat := 4983230072969 + 3 ^ 40 * 1970848 * 2
def baseEnd_1970848 : Nat := 337330773650803427278747

theorem tailTrace_1970848 : CollatzResearch.WordTrace tailWord_1970848 prefixEnd_1970848 337330773650803427278747 := by
  unfold tailWord_1970848
  simp only [CollatzResearch.WordTrace]
  refine ⟨35941365981980882442944599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47921821309307843257259465 35941365981980882442944599)
  ·
    refine ⟨53912048972971323664416899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35941365981980882442944599 53912048972971323664416899)
    ·
      refine ⟨80868073459456985496625349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53912048972971323664416899 80868073459456985496625349)
      ·
        refine ⟨15162763773648184780617253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80868073459456985496625349 15162763773648184780617253)
        ·
          refine ⟨2843018207559034646365735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15162763773648184780617253 2843018207559034646365735)
          ·
            refine ⟨4264527311338551969548603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843018207559034646365735 4264527311338551969548603)
            ·
              refine ⟨6396790967007827954322905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264527311338551969548603 6396790967007827954322905)
              ·
                refine ⟨4797593225255870965742179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6396790967007827954322905 4797593225255870965742179)
                ·
                  refine ⟨7196389837883806448613269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797593225255870965742179 7196389837883806448613269)
                  ·
                    refine ⟨337330773650803427278747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7196389837883806448613269 337330773650803427278747)
                    ·
                      rfl

theorem cell23_1970848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_1970848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970848 prefixEnd_1970848 := by exact prefixLift 1970848
  have htrace : WordTrace (prefixWord ++ tailWord_1970848) baseStart_1970848 baseEnd_1970848 := by
    simpa [prefixWord, tailWord_1970848, baseEnd_1970848] using wordTrace_append hprefix tailTrace_1970848
  have hstable : (prefixWord ++ tailWord_1970848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970848).length < 2 ^ (prefixWord ++ tailWord_1970848).sum := by decide
  have hdescent : baseEnd_1970848 < baseStart_1970848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970861 : List Nat := [1, 5, 2, 1, 1, 13]
def baseStart_1970861 : Nat := 118140960795 + 1970861 * 2 ^ 59
def prefixEnd_1970861 : Nat := 4983230072969 + 3 ^ 40 * 1970861 * 2
def baseEnd_1970861 : Nat := 4164604922637525641867

theorem tailTrace_1970861 : CollatzResearch.WordTrace tailWord_1970861 prefixEnd_1970861 4164604922637525641867 := by
  unfold tailWord_1970861
  simp only [CollatzResearch.WordTrace]
  refine ⟨71883206112914668106112437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47922137408609778737408291 71883206112914668106112437)
  ·
    refine ⟨6739050573085750134948041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71883206112914668106112437 6739050573085750134948041)
    ·
      refine ⟨5054287929814312601211031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6739050573085750134948041 5054287929814312601211031)
      ·
        refine ⟨7581431894721468901816547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5054287929814312601211031 7581431894721468901816547)
        ·
          refine ⟨11372147842082203352724821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7581431894721468901816547 11372147842082203352724821)
          ·
            refine ⟨4164604922637525641867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 11372147842082203352724821 4164604922637525641867)
            ·
              rfl

theorem cell23_1970861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 13].length) (baseStart_1970861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970861 prefixEnd_1970861 := by exact prefixLift 1970861
  have htrace : WordTrace (prefixWord ++ tailWord_1970861) baseStart_1970861 baseEnd_1970861 := by
    simpa [prefixWord, tailWord_1970861, baseEnd_1970861] using wordTrace_append hprefix tailTrace_1970861
  have hstable : (prefixWord ++ tailWord_1970861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970861).length < 2 ^ (prefixWord ++ tailWord_1970861).sum := by decide
  have hdescent : baseEnd_1970861 < baseStart_1970861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970888 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_1970888 : Nat := 118140960795 + 1970888 * 2 ^ 59
def prefixEnd_1970888 : Nat := 4983230072969 + 3 ^ 40 * 1970888 * 2
def baseEnd_1970888 : Nat := 1012012860178590125336057

theorem tailTrace_1970888 : CollatzResearch.WordTrace tailWord_1970888 prefixEnd_1970888 1012012860178590125336057 := by
  unfold tailWord_1970888
  simp only [CollatzResearch.WordTrace]
  refine ⟨35942095441908425858672659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47922793922544567811563545 35942095441908425858672659)
  ·
    refine ⟨53913143162862638788008989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35942095441908425858672659 53913143162862638788008989)
    ·
      refine ⟨20217428686073489545503371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53913143162862638788008989 20217428686073489545503371)
      ·
        refine ⟨30326143029110234318255057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20217428686073489545503371 30326143029110234318255057)
        ·
          refine ⟨22744607271832675738691293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30326143029110234318255057 22744607271832675738691293)
          ·
            refine ⟨8529227726937253402009235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22744607271832675738691293 8529227726937253402009235)
            ·
              refine ⟨12793841590405880103013853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529227726937253402009235 12793841590405880103013853)
              ·
                refine ⟨4797690596402205038630195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12793841590405880103013853 4797690596402205038630195)
                ·
                  refine ⟨7196535894603307557945293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797690596402205038630195 7196535894603307557945293)
                  ·
                    refine ⟨2698700960476240334229485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7196535894603307557945293 2698700960476240334229485)
                    ·
                      refine ⟨1012012860178590125336057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2698700960476240334229485 1012012860178590125336057)
                      ·
                        rfl

theorem cell23_1970888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_1970888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970888 prefixEnd_1970888 := by exact prefixLift 1970888
  have htrace : WordTrace (prefixWord ++ tailWord_1970888) baseStart_1970888 baseEnd_1970888 := by
    simpa [prefixWord, tailWord_1970888, baseEnd_1970888] using wordTrace_append hprefix tailTrace_1970888
  have hstable : (prefixWord ++ tailWord_1970888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970888).length < 2 ^ (prefixWord ++ tailWord_1970888).sum := by decide
  have hdescent : baseEnd_1970888 < baseStart_1970888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970921 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 2, 6]
def baseStart_1970921 : Nat := 118140960795 + 1970921 * 2 ^ 59
def prefixEnd_1970921 : Nat := 4983230072969 + 3 ^ 40 * 1970921 * 2
def baseEnd_1970921 : Nat := 337343268346729498741135

theorem tailTrace_1970921 : CollatzResearch.WordTrace tailWord_1970921 prefixEnd_1970921 337343268346729498741135 := by
  unfold tailWord_1970921
  simp only [CollatzResearch.WordTrace]
  refine ⟨71885394492697298353296617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47923596328464865568864411 71885394492697298353296617)
  ·
    refine ⟨53914045869522973764972463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71885394492697298353296617 53914045869522973764972463)
    ·
      refine ⟨80871068804284460647458695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53914045869522973764972463 80871068804284460647458695)
      ·
        refine ⟨121306603206426690971188043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80871068804284460647458695 121306603206426690971188043)
        ·
          refine ⟨181959904809640036456782065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121306603206426690971188043 181959904809640036456782065)
          ·
            refine ⟨136469928607230027342586549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181959904809640036456782065 136469928607230027342586549)
            ·
              refine ⟨12794055806927815063367489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136469928607230027342586549 12794055806927815063367489)
              ·
                refine ⟨9595541855195861297525617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12794055806927815063367489 9595541855195861297525617)
                ·
                  refine ⟨7196656391396895973144213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9595541855195861297525617 7196656391396895973144213)
                  ·
                    refine ⟨337343268346729498741135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7196656391396895973144213 337343268346729498741135)
                    ·
                      rfl

theorem cell23_1970921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_1970921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970921 prefixEnd_1970921 := by exact prefixLift 1970921
  have htrace : WordTrace (prefixWord ++ tailWord_1970921) baseStart_1970921 baseEnd_1970921 := by
    simpa [prefixWord, tailWord_1970921, baseEnd_1970921] using wordTrace_append hprefix tailTrace_1970921
  have hstable : (prefixWord ++ tailWord_1970921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970921).length < 2 ^ (prefixWord ++ tailWord_1970921).sum := by decide
  have hdescent : baseEnd_1970921 < baseStart_1970921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970931 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 5]
def baseStart_1970931 : Nat := 118140960795 + 1970931 * 2 ^ 59
def prefixEnd_1970931 : Nat := 4983230072969 + 3 ^ 40 * 1970931 * 2
def baseEnd_1970931 : Nat := 1012034939846733457098359

theorem tailTrace_1970931 : CollatzResearch.WordTrace tailWord_1970931 prefixEnd_1970931 1012034939846733457098359 := by
  unfold tailWord_1970931
  simp only [CollatzResearch.WordTrace]
  refine ⟨71885759222661070061160647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47923839481774046707440431 71885759222661070061160647)
  ·
    refine ⟨107828638833991605091740971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71885759222661070061160647 107828638833991605091740971)
    ·
      refine ⟨161742958250987407637611457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107828638833991605091740971 161742958250987407637611457)
      ·
        refine ⟨121307218688240555728208593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161742958250987407637611457 121307218688240555728208593)
        ·
          refine ⟨90980414016180416796156445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121307218688240555728208593 90980414016180416796156445)
          ·
            refine ⟨34117655256067656298558667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90980414016180416796156445 34117655256067656298558667)
            ·
              refine ⟨51176482884101484447838001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34117655256067656298558667 51176482884101484447838001)
              ·
                refine ⟨38382362163076113335878501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51176482884101484447838001 38382362163076113335878501)
                ·
                  refine ⟨7196692905576771250477219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38382362163076113335878501 7196692905576771250477219)
                  ·
                    refine ⟨10795039358365156875715829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7196692905576771250477219 10795039358365156875715829)
                    ·
                      refine ⟨1012034939846733457098359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10795039358365156875715829 1012034939846733457098359)
                      ·
                        rfl

theorem cell23_1970931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_1970931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970931 prefixEnd_1970931 := by exact prefixLift 1970931
  have htrace : WordTrace (prefixWord ++ tailWord_1970931) baseStart_1970931 baseEnd_1970931 := by
    simpa [prefixWord, tailWord_1970931, baseEnd_1970931] using wordTrace_append hprefix tailTrace_1970931
  have hstable : (prefixWord ++ tailWord_1970931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970931).length < 2 ^ (prefixWord ++ tailWord_1970931).sum := by decide
  have hdescent : baseEnd_1970931 < baseStart_1970931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970948 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1970948 : Nat := 118140960795 + 1970948 * 2 ^ 59
def prefixEnd_1970948 : Nat := 4983230072969 + 3 ^ 40 * 1970948 * 2
def baseEnd_1970948 : Nat := 1012043669017859890585781

theorem tailTrace_1970948 : CollatzResearch.WordTrace tailWord_1970948 prefixEnd_1970948 1012043669017859890585781 := by
  unfold tailWord_1970948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35943189631799740982264749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47924252842399654643019665 35943189631799740982264749)
  ·
    refine ⟨13478696111924902868349281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35943189631799740982264749 13478696111924902868349281)
    ·
      refine ⟨10109022083943677151261961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13478696111924902868349281 10109022083943677151261961)
      ·
        refine ⟨7581766562957757863446471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10109022083943677151261961 7581766562957757863446471)
        ·
          refine ⟨11372649844436636795169707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7581766562957757863446471 11372649844436636795169707)
          ·
            refine ⟨17058974766654955192754561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11372649844436636795169707 17058974766654955192754561)
            ·
              refine ⟨12794231074991216394565921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17058974766654955192754561 12794231074991216394565921)
              ·
                refine ⟨9595673306243412295924441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12794231074991216394565921 9595673306243412295924441)
                ·
                  refine ⟨7196754979682559221943331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9595673306243412295924441 7196754979682559221943331)
                  ·
                    refine ⟨10795132469523838832914997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7196754979682559221943331 10795132469523838832914997)
                    ·
                      refine ⟨1012043669017859890585781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10795132469523838832914997 1012043669017859890585781)
                      ·
                        rfl

theorem cell23_1970948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1970948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970948 prefixEnd_1970948 := by exact prefixLift 1970948
  have htrace : WordTrace (prefixWord ++ tailWord_1970948) baseStart_1970948 baseEnd_1970948 := by
    simpa [prefixWord, tailWord_1970948, baseEnd_1970948] using wordTrace_append hprefix tailTrace_1970948
  have hstable : (prefixWord ++ tailWord_1970948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970948).length < 2 ^ (prefixWord ++ tailWord_1970948).sum := by decide
  have hdescent : baseEnd_1970948 < baseStart_1970948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970996 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_1970996 : Nat := 118140960795 + 1970996 * 2 ^ 59
def prefixEnd_1970996 : Nat := 4983230072969 + 3 ^ 40 * 1970996 * 2
def baseEnd_1970996 : Nat := 1012068316089275702785561

theorem tailTrace_1970996 : CollatzResearch.WordTrace tailWord_1970996 prefixEnd_1970996 1012068316089275702785561 := by
  unfold tailWord_1970996
  simp only [CollatzResearch.WordTrace]
  refine ⟨35944064983712793081138421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47925419978283724108184561 35944064983712793081138421)
  ·
    refine ⟨3369756092223074351356727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35944064983712793081138421 3369756092223074351356727)
    ·
      refine ⟨5054634138334611527035091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3369756092223074351356727 5054634138334611527035091)
      ·
        refine ⟨7581951207501917290552637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5054634138334611527035091 7581951207501917290552637)
        ·
          refine ⟨2843231702813218983957239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7581951207501917290552637 2843231702813218983957239)
          ·
            refine ⟨4264847554219828475935859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843231702813218983957239 4264847554219828475935859)
            ·
              refine ⟨6397271331329742713903789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264847554219828475935859 6397271331329742713903789)
              ·
                refine ⟨2398976749248653517713921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6397271331329742713903789 2398976749248653517713921)
                ·
                  refine ⟨1799232561936490138285441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2398976749248653517713921 1799232561936490138285441)
                  ·
                    refine ⟨1349424421452367603714081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1799232561936490138285441 1349424421452367603714081)
                    ·
                      refine ⟨1012068316089275702785561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349424421452367603714081 1012068316089275702785561)
                      ·
                        rfl

theorem cell23_1970996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_1970996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1970996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1970996 prefixEnd_1970996 := by exact prefixLift 1970996
  have htrace : WordTrace (prefixWord ++ tailWord_1970996) baseStart_1970996 baseEnd_1970996 := by
    simpa [prefixWord, tailWord_1970996, baseEnd_1970996] using wordTrace_append hprefix tailTrace_1970996
  have hstable : (prefixWord ++ tailWord_1970996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970996).length < 2 ^ (prefixWord ++ tailWord_1970996).sum := by decide
  have hdescent : baseEnd_1970996 < baseStart_1970996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971062 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1971062 : Nat := 118140960795 + 1971062 * 2 ^ 59
def prefixEnd_1971062 : Nat := 4983230072969 + 3 ^ 40 * 1971062 * 2
def baseEnd_1971062 : Nat := 337367401937490814853419

theorem tailTrace_1971062 : CollatzResearch.WordTrace tailWord_1971062 prefixEnd_1971062 337367401937490814853419 := by
  unfold tailWord_1971062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4493158574074154964636215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47927024790124319622786293 4493158574074154964636215)
  ·
    refine ⟨6739737861111232446954323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4493158574074154964636215 6739737861111232446954323)
    ·
      refine ⟨10109606791666848670431485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6739737861111232446954323 10109606791666848670431485)
      ·
        refine ⟨3791102546875068251411807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10109606791666848670431485 3791102546875068251411807)
        ·
          refine ⟨5686653820312602377117711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791102546875068251411807 5686653820312602377117711)
          ·
            refine ⟨8529980730468903565676567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686653820312602377117711 8529980730468903565676567)
            ·
              refine ⟨12794971095703355348514851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529980730468903565676567 12794971095703355348514851)
              ·
                refine ⟨19192456643555033022772277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12794971095703355348514851 19192456643555033022772277)
                ·
                  refine ⟨1799292810333284345884901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19192456643555033022772277 1799292810333284345884901)
                  ·
                    refine ⟨337367401937490814853419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1799292810333284345884901 337367401937490814853419)
                    ·
                      rfl

theorem cell23_1971062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1971062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971062 prefixEnd_1971062 := by exact prefixLift 1971062
  have htrace : WordTrace (prefixWord ++ tailWord_1971062) baseStart_1971062 baseEnd_1971062 := by
    simpa [prefixWord, tailWord_1971062, baseEnd_1971062] using wordTrace_append hprefix tailTrace_1971062
  have hstable : (prefixWord ++ tailWord_1971062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971062).length < 2 ^ (prefixWord ++ tailWord_1971062).sum := by decide
  have hdescent : baseEnd_1971062 < baseStart_1971062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971079 : List Nat := [1, 1, 4, 2, 3, 2, 2, 3, 1, 4]
def baseStart_1971079 : Nat := 118140960795 + 1971079 * 2 ^ 59
def prefixEnd_1971079 : Nat := 4983230072969 + 3 ^ 40 * 1971079 * 2
def baseEnd_1971079 : Nat := 337370311661199626015893

theorem tailTrace_1971079 : CollatzResearch.WordTrace tailWord_1971079 prefixEnd_1971079 337370311661199626015893 := by
  unfold tailWord_1971079
  simp only [CollatzResearch.WordTrace]
  refine ⟨71891157226124891337548291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47927438150749927558365527 71891157226124891337548291)
  ·
    refine ⟨107836735839187337006322437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71891157226124891337548291 107836735839187337006322437)
    ·
      refine ⟨20219387969847625688685457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107836735839187337006322437 20219387969847625688685457)
      ·
        refine ⟨15164540977385719266514093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20219387969847625688685457 15164540977385719266514093)
        ·
          refine ⟨5686702866519644724942785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15164540977385719266514093 5686702866519644724942785)
          ·
            refine ⟨4265027149889733543707089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5686702866519644724942785 4265027149889733543707089)
            ·
              refine ⟨3198770362417300157780317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4265027149889733543707089 3198770362417300157780317)
              ·
                refine ⟨1199538885906487559167619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3198770362417300157780317 1199538885906487559167619)
                ·
                  refine ⟨1799308328859731338751429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199538885906487559167619 1799308328859731338751429)
                  ·
                    refine ⟨337370311661199626015893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1799308328859731338751429 337370311661199626015893)
                    ·
                      rfl

theorem cell23_1971079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_1971079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971079 prefixEnd_1971079 := by exact prefixLift 1971079
  have htrace : WordTrace (prefixWord ++ tailWord_1971079) baseStart_1971079 baseEnd_1971079 := by
    simpa [prefixWord, tailWord_1971079, baseEnd_1971079] using wordTrace_append hprefix tailTrace_1971079
  have hstable : (prefixWord ++ tailWord_1971079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971079).length < 2 ^ (prefixWord ++ tailWord_1971079).sum := by decide
  have hdescent : baseEnd_1971079 < baseStart_1971079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971136 : List Nat := [2, 1, 1, 2, 3, 5, 1, 3, 1, 1, 3]
def baseStart_1971136 : Nat := 118140960795 + 1971136 * 2 ^ 59
def prefixEnd_1971136 : Nat := 4983230072969 + 3 ^ 40 * 1971136 * 2
def baseEnd_1971136 : Nat := 1012140203380905155034917

theorem tailTrace_1971136 : CollatzResearch.WordTrace tailWord_1971136 prefixEnd_1971136 1012140203380905155034917 := by
  unfold tailWord_1971136
  simp only [CollatzResearch.WordTrace]
  refine ⟨35946618093459195036186631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47928824124612260048248841 35946618093459195036186631)
  ·
    refine ⟨53919927140188792554279947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35946618093459195036186631 53919927140188792554279947)
    ·
      refine ⟨80879890710283188831419921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53919927140188792554279947 80879890710283188831419921)
      ·
        refine ⟨60659918032712391623564941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80879890710283188831419921 60659918032712391623564941)
        ·
          refine ⟨22747469262267146858836853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60659918032712391623564941 22747469262267146858836853)
          ·
            refine ⟨2132575243337545018015955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22747469262267146858836853 2132575243337545018015955)
            ·
              refine ⟨3198862865006317527023933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132575243337545018015955 3198862865006317527023933)
              ·
                refine ⟨1199573574377369072633975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3198862865006317527023933 1199573574377369072633975)
                ·
                  refine ⟨1799360361566053608950963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199573574377369072633975 1799360361566053608950963)
                  ·
                    refine ⟨2699040542349080413426445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1799360361566053608950963 2699040542349080413426445)
                    ·
                      refine ⟨1012140203380905155034917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2699040542349080413426445 1012140203380905155034917)
                      ·
                        rfl

theorem cell23_1971136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 1, 3].length) (baseStart_1971136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971136 prefixEnd_1971136 := by exact prefixLift 1971136
  have htrace : WordTrace (prefixWord ++ tailWord_1971136) baseStart_1971136 baseEnd_1971136 := by
    simpa [prefixWord, tailWord_1971136, baseEnd_1971136] using wordTrace_append hprefix tailTrace_1971136
  have hstable : (prefixWord ++ tailWord_1971136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971136).length < 2 ^ (prefixWord ++ tailWord_1971136).sum := by decide
  have hdescent : baseEnd_1971136 < baseStart_1971136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971165 : List Nat := [1, 4, 3, 1, 2, 1, 1, 10]
def baseStart_1971165 : Nat := 118140960795 + 1971165 * 2 ^ 59
def prefixEnd_1971165 : Nat := 4983230072969 + 3 ^ 40 * 1971165 * 2
def baseEnd_1971165 : Nat := 37487225715551316354529

theorem tailTrace_1971165 : CollatzResearch.WordTrace tailWord_1971165 prefixEnd_1971165 37487225715551316354529 := by
  unfold tailWord_1971165
  simp only [CollatzResearch.WordTrace]
  refine ⟨71894293903813328025178949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47929529269208885350119299 71894293903813328025178949)
  ·
    refine ⟨13480180106964999004721053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71894293903813328025178949 13480180106964999004721053)
    ·
      refine ⟨5055067540111874626770395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13480180106964999004721053 5055067540111874626770395)
      ·
        refine ⟨7582601310167811940155593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5055067540111874626770395 7582601310167811940155593)
        ·
          refine ⟨5686950982625858955116695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7582601310167811940155593 5686950982625858955116695)
          ·
            refine ⟨8530426473938788432675043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686950982625858955116695 8530426473938788432675043)
            ·
              refine ⟨12795639710908182649012565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8530426473938788432675043 12795639710908182649012565)
              ·
                refine ⟨37487225715551316354529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12795639710908182649012565 37487225715551316354529)
                ·
                  rfl

theorem cell23_1971165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 10].length) (baseStart_1971165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971165 prefixEnd_1971165 := by exact prefixLift 1971165
  have htrace : WordTrace (prefixWord ++ tailWord_1971165) baseStart_1971165 baseEnd_1971165 := by
    simpa [prefixWord, tailWord_1971165, baseEnd_1971165] using wordTrace_append hprefix tailTrace_1971165
  have hstable : (prefixWord ++ tailWord_1971165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971165).length < 2 ^ (prefixWord ++ tailWord_1971165).sum := by decide
  have hdescent : baseEnd_1971165 < baseStart_1971165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971210 : List Nat := [3, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2]
def baseStart_1971210 : Nat := 118140960795 + 1971210 * 2 ^ 59
def prefixEnd_1971210 : Nat := 4983230072969 + 3 ^ 40 * 1971210 * 2
def baseEnd_1971210 : Nat := 1012178200949337865509577

theorem tailTrace_1971210 : CollatzResearch.WordTrace tailWord_1971210 prefixEnd_1971210 1012178200949337865509577 := by
  unfold tailWord_1971210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17973983797162575177641771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47930623459100200473711389 17973983797162575177641771)
  ·
    refine ⟨26960975695743862766462657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17973983797162575177641771 26960975695743862766462657)
    ·
      refine ⟨20220731771807897074846993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26960975695743862766462657 20220731771807897074846993)
      ·
        refine ⟨15165548828855922806135245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20220731771807897074846993 15165548828855922806135245)
        ·
          refine ⟨5687080810820971052300717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15165548828855922806135245 5687080810820971052300717)
          ·
            refine ⟨2132655304057864144612769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5687080810820971052300717 2132655304057864144612769)
            ·
              refine ⟨1599491478043398108459577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132655304057864144612769 1599491478043398108459577)
              ·
                refine ⟨1199618608532548581344683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599491478043398108459577 1199618608532548581344683)
                ·
                  refine ⟨1799427912798822872017025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199618608532548581344683 1799427912798822872017025)
                  ·
                    refine ⟨1349570934599117154012769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1799427912798822872017025 1349570934599117154012769)
                    ·
                      refine ⟨1012178200949337865509577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349570934599117154012769 1012178200949337865509577)
                      ·
                        rfl

theorem cell23_1971210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_1971210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971210 prefixEnd_1971210 := by exact prefixLift 1971210
  have htrace : WordTrace (prefixWord ++ tailWord_1971210) baseStart_1971210 baseEnd_1971210 := by
    simpa [prefixWord, tailWord_1971210, baseEnd_1971210] using wordTrace_append hprefix tailTrace_1971210
  have hstable : (prefixWord ++ tailWord_1971210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971210).length < 2 ^ (prefixWord ++ tailWord_1971210).sum := by decide
  have hdescent : baseEnd_1971210 < baseStart_1971210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971249 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 4, 2, 2]
def baseStart_1971249 : Nat := 118140960795 + 1971249 * 2 ^ 59
def prefixEnd_1971249 : Nat := 4983230072969 + 3 ^ 40 * 1971249 * 2
def baseEnd_1971249 : Nat := 1012198226694863212921897

theorem tailTrace_1971249 : CollatzResearch.WordTrace tailWord_1971249 prefixEnd_1971249 1012198226694863212921897 := by
  unfold tailWord_1971249
  simp only [CollatzResearch.WordTrace]
  refine ⟨71897357635509010371236801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47931571757006006914157867 71897357635509010371236801)
  ·
    refine ⟨53923018226631757778427601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71897357635509010371236801 53923018226631757778427601)
    ·
      refine ⟨40442263669973818333820701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53923018226631757778427601 40442263669973818333820701)
      ·
        refine ⟨15165848876240181875182763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40442263669973818333820701 15165848876240181875182763)
        ·
          refine ⟨22748773314360272812774145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15165848876240181875182763 22748773314360272812774145)
          ·
            refine ⟨17061579985770204609580609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22748773314360272812774145 17061579985770204609580609)
            ·
              refine ⟨12796184989327653457185457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17061579985770204609580609 12796184989327653457185457)
              ·
                refine ⟨9597138741995740092889093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12796184989327653457185457 9597138741995740092889093)
                ·
                  refine ⟨1799463514124201267416705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9597138741995740092889093 1799463514124201267416705)
                  ·
                    refine ⟨1349597635593150950562529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1799463514124201267416705 1349597635593150950562529)
                    ·
                      refine ⟨1012198226694863212921897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349597635593150950562529 1012198226694863212921897)
                      ·
                        rfl

theorem cell23_1971249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_1971249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971249 prefixEnd_1971249 := by exact prefixLift 1971249
  have htrace : WordTrace (prefixWord ++ tailWord_1971249) baseStart_1971249 baseEnd_1971249 := by
    simpa [prefixWord, tailWord_1971249, baseEnd_1971249] using wordTrace_append hprefix tailTrace_1971249
  have hstable : (prefixWord ++ tailWord_1971249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971249).length < 2 ^ (prefixWord ++ tailWord_1971249).sum := by decide
  have hdescent : baseEnd_1971249 < baseStart_1971249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971272 : List Nat := [2, 1, 3, 1, 1, 1, 3, 6, 5]
def baseStart_1971272 : Nat := 118140960795 + 1971272 * 2 ^ 59
def prefixEnd_1971272 : Nat := 4983230072969 + 3 ^ 40 * 1971272 * 2
def baseEnd_1971272 : Nat := 112467781861101846992699

theorem tailTrace_1971272 : CollatzResearch.WordTrace tailWord_1971272 prefixEnd_1971272 112467781861101846992699 := by
  unfold tailWord_1971272
  simp only [CollatzResearch.WordTrace]
  refine ⟨35949098257212842649662035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47932131009617123532882713 35949098257212842649662035)
  ·
    refine ⟨53923647385819263974493053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35949098257212842649662035 53923647385819263974493053)
    ·
      refine ⟨20221367769682223990434895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53923647385819263974493053 20221367769682223990434895)
      ·
        refine ⟨30332051654523335985652343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20221367769682223990434895 30332051654523335985652343)
        ·
          refine ⟨45498077481785003978478515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30332051654523335985652343 45498077481785003978478515)
          ·
            refine ⟨68247116222677505967717773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45498077481785003978478515 68247116222677505967717773)
            ·
              refine ⟨25592668583504064737894165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68247116222677505967717773 25592668583504064737894165)
              ·
                refine ⟨1199656339851753034588789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25592668583504064737894165 1199656339851753034588789)
                ·
                  refine ⟨112467781861101846992699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1199656339851753034588789 112467781861101846992699)
                  ·
                    rfl

theorem cell23_1971272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 5].length) (baseStart_1971272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971272 prefixEnd_1971272 := by exact prefixLift 1971272
  have htrace : WordTrace (prefixWord ++ tailWord_1971272) baseStart_1971272 baseEnd_1971272 := by
    simpa [prefixWord, tailWord_1971272, baseEnd_1971272] using wordTrace_append hprefix tailTrace_1971272
  have hstable : (prefixWord ++ tailWord_1971272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971272).length < 2 ^ (prefixWord ++ tailWord_1971272).sum := by decide
  have hdescent : baseEnd_1971272 < baseStart_1971272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971285 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_1971285 : Nat := 118140960795 + 1971285 * 2 ^ 59
def prefixEnd_1971285 : Nat := 4983230072969 + 3 ^ 40 * 1971285 * 2
def baseEnd_1971285 : Nat := 337405570666141690690577

theorem tailTrace_1971285 : CollatzResearch.WordTrace tailWord_1971285 prefixEnd_1971285 337405570666141690690577 := by
  unfold tailWord_1971285
  simp only [CollatzResearch.WordTrace]
  refine ⟨71898670663378588519547309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47932447108919059013031539 71898670663378588519547309)
  ·
    refine ⟨26962001498766970694830241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71898670663378588519547309 26962001498766970694830241)
    ·
      refine ⟨20221501124075228021122681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26962001498766970694830241 20221501124075228021122681)
      ·
        refine ⟨15166125843056421015842011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20221501124075228021122681 15166125843056421015842011)
        ·
          refine ⟨22749188764584631523763017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15166125843056421015842011 22749188764584631523763017)
          ·
            refine ⟨17061891573438473642822263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22749188764584631523763017 17061891573438473642822263)
            ·
              refine ⟨25592837360157710464233395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17061891573438473642822263 25592837360157710464233395)
              ·
                refine ⟨38389256040236565696350093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25592837360157710464233395 38389256040236565696350093)
                ·
                  refine ⟨14395971015088712136131285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38389256040236565696350093 14395971015088712136131285)
                  ·
                    refine ⟨337405570666141690690577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14395971015088712136131285 337405570666141690690577)
                    ·
                      rfl

theorem cell23_1971285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_1971285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971285 prefixEnd_1971285 := by exact prefixLift 1971285
  have htrace : WordTrace (prefixWord ++ tailWord_1971285) baseStart_1971285 baseEnd_1971285 := by
    simpa [prefixWord, tailWord_1971285, baseEnd_1971285] using wordTrace_append hprefix tailTrace_1971285
  have hstable : (prefixWord ++ tailWord_1971285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971285).length < 2 ^ (prefixWord ++ tailWord_1971285).sum := by decide
  have hdescent : baseEnd_1971285 < baseStart_1971285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971306 : List Nat := [3, 1, 3, 2, 2, 3, 1, 3, 5]
def baseStart_1971306 : Nat := 118140960795 + 1971306 * 2 ^ 59
def prefixEnd_1971306 : Nat := 4983230072969 + 3 ^ 40 * 1971306 * 2
def baseEnd_1971306 : Nat := 112469721676907721101015

theorem tailTrace_1971306 : CollatzResearch.WordTrace tailWord_1971306 prefixEnd_1971306 112469721676907721101015 := by
  unfold tailWord_1971306
  simp only [CollatzResearch.WordTrace]
  refine ⟨17974859149075627276515443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47932957730868339404041181 17974859149075627276515443)
  ·
    refine ⟨26962288723613440914773165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17974859149075627276515443 26962288723613440914773165)
    ·
      refine ⟨10110858271355040343039937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26962288723613440914773165 10110858271355040343039937)
      ·
        refine ⟨7583143703516280257279953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10110858271355040343039937 7583143703516280257279953)
        ·
          refine ⟨5687357777637210192959965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7583143703516280257279953 5687357777637210192959965)
          ·
            refine ⟨2132759166613953822359987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5687357777637210192959965 2132759166613953822359987)
            ·
              refine ⟨3199138749920930733539981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132759166613953822359987 3199138749920930733539981)
              ·
                refine ⟨1199677031220349025077493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3199138749920930733539981 1199677031220349025077493)
                ·
                  refine ⟨112469721676907721101015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1199677031220349025077493 112469721676907721101015)
                  ·
                    rfl

theorem cell23_1971306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_1971306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971306 prefixEnd_1971306 := by exact prefixLift 1971306
  have htrace : WordTrace (prefixWord ++ tailWord_1971306) baseStart_1971306 baseEnd_1971306 := by
    simpa [prefixWord, tailWord_1971306, baseEnd_1971306] using wordTrace_append hprefix tailTrace_1971306
  have hstable : (prefixWord ++ tailWord_1971306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971306).length < 2 ^ (prefixWord ++ tailWord_1971306).sum := by decide
  have hdescent : baseEnd_1971306 < baseStart_1971306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971399 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_1971399 : Nat := 118140960795 + 1971399 * 2 ^ 59
def prefixEnd_1971399 : Nat := 4983230072969 + 3 ^ 40 * 1971399 * 2
def baseEnd_1971399 : Nat := 1012275248793037626046207

theorem tailTrace_1971399 : CollatzResearch.WordTrace tailWord_1971399 prefixEnd_1971399 1012275248793037626046207 := by
  unfold tailWord_1971399
  simp only [CollatzResearch.WordTrace]
  refine ⟨71902828584965585989197251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47935219056643723992798167 71902828584965585989197251)
  ·
    refine ⟨107854242877448378983795877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71902828584965585989197251 107854242877448378983795877)
    ·
      refine ⟨20222670539521571059461727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107854242877448378983795877 20222670539521571059461727)
      ·
        refine ⟨30334005809282356589192591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20222670539521571059461727 30334005809282356589192591)
        ·
          refine ⟨45501008713923534883788887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30334005809282356589192591 45501008713923534883788887)
          ·
            refine ⟨68251513070885302325683331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45501008713923534883788887 68251513070885302325683331)
            ·
              refine ⟨102377269606327953488524997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68251513070885302325683331 102377269606327953488524997)
              ·
                refine ⟨19195738051186491279098437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102377269606327953488524997 19195738051186491279098437)
                ·
                  refine ⟨3599200884597467114830957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19195738051186491279098437 3599200884597467114830957)
                  ·
                    refine ⟨1349700331724050168061609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599200884597467114830957 1349700331724050168061609)
                    ·
                      refine ⟨1012275248793037626046207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349700331724050168061609 1012275248793037626046207)
                      ·
                        rfl

theorem cell23_1971399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_1971399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971399 prefixEnd_1971399 := by exact prefixLift 1971399
  have htrace : WordTrace (prefixWord ++ tailWord_1971399) baseStart_1971399 baseEnd_1971399 := by
    simpa [prefixWord, tailWord_1971399, baseEnd_1971399] using wordTrace_append hprefix tailTrace_1971399
  have hstable : (prefixWord ++ tailWord_1971399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971399).length < 2 ^ (prefixWord ++ tailWord_1971399).sum := by decide
  have hdescent : baseEnd_1971399 < baseStart_1971399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971416 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 1, 5, 2]
def baseStart_1971416 : Nat := 118140960795 + 1971416 * 2 ^ 59
def prefixEnd_1971416 : Nat := 4983230072969 + 3 ^ 40 * 1971416 * 2
def baseEnd_1971416 : Nat := 1012283977964164059533629

theorem tailTrace_1971416 : CollatzResearch.WordTrace tailWord_1971416 prefixEnd_1971416 1012283977964164059533629 := by
  unfold tailWord_1971416
  simp only [CollatzResearch.WordTrace]
  refine ⟨35951724312951998946283051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47935632417269331928377401 35951724312951998946283051)
  ·
    refine ⟨53927586469427998419424577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35951724312951998946283051 53927586469427998419424577)
    ·
      refine ⟨40445689852070998814568433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53927586469427998419424577 40445689852070998814568433)
      ·
        refine ⟨30334267389053249110926325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40445689852070998814568433 30334267389053249110926325)
        ·
          refine ⟨2843837567723742104149343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30334267389053249110926325 2843837567723742104149343)
          ·
            refine ⟨4265756351585613156224015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843837567723742104149343 4265756351585613156224015)
            ·
              refine ⟨6398634527378419734336023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4265756351585613156224015 6398634527378419734336023)
              ·
                refine ⟨9597951791067629601504035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6398634527378419734336023 9597951791067629601504035)
                ·
                  refine ⟨14396927686601444402256053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9597951791067629601504035 14396927686601444402256053)
                  ·
                    refine ⟨1349711970618885412711505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14396927686601444402256053 1349711970618885412711505)
                    ·
                      refine ⟨1012283977964164059533629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349711970618885412711505 1012283977964164059533629)
                      ·
                        rfl

theorem cell23_1971416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_1971416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971416 prefixEnd_1971416 := by exact prefixLift 1971416
  have htrace : WordTrace (prefixWord ++ tailWord_1971416) baseStart_1971416 baseEnd_1971416 := by
    simpa [prefixWord, tailWord_1971416, baseEnd_1971416] using wordTrace_append hprefix tailTrace_1971416
  have hstable : (prefixWord ++ tailWord_1971416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971416).length < 2 ^ (prefixWord ++ tailWord_1971416).sum := by decide
  have hdescent : baseEnd_1971416 < baseStart_1971416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971459 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 4]
def baseStart_1971459 : Nat := 118140960795 + 1971459 * 2 ^ 59
def prefixEnd_1971459 : Nat := 4983230072969 + 3 ^ 40 * 1971459 * 2
def baseEnd_1971459 : Nat := 1012306057632307391295931

theorem tailTrace_1971459 : CollatzResearch.WordTrace tailWord_1971459 prefixEnd_1971459 1012306057632307391295931 := by
  unfold tailWord_1971459
  simp only [CollatzResearch.WordTrace]
  refine ⟨71905016964748216236381431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47936677976498810824254287 71905016964748216236381431)
  ·
    refine ⟨107857525447122324354572147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71905016964748216236381431 107857525447122324354572147)
    ·
      refine ⟨161786288170683486531858221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107857525447122324354572147 161786288170683486531858221)
      ·
        refine ⟨60669858064006307449446833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161786288170683486531858221 60669858064006307449446833)
        ·
          refine ⟨45502393548004730587085125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60669858064006307449446833 45502393548004730587085125)
          ·
            refine ⟨8531698790250886985078461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45502393548004730587085125 8531698790250886985078461)
            ·
              refine ⟨3199387046344082619404423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8531698790250886985078461 3199387046344082619404423)
              ·
                refine ⟨4799080569516123929106635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199387046344082619404423 4799080569516123929106635)
                ·
                  refine ⟨7198620854274185893659953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799080569516123929106635 7198620854274185893659953)
                  ·
                    refine ⟨5398965640705639420244965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7198620854274185893659953 5398965640705639420244965)
                    ·
                      refine ⟨1012306057632307391295931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5398965640705639420244965 1012306057632307391295931)
                      ·
                        rfl

theorem cell23_1971459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_1971459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971459 prefixEnd_1971459 := by exact prefixLift 1971459
  have htrace : WordTrace (prefixWord ++ tailWord_1971459) baseStart_1971459 baseEnd_1971459 := by
    simpa [prefixWord, tailWord_1971459, baseEnd_1971459] using wordTrace_append hprefix tailTrace_1971459
  have hstable : (prefixWord ++ tailWord_1971459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971459).length < 2 ^ (prefixWord ++ tailWord_1971459).sum := by decide
  have hdescent : baseEnd_1971459 < baseStart_1971459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971474 : List Nat := [3, 2, 4, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1971474 : Nat := 118140960795 + 1971474 * 2 ^ 59
def prefixEnd_1971474 : Nat := 4983230072969 + 3 ^ 40 * 1971474 * 2
def baseEnd_1971474 : Nat := 1012313759842124832608363

theorem tailTrace_1971474 : CollatzResearch.WordTrace tailWord_1971474 prefixEnd_1971474 1012313759842124832608363 := by
  unfold tailWord_1971474
  simp only [CollatzResearch.WordTrace]
  refine ⟨17976391014923468449544369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47937042706462582532118317 17976391014923468449544369)
  ·
    refine ⟨13482293261192601337158277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17976391014923468449544369 13482293261192601337158277)
    ·
      refine ⟨2527929986473612750717177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13482293261192601337158277 2527929986473612750717177)
      ·
        refine ⟨1895947489855209563037883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2527929986473612750717177 1895947489855209563037883)
        ·
          refine ⟨2843921234782814344556825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895947489855209563037883 2843921234782814344556825)
          ·
            refine ⟨2132940926087110758417619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2843921234782814344556825 2132940926087110758417619)
            ·
              refine ⟨3199411389130666137626429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132940926087110758417619 3199411389130666137626429)
              ·
                refine ⟨1199779270923999801609911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3199411389130666137626429 1199779270923999801609911)
                ·
                  refine ⟨1799668906385999702414867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199779270923999801609911 1799668906385999702414867)
                  ·
                    refine ⟨2699503359578999553622301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1799668906385999702414867 2699503359578999553622301)
                    ·
                      refine ⟨1012313759842124832608363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2699503359578999553622301 1012313759842124832608363)
                      ·
                        rfl

theorem cell23_1971474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1971474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971474 prefixEnd_1971474 := by exact prefixLift 1971474
  have htrace : WordTrace (prefixWord ++ tailWord_1971474) baseStart_1971474 baseEnd_1971474 := by
    simpa [prefixWord, tailWord_1971474, baseEnd_1971474] using wordTrace_append hprefix tailTrace_1971474
  have hstable : (prefixWord ++ tailWord_1971474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971474).length < 2 ^ (prefixWord ++ tailWord_1971474).sum := by decide
  have hdescent : baseEnd_1971474 < baseStart_1971474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971479 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1971479 : Nat := 118140960795 + 1971479 * 2 ^ 59
def prefixEnd_1971479 : Nat := 4983230072969 + 3 ^ 40 * 1971479 * 2
def baseEnd_1971479 : Nat := 1012316327245397313045839

theorem tailTrace_1971479 : CollatzResearch.WordTrace tailWord_1971479 prefixEnd_1971479 1012316327245397313045839 := by
  unfold tailWord_1971479
  simp only [CollatzResearch.WordTrace]
  refine ⟨71905746424675759652109491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47937164283117173101406327 71905746424675759652109491)
  ·
    refine ⟨107858619637013639478164237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71905746424675759652109491 107858619637013639478164237)
    ·
      refine ⟨40446982363880114804311589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107858619637013639478164237 40446982363880114804311589)
      ·
        refine ⟨7583809193227521525808423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40446982363880114804311589 7583809193227521525808423)
        ·
          refine ⟨11375713789841282288712635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7583809193227521525808423 11375713789841282288712635)
          ·
            refine ⟨17063570684761923433068953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11375713789841282288712635 17063570684761923433068953)
            ·
              refine ⟨12797678013571442574801715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17063570684761923433068953 12797678013571442574801715)
              ·
                refine ⟨19196517020357163862202573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12797678013571442574801715 19196517020357163862202573)
                ·
                  refine ⟨7198693882633936448325965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19196517020357163862202573 7198693882633936448325965)
                  ·
                    refine ⟨2699510205987726168122237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7198693882633936448325965 2699510205987726168122237)
                    ·
                      refine ⟨1012316327245397313045839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2699510205987726168122237 1012316327245397313045839)
                      ·
                        rfl

theorem cell23_1971479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1971479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971479 prefixEnd_1971479 := by exact prefixLift 1971479
  have htrace : WordTrace (prefixWord ++ tailWord_1971479) baseStart_1971479 baseEnd_1971479 := by
    simpa [prefixWord, tailWord_1971479, baseEnd_1971479] using wordTrace_append hprefix tailTrace_1971479
  have hstable : (prefixWord ++ tailWord_1971479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971479).length < 2 ^ (prefixWord ++ tailWord_1971479).sum := by decide
  have hdescent : baseEnd_1971479 < baseStart_1971479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971480 : List Nat := [2, 1, 2, 3, 1, 3, 3, 3, 1, 2, 2]
def baseStart_1971480 : Nat := 118140960795 + 1971480 * 2 ^ 59
def prefixEnd_1971480 : Nat := 4983230072969 + 3 ^ 40 * 1971480 * 2
def baseEnd_1971480 : Nat := 1012316840726051809133335

theorem tailTrace_1971480 : CollatzResearch.WordTrace tailWord_1971480 prefixEnd_1971480 1012316840726051809133335 := by
  unfold tailWord_1971480
  simp only [CollatzResearch.WordTrace]
  refine ⟨35952891448836068411447947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47937188598448091215263929 35952891448836068411447947)
  ·
    refine ⟨53929337173254102617171921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35952891448836068411447947 53929337173254102617171921)
    ·
      refine ⟨40447002879940576962878941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53929337173254102617171921 40447002879940576962878941)
      ·
        refine ⟨15167626079977716361079603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40447002879940576962878941 15167626079977716361079603)
        ·
          refine ⟨22751439119966574541619405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15167626079977716361079603 22751439119966574541619405)
          ·
            refine ⟨8531789669987465453107277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22751439119966574541619405 8531789669987465453107277)
            ·
              refine ⟨3199421126245299544915229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8531789669987465453107277 3199421126245299544915229)
              ·
                refine ⟨1199782922341987329343211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3199421126245299544915229 1199782922341987329343211)
                ·
                  refine ⟨1799674383512980994014817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199782922341987329343211 1799674383512980994014817)
                  ·
                    refine ⟨1349755787634735745511113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1799674383512980994014817 1349755787634735745511113)
                    ·
                      refine ⟨1012316840726051809133335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349755787634735745511113 1012316840726051809133335)
                      ·
                        rfl

theorem cell23_1971480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_1971480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971480 prefixEnd_1971480 := by exact prefixLift 1971480
  have htrace : WordTrace (prefixWord ++ tailWord_1971480) baseStart_1971480 baseEnd_1971480 := by
    simpa [prefixWord, tailWord_1971480, baseEnd_1971480] using wordTrace_append hprefix tailTrace_1971480
  have hstable : (prefixWord ++ tailWord_1971480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971480).length < 2 ^ (prefixWord ++ tailWord_1971480).sum := by decide
  have hdescent : baseEnd_1971480 < baseStart_1971480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971512 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 1, 8]
def baseStart_1971512 : Nat := 118140960795 + 1971512 * 2 ^ 59
def prefixEnd_1971512 : Nat := 4983230072969 + 3 ^ 40 * 1971512 * 2
def baseEnd_1971512 : Nat := 337444424035665227977729

theorem tailTrace_1971512 : CollatzResearch.WordTrace tailWord_1971512 prefixEnd_1971512 337444424035665227977729 := by
  unfold tailWord_1971512
  simp only [CollatzResearch.WordTrace]
  refine ⟨35953475016778103144030395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47937966689037470858707193 35953475016778103144030395)
  ·
    refine ⟨53930212525167154716045593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35953475016778103144030395 53930212525167154716045593)
    ·
      refine ⟨40447659393875366037034195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53930212525167154716045593 40447659393875366037034195)
      ·
        refine ⟨60671489090813049055551293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40447659393875366037034195 60671489090813049055551293)
        ·
          refine ⟨22751808409054893395831735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60671489090813049055551293 22751808409054893395831735)
          ·
            refine ⟨34127712613582340093747603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22751808409054893395831735 34127712613582340093747603)
            ·
              refine ⟨51191568920373510140621405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34127712613582340093747603 51191568920373510140621405)
              ·
                refine ⟨19196838345140066302733027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51191568920373510140621405 19196838345140066302733027)
                ·
                  refine ⟨28795257517710099454099541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19196838345140066302733027 28795257517710099454099541)
                  ·
                    refine ⟨337444424035665227977729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28795257517710099454099541 337444424035665227977729)
                    ·
                      rfl

theorem cell23_1971512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_1971512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971512 prefixEnd_1971512 := by exact prefixLift 1971512
  have htrace : WordTrace (prefixWord ++ tailWord_1971512) baseStart_1971512 baseEnd_1971512 := by
    simpa [prefixWord, tailWord_1971512, baseEnd_1971512] using wordTrace_append hprefix tailTrace_1971512
  have hstable : (prefixWord ++ tailWord_1971512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971512).length < 2 ^ (prefixWord ++ tailWord_1971512).sum := by decide
  have hdescent : baseEnd_1971512 < baseStart_1971512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971517 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1971517 : Nat := 118140960795 + 1971517 * 2 ^ 59
def prefixEnd_1971517 : Nat := 4983230072969 + 3 ^ 40 * 1971517 * 2
def baseEnd_1971517 : Nat := 1012335839510268164370665

theorem tailTrace_1971517 : CollatzResearch.WordTrace tailWord_1971517 prefixEnd_1971517 1012335839510268164370665 := by
  unfold tailWord_1971517
  simp only [CollatzResearch.WordTrace]
  refine ⟨71907132398538092141992805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47938088265692061427995203 71907132398538092141992805)
  ·
    refine ⟨13482587324725892276623651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71907132398538092141992805 13482587324725892276623651)
    ·
      refine ⟨20223880987088838414935477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13482587324725892276623651 20223880987088838414935477)
      ·
        refine ⟨1895988842539578601400201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20223880987088838414935477 1895988842539578601400201)
        ·
          refine ⟨1421991631904683951050151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1895988842539578601400201 1421991631904683951050151)
          ·
            refine ⟨2132987447857025926575227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421991631904683951050151 2132987447857025926575227)
            ·
              refine ⟨3199481171785538889862841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132987447857025926575227 3199481171785538889862841)
              ·
                refine ⟨2399610878839154167397131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3199481171785538889862841 2399610878839154167397131)
                ·
                  refine ⟨3599416318258731251095697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399610878839154167397131 3599416318258731251095697)
                  ·
                    refine ⟨2699562238694048438321773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599416318258731251095697 2699562238694048438321773)
                    ·
                      refine ⟨1012335839510268164370665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2699562238694048438321773 1012335839510268164370665)
                      ·
                        rfl

theorem cell23_1971517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1971517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971517 prefixEnd_1971517 := by exact prefixLift 1971517
  have htrace : WordTrace (prefixWord ++ tailWord_1971517) baseStart_1971517 baseEnd_1971517 := by
    simpa [prefixWord, tailWord_1971517, baseEnd_1971517] using wordTrace_append hprefix tailTrace_1971517
  have hstable : (prefixWord ++ tailWord_1971517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971517).length < 2 ^ (prefixWord ++ tailWord_1971517).sum := by decide
  have hdescent : baseEnd_1971517 < baseStart_1971517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971536 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 1, 4, 2]
def baseStart_1971536 : Nat := 118140960795 + 1971536 * 2 ^ 59
def prefixEnd_1971536 : Nat := 4983230072969 + 3 ^ 40 * 1971536 * 2
def baseEnd_1971536 : Nat := 1012345595642703590033077

theorem tailTrace_1971536 : CollatzResearch.WordTrace tailWord_1971536 prefixEnd_1971536 1012345595642703590033077 := by
  unfold tailWord_1971536
  simp only [CollatzResearch.WordTrace]
  refine ⟨35953912692734629193467231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47938550256979505591289641 35953912692734629193467231)
  ·
    refine ⟨53930869039101943790200847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35953912692734629193467231 53930869039101943790200847)
    ·
      refine ⟨80896303558652915685301271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53930869039101943790200847 80896303558652915685301271)
      ·
        refine ⟨121344455337979373527951907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80896303558652915685301271 121344455337979373527951907)
        ·
          refine ⟨182016683006969060291927861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121344455337979373527951907 182016683006969060291927861)
          ·
            refine ⟨17064064031903349402368237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182016683006969060291927861 17064064031903349402368237)
            ·
              refine ⟨6399024011963756025888089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17064064031903349402368237 6399024011963756025888089)
              ·
                refine ⟨4799268008972817019416067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6399024011963756025888089 4799268008972817019416067)
                ·
                  refine ⟨7198902013459225529124101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799268008972817019416067 7198902013459225529124101)
                  ·
                    refine ⟨1349794127523604786710769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7198902013459225529124101 1349794127523604786710769)
                    ·
                      refine ⟨1012345595642703590033077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349794127523604786710769 1012345595642703590033077)
                      ·
                        rfl

theorem cell23_1971536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 4, 2].length) (baseStart_1971536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971536 prefixEnd_1971536 := by exact prefixLift 1971536
  have htrace : WordTrace (prefixWord ++ tailWord_1971536) baseStart_1971536 baseEnd_1971536 := by
    simpa [prefixWord, tailWord_1971536, baseEnd_1971536] using wordTrace_append hprefix tailTrace_1971536
  have hstable : (prefixWord ++ tailWord_1971536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971536).length < 2 ^ (prefixWord ++ tailWord_1971536).sum := by decide
  have hdescent : baseEnd_1971536 < baseStart_1971536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971540 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_1971540 : Nat := 118140960795 + 1971540 * 2 ^ 59
def prefixEnd_1971540 : Nat := 4983230072969 + 3 ^ 40 * 1971540 * 2
def baseEnd_1971540 : Nat := 1012347649565321574383059

theorem tailTrace_1971540 : CollatzResearch.WordTrace tailWord_1971540 prefixEnd_1971540 1012347649565321574383059 := by
  unfold tailWord_1971540
  simp only [CollatzResearch.WordTrace]
  refine ⟨35953985638727383535040037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47938647518303178046720049 35953985638727383535040037)
  ·
    refine ⟨6741372307261384412820007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35953985638727383535040037 6741372307261384412820007)
    ·
      refine ⟨10112058460892076619230011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6741372307261384412820007 10112058460892076619230011)
      ·
        refine ⟨15168087691338114928845017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10112058460892076619230011 15168087691338114928845017)
        ·
          refine ⟨11376065768503586196633763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15168087691338114928845017 11376065768503586196633763)
          ·
            refine ⟨17064098652755379294950645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11376065768503586196633763 17064098652755379294950645)
            ·
              refine ⟨1599759248695816808901623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17064098652755379294950645 1599759248695816808901623)
              ·
                refine ⟨2399638873043725213352435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599759248695816808901623 2399638873043725213352435)
                ·
                  refine ⟨3599458309565587820028653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399638873043725213352435 3599458309565587820028653)
                  ·
                    refine ⟨1349796866087095432510745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599458309565587820028653 1349796866087095432510745)
                    ·
                      refine ⟨1012347649565321574383059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349796866087095432510745 1012347649565321574383059)
                      ·
                        rfl

theorem cell23_1971540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_1971540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971540 prefixEnd_1971540 := by exact prefixLift 1971540
  have htrace : WordTrace (prefixWord ++ tailWord_1971540) baseStart_1971540 baseEnd_1971540 := by
    simpa [prefixWord, tailWord_1971540, baseEnd_1971540] using wordTrace_append hprefix tailTrace_1971540
  have hstable : (prefixWord ++ tailWord_1971540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971540).length < 2 ^ (prefixWord ++ tailWord_1971540).sum := by decide
  have hdescent : baseEnd_1971540 < baseStart_1971540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971569 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_1971569 : Nat := 118140960795 + 1971569 * 2 ^ 59
def prefixEnd_1971569 : Nat := 4983230072969 + 3 ^ 40 * 1971569 * 2
def baseEnd_1971569 : Nat := 1012362540504301960920425

theorem tailTrace_1971569 : CollatzResearch.WordTrace tailWord_1971569 prefixEnd_1971569 1012362540504301960920425 := by
  unfold tailWord_1971569
  simp only [CollatzResearch.WordTrace]
  refine ⟨71909028994349705022885761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47939352662899803348590507 71909028994349705022885761)
  ·
    refine ⟨53931771745762278767164321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71909028994349705022885761 53931771745762278767164321)
    ·
      refine ⟨40448828809321709075373241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53931771745762278767164321 40448828809321709075373241)
      ·
        refine ⟨30336621606991281806529931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40448828809321709075373241 30336621606991281806529931)
        ·
          refine ⟨45504932410486922709794897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30336621606991281806529931 45504932410486922709794897)
          ·
            refine ⟨34128699307865192032346173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45504932410486922709794897 34128699307865192032346173)
            ·
              refine ⟨12798262240449447012129815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34128699307865192032346173 12798262240449447012129815)
              ·
                refine ⟨19197393360674170518194723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12798262240449447012129815 19197393360674170518194723)
                ·
                  refine ⟨28796090041011255777292085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19197393360674170518194723 28796090041011255777292085)
                  ·
                    refine ⟨2699633441344805229121133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28796090041011255777292085 2699633441344805229121133)
                    ·
                      refine ⟨1012362540504301960920425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2699633441344805229121133 1012362540504301960920425)
                      ·
                        rfl

theorem cell23_1971569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_1971569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971569 prefixEnd_1971569 := by exact prefixLift 1971569
  have htrace : WordTrace (prefixWord ++ tailWord_1971569) baseStart_1971569 baseEnd_1971569 := by
    simpa [prefixWord, tailWord_1971569, baseEnd_1971569] using wordTrace_append hprefix tailTrace_1971569
  have hstable : (prefixWord ++ tailWord_1971569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971569).length < 2 ^ (prefixWord ++ tailWord_1971569).sum := by decide
  have hdescent : baseEnd_1971569 < baseStart_1971569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971593 : List Nat := [1, 2, 1, 1, 7, 1, 2, 3, 5]
def baseStart_1971593 : Nat := 118140960795 + 1971593 * 2 ^ 59
def prefixEnd_1971593 : Nat := 4983230072969 + 3 ^ 40 * 1971593 * 2
def baseEnd_1971593 : Nat := 112486096004445540780035

theorem tailTrace_1971593 : CollatzResearch.WordTrace tailWord_1971593 prefixEnd_1971593 112486096004445540780035 := by
  unfold tailWord_1971593
  simp only [CollatzResearch.WordTrace]
  refine ⟨71909904346262757121759433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47939936230841838081172955 71909904346262757121759433)
  ·
    refine ⟨53932428259697067841319575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71909904346262757121759433 53932428259697067841319575)
    ·
      refine ⟨80898642389545601761979363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53932428259697067841319575 80898642389545601761979363)
      ·
        refine ⟨121347963584318402642969045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80898642389545601761979363 121347963584318402642969045)
        ·
          refine ⟨2844092896507462561944587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 121347963584318402642969045 2844092896507462561944587)
          ·
            refine ⟨4266139344761193842916881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844092896507462561944587 4266139344761193842916881)
            ·
              refine ⟨3199604508570895382187661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4266139344761193842916881 3199604508570895382187661)
              ·
                refine ⟨1199851690714085768320373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3199604508570895382187661 1199851690714085768320373)
                ·
                  refine ⟨112486096004445540780035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1199851690714085768320373 112486096004445540780035)
                  ·
                    rfl

theorem cell23_1971593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 5].length) (baseStart_1971593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971593 prefixEnd_1971593 := by exact prefixLift 1971593
  have htrace : WordTrace (prefixWord ++ tailWord_1971593) baseStart_1971593 baseEnd_1971593 := by
    simpa [prefixWord, tailWord_1971593, baseEnd_1971593] using wordTrace_append hprefix tailTrace_1971593
  have hstable : (prefixWord ++ tailWord_1971593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971593).length < 2 ^ (prefixWord ++ tailWord_1971593).sum := by decide
  have hdescent : baseEnd_1971593 < baseStart_1971593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971639 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_1971639 : Nat := 118140960795 + 1971639 * 2 ^ 59
def prefixEnd_1971639 : Nat := 4983230072969 + 3 ^ 40 * 1971639 * 2
def baseEnd_1971639 : Nat := 1012398484150116687045103

theorem tailTrace_1971639 : CollatzResearch.WordTrace tailWord_1971639 prefixEnd_1971639 1012398484150116687045103 := by
  unfold tailWord_1971639
  simp only [CollatzResearch.WordTrace]
  refine ⟨71911582104096106977933971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47941054736064071318622647 71911582104096106977933971)
  ·
    refine ⟨107867373156144160466900957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71911582104096106977933971 107867373156144160466900957)
    ·
      refine ⟨40450264933554060175087859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107867373156144160466900957 40450264933554060175087859)
      ·
        refine ⟨60675397400331090262631789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40450264933554060175087859 60675397400331090262631789)
        ·
          refine ⟨22753274025124158848486921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60675397400331090262631789 22753274025124158848486921)
          ·
            refine ⟨17064955518843119136365191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22753274025124158848486921 17064955518843119136365191)
            ·
              refine ⟨25597433278264678704547787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17064955518843119136365191 25597433278264678704547787)
              ·
                refine ⟨38396149917397018056821681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25597433278264678704547787 38396149917397018056821681)
                ·
                  refine ⟨28797112438047763542616261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38396149917397018056821681 28797112438047763542616261)
                  ·
                    refine ⟨5399458582133955664240549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28797112438047763542616261 5399458582133955664240549)
                    ·
                      refine ⟨1012398484150116687045103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5399458582133955664240549 1012398484150116687045103)
                      ·
                        rfl

theorem cell23_1971639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_1971639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971639 prefixEnd_1971639 := by exact prefixLift 1971639
  have htrace : WordTrace (prefixWord ++ tailWord_1971639) baseStart_1971639 baseEnd_1971639 := by
    simpa [prefixWord, tailWord_1971639, baseEnd_1971639] using wordTrace_append hprefix tailTrace_1971639
  have hstable : (prefixWord ++ tailWord_1971639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971639).length < 2 ^ (prefixWord ++ tailWord_1971639).sum := by decide
  have hdescent : baseEnd_1971639 < baseStart_1971639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971670 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1971670 : Nat := 118140960795 + 1971670 * 2 ^ 59
def prefixEnd_1971670 : Nat := 4983230072969 + 3 ^ 40 * 1971670 * 2
def baseEnd_1971670 : Nat := 337471467350135355252487

theorem tailTrace_1971670 : CollatzResearch.WordTrace tailWord_1971670 prefixEnd_1971670 337471467350135355252487 := by
  unfold tailWord_1971670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4494544547936487454519529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47941808511322532848208309 4494544547936487454519529)
  ·
    refine ⟨3370908410952365590889647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4494544547936487454519529 3370908410952365590889647)
    ·
      refine ⟨5056362616428548386334471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3370908410952365590889647 5056362616428548386334471)
      ·
        refine ⟨7584543924642822579501707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5056362616428548386334471 7584543924642822579501707)
        ·
          refine ⟨11376815886964233869252561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7584543924642822579501707 11376815886964233869252561)
          ·
            refine ⟨8532611915223175401939421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11376815886964233869252561 8532611915223175401939421)
            ·
              refine ⟨3199729468208690775727283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8532611915223175401939421 3199729468208690775727283)
              ·
                refine ⟨4799594202313036163590925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199729468208690775727283 4799594202313036163590925)
                ·
                  refine ⟨1799847825867388561346597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4799594202313036163590925 1799847825867388561346597)
                  ·
                    refine ⟨337471467350135355252487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1799847825867388561346597 337471467350135355252487)
                    ·
                      rfl

theorem cell23_1971670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1971670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971670 prefixEnd_1971670 := by exact prefixLift 1971670
  have htrace : WordTrace (prefixWord ++ tailWord_1971670) baseStart_1971670 baseEnd_1971670 := by
    simpa [prefixWord, tailWord_1971670, baseEnd_1971670] using wordTrace_append hprefix tailTrace_1971670
  have hstable : (prefixWord ++ tailWord_1971670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971670).length < 2 ^ (prefixWord ++ tailWord_1971670).sum := by decide
  have hdescent : baseEnd_1971670 < baseStart_1971670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971683 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 6]
def baseStart_1971683 : Nat := 118140960795 + 1971683 * 2 ^ 59
def prefixEnd_1971683 : Nat := 4983230072969 + 3 ^ 40 * 1971683 * 2
def baseEnd_1971683 : Nat := 112491230810990501654989

theorem tailTrace_1971683 : CollatzResearch.WordTrace tailWord_1971683 prefixEnd_1971683 112491230810990501654989 := by
  unfold tailWord_1971683
  simp only [CollatzResearch.WordTrace]
  refine ⟨71913186915936702492535703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47942124610624468328357135 71913186915936702492535703)
  ·
    refine ⟨107869780373905053738803555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71913186915936702492535703 107869780373905053738803555)
    ·
      refine ⟨161804670560857580608205333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107869780373905053738803555 161804670560857580608205333)
      ·
        refine ⟨7584593932540199091009625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161804670560857580608205333 7584593932540199091009625)
        ·
          refine ⟨5688445449405149318257219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7584593932540199091009625 5688445449405149318257219)
          ·
            refine ⟨8532668174107723977385829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688445449405149318257219 8532668174107723977385829)
            ·
              refine ⟨1599875282645198245759843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8532668174107723977385829 1599875282645198245759843)
              ·
                refine ⟨2399812923967797368639765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599875282645198245759843 2399812923967797368639765)
                ·
                  refine ⟨112491230810990501654989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2399812923967797368639765 112491230810990501654989)
                  ·
                    rfl

theorem cell23_1971683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 6].length) (baseStart_1971683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971683 prefixEnd_1971683 := by exact prefixLift 1971683
  have htrace : WordTrace (prefixWord ++ tailWord_1971683) baseStart_1971683 baseEnd_1971683 := by
    simpa [prefixWord, tailWord_1971683, baseEnd_1971683] using wordTrace_append hprefix tailTrace_1971683
  have hstable : (prefixWord ++ tailWord_1971683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971683).length < 2 ^ (prefixWord ++ tailWord_1971683).sum := by decide
  have hdescent : baseEnd_1971683 < baseStart_1971683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971696 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 3, 5]
def baseStart_1971696 : Nat := 118140960795 + 1971696 * 2 ^ 59
def prefixEnd_1971696 : Nat := 4983230072969 + 3 ^ 40 * 1971696 * 2
def baseEnd_1971696 : Nat := 337475917515807654677447

theorem tailTrace_1971696 : CollatzResearch.WordTrace tailWord_1971696 prefixEnd_1971696 337475917515807654677447 := by
  unfold tailWord_1971696
  simp only [CollatzResearch.WordTrace]
  refine ⟨35956830532444802856379471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47942440709926403808505961 35956830532444802856379471)
  ·
    refine ⟨53935245798667204284569207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35956830532444802856379471 53935245798667204284569207)
    ·
      refine ⟨80902868698000806426853811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53935245798667204284569207 80902868698000806426853811)
      ·
        refine ⟨121354303047001209640280717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80902868698000806426853811 121354303047001209640280717)
        ·
          refine ⟨45507863642625453615105269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121354303047001209640280717 45507863642625453615105269)
          ·
            refine ⟨4266362216496136276416119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45507863642625453615105269 4266362216496136276416119)
            ·
              refine ⟨6399543324744204414624179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266362216496136276416119 6399543324744204414624179)
              ·
                refine ⟨9599314987116306621936269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399543324744204414624179 9599314987116306621936269)
                ·
                  refine ⟨3599743120168614983226101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9599314987116306621936269 3599743120168614983226101)
                  ·
                    refine ⟨337475917515807654677447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3599743120168614983226101 337475917515807654677447)
                    ·
                      rfl

theorem cell23_1971696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_1971696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971696 prefixEnd_1971696 := by exact prefixLift 1971696
  have htrace : WordTrace (prefixWord ++ tailWord_1971696) baseStart_1971696 baseEnd_1971696 := by
    simpa [prefixWord, tailWord_1971696, baseEnd_1971696] using wordTrace_append hprefix tailTrace_1971696
  have hstable : (prefixWord ++ tailWord_1971696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971696).length < 2 ^ (prefixWord ++ tailWord_1971696).sum := by decide
  have hdescent : baseEnd_1971696 < baseStart_1971696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971743 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 2, 4]
def baseStart_1971743 : Nat := 118140960795 + 1971743 * 2 ^ 59
def prefixEnd_1971743 : Nat := 4983230072969 + 3 ^ 40 * 1971743 * 2
def baseEnd_1971743 : Nat := 337483962046061426714875

theorem tailTrace_1971743 : CollatzResearch.WordTrace tailWord_1971743 prefixEnd_1971743 337483962046061426714875 := by
  unfold tailWord_1971743
  simp only [CollatzResearch.WordTrace]
  refine ⟨71915375295719332739719883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47943583530479555159813255 71915375295719332739719883)
  ·
    refine ⟨107873062943578999109579825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71915375295719332739719883 107873062943578999109579825)
    ·
      refine ⟨80904797207684249332184869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107873062943578999109579825 80904797207684249332184869)
      ·
        refine ⟨15169649476440796749784663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80904797207684249332184869 15169649476440796749784663)
        ·
          refine ⟨22754474214661195124676995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15169649476440796749784663 22754474214661195124676995)
          ·
            refine ⟨34131711321991792687015493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22754474214661195124676995 34131711321991792687015493)
            ·
              refine ⟨6399695872873461128815405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34131711321991792687015493 6399695872873461128815405)
              ·
                refine ⟨2399885952327547923305777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6399695872873461128815405 2399885952327547923305777)
                ·
                  refine ⟨1799914464245660942479333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2399885952327547923305777 1799914464245660942479333)
                  ·
                    refine ⟨337483962046061426714875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1799914464245660942479333 337483962046061426714875)
                    ·
                      rfl

theorem cell23_1971743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 4].length) (baseStart_1971743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971743 prefixEnd_1971743 := by exact prefixLift 1971743
  have htrace : WordTrace (prefixWord ++ tailWord_1971743) baseStart_1971743 baseEnd_1971743 := by
    simpa [prefixWord, tailWord_1971743, baseEnd_1971743] using wordTrace_append hprefix tailTrace_1971743
  have hstable : (prefixWord ++ tailWord_1971743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971743).length < 2 ^ (prefixWord ++ tailWord_1971743).sum := by decide
  have hdescent : baseEnd_1971743 < baseStart_1971743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971746 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1971746 : Nat := 118140960795 + 1971746 * 2 ^ 59
def prefixEnd_1971746 : Nat := 4983230072969 + 3 ^ 40 * 1971746 * 2
def baseEnd_1971746 : Nat := 1012453426580147768407111

theorem tailTrace_1971746 : CollatzResearch.WordTrace tailWord_1971746 prefixEnd_1971746 1012453426580147768407111 := by
  unfold tailWord_1971746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17978871178677116063019773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47943656476472309501386061 17978871178677116063019773)
  ·
    refine ⟨6742076692003918523632415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17978871178677116063019773 6742076692003918523632415)
    ·
      refine ⟨10113115038005877785448623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6742076692003918523632415 10113115038005877785448623)
      ·
        refine ⟨15169672557008816678172935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10113115038005877785448623 15169672557008816678172935)
        ·
          refine ⟨22754508835513225017259403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15169672557008816678172935 22754508835513225017259403)
          ·
            refine ⟨34131763253269837525889105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22754508835513225017259403 34131763253269837525889105)
            ·
              refine ⟨25598822439952378144416829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34131763253269837525889105 25598822439952378144416829)
              ·
                refine ⟨9599558414982141804156311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25598822439952378144416829 9599558414982141804156311)
                ·
                  refine ⟨14399337622473212706234467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9599558414982141804156311 14399337622473212706234467)
                  ·
                    refine ⟨21599006433709819059351701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14399337622473212706234467 21599006433709819059351701)
                    ·
                      refine ⟨1012453426580147768407111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21599006433709819059351701 1012453426580147768407111)
                      ·
                        rfl

theorem cell23_1971746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1971746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971746 prefixEnd_1971746 := by exact prefixLift 1971746
  have htrace : WordTrace (prefixWord ++ tailWord_1971746) baseStart_1971746 baseEnd_1971746 := by
    simpa [prefixWord, tailWord_1971746, baseEnd_1971746] using wordTrace_append hprefix tailTrace_1971746
  have hstable : (prefixWord ++ tailWord_1971746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971746).length < 2 ^ (prefixWord ++ tailWord_1971746).sum := by decide
  have hdescent : baseEnd_1971746 < baseStart_1971746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971767 : List Nat := [1, 1, 3, 1, 2, 4, 1, 5, 1, 2, 2]
def baseStart_1971767 : Nat := 118140960795 + 1971767 * 2 ^ 59
def prefixEnd_1971767 : Nat := 4983230072969 + 3 ^ 40 * 1971767 * 2
def baseEnd_1971767 : Nat := 1012464209673892186244515

theorem tailTrace_1971767 : CollatzResearch.WordTrace tailWord_1971767 prefixEnd_1971767 1012464209673892186244515 := by
  unfold tailWord_1971767
  simp only [CollatzResearch.WordTrace]
  refine ⟨71916250647632384838593555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47944167098421589892395703 71916250647632384838593555)
  ·
    refine ⟨107874375971448577257890333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71916250647632384838593555 107874375971448577257890333)
    ·
      refine ⟨40452890989293216471708875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107874375971448577257890333 40452890989293216471708875)
      ·
        refine ⟨60679336483939824707563313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40452890989293216471708875 60679336483939824707563313)
        ·
          refine ⟨45509502362954868530672485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60679336483939824707563313 45509502362954868530672485)
          ·
            refine ⟨8533031693054037849501091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45509502362954868530672485 8533031693054037849501091)
            ·
              refine ⟨12799547539581056774251637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8533031693054037849501091 12799547539581056774251637)
              ·
                refine ⟨1199957581835724072586091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12799547539581056774251637 1199957581835724072586091)
                ·
                  refine ⟨1799936372753586108879137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199957581835724072586091 1799936372753586108879137)
                  ·
                    refine ⟨1349952279565189581659353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1799936372753586108879137 1349952279565189581659353)
                    ·
                      refine ⟨1012464209673892186244515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349952279565189581659353 1012464209673892186244515)
                      ·
                        rfl

theorem cell23_1971767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 2, 2].length) (baseStart_1971767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971767 prefixEnd_1971767 := by exact prefixLift 1971767
  have htrace : WordTrace (prefixWord ++ tailWord_1971767) baseStart_1971767 baseEnd_1971767 := by
    simpa [prefixWord, tailWord_1971767, baseEnd_1971767] using wordTrace_append hprefix tailTrace_1971767
  have hstable : (prefixWord ++ tailWord_1971767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971767).length < 2 ^ (prefixWord ++ tailWord_1971767).sum := by decide
  have hdescent : baseEnd_1971767 < baseStart_1971767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971823 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 3, 4, 2]
def baseStart_1971823 : Nat := 118140960795 + 1971823 * 2 ^ 59
def prefixEnd_1971823 : Nat := 4983230072969 + 3 ^ 40 * 1971823 * 2
def baseEnd_1971823 : Nat := 1012492964590543967144257

theorem tailTrace_1971823 : CollatzResearch.WordTrace tailWord_1971823 prefixEnd_1971823 1012492964590543967144257 := by
  unfold tailWord_1971823
  simp only [CollatzResearch.WordTrace]
  refine ⟨71918293135429506402632123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47945528756953004268421415 71918293135429506402632123)
  ·
    refine ⟨107877439703144259603948185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71918293135429506402632123 107877439703144259603948185)
    ·
      refine ⟨80908079777358194702961139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107877439703144259603948185 80908079777358194702961139)
      ·
        refine ⟨121362119666037292054441709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80908079777358194702961139 121362119666037292054441709)
        ·
          refine ⟨45510794874763984520415641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121362119666037292054441709 45510794874763984520415641)
          ·
            refine ⟨34133096156072988390311731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45510794874763984520415641 34133096156072988390311731)
            ·
              refine ⟨51199644234109482585467597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34133096156072988390311731 51199644234109482585467597)
              ·
                refine ⟨19199866587791055969550349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51199644234109482585467597 19199866587791055969550349)
                ·
                  refine ⟨7199949970421645988581381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19199866587791055969550349 7199949970421645988581381)
                  ·
                    refine ⟨1349990619454058622859009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7199949970421645988581381 1349990619454058622859009)
                    ·
                      refine ⟨1012492964590543967144257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1349990619454058622859009 1012492964590543967144257)
                      ·
                        rfl

theorem cell23_1971823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 4, 2].length) (baseStart_1971823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971823 prefixEnd_1971823 := by exact prefixLift 1971823
  have htrace : WordTrace (prefixWord ++ tailWord_1971823) baseStart_1971823 baseEnd_1971823 := by
    simpa [prefixWord, tailWord_1971823, baseEnd_1971823] using wordTrace_append hprefix tailTrace_1971823
  have hstable : (prefixWord ++ tailWord_1971823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971823).length < 2 ^ (prefixWord ++ tailWord_1971823).sum := by decide
  have hdescent : baseEnd_1971823 < baseStart_1971823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971840 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 4, 2, 2]
def baseStart_1971840 : Nat := 118140960795 + 1971840 * 2 ^ 59
def prefixEnd_1971840 : Nat := 4983230072969 + 3 ^ 40 * 1971840 * 2
def baseEnd_1971840 : Nat := 1012501693761670400631679

theorem tailTrace_1971840 : CollatzResearch.WordTrace tailWord_1971840 prefixEnd_1971840 1012501693761670400631679 := by
  unfold tailWord_1971840
  simp only [CollatzResearch.WordTrace]
  refine ⟨35959456588183959153000487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47945942117578612204000649 35959456588183959153000487)
  ·
    refine ⟨53939184882275938729500731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35959456588183959153000487 53939184882275938729500731)
    ·
      refine ⟨80908777323413908094251097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53939184882275938729500731 80908777323413908094251097)
      ·
        refine ⟨60681582992560431070688323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80908777323413908094251097 60681582992560431070688323)
        ·
          refine ⟨91022374488840646606032485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60681582992560431070688323 91022374488840646606032485)
          ·
            refine ⟨17066695216657621238631091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91022374488840646606032485 17066695216657621238631091)
            ·
              refine ⟨25600042824986431857946637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17066695216657621238631091 25600042824986431857946637)
              ·
                refine ⟨9600016059369911946729989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25600042824986431857946637 9600016059369911946729989)
                ·
                  refine ⟨1800003011131858490011873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9600016059369911946729989 1800003011131858490011873)
                  ·
                    refine ⟨1350002258348893867508905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1800003011131858490011873 1350002258348893867508905)
                    ·
                      refine ⟨1012501693761670400631679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350002258348893867508905 1012501693761670400631679)
                      ·
                        rfl

theorem cell23_1971840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_1971840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971840 prefixEnd_1971840 := by exact prefixLift 1971840
  have htrace : WordTrace (prefixWord ++ tailWord_1971840) baseStart_1971840 baseEnd_1971840 := by
    simpa [prefixWord, tailWord_1971840, baseEnd_1971840] using wordTrace_append hprefix tailTrace_1971840
  have hstable : (prefixWord ++ tailWord_1971840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971840).length < 2 ^ (prefixWord ++ tailWord_1971840).sum := by decide
  have hdescent : baseEnd_1971840 < baseStart_1971840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971874 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1971874 : Nat := 118140960795 + 1971874 * 2 ^ 59
def prefixEnd_1971874 : Nat := 4983230072969 + 3 ^ 40 * 1971874 * 2
def baseEnd_1971874 : Nat := 1012519152103923267606523

theorem tailTrace_1971874 : CollatzResearch.WordTrace tailWord_1971874 prefixEnd_1971874 1012519152103923267606523 := by
  unfold tailWord_1971874
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980038314561185528184669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47946768838829828075159117 17980038314561185528184669)
  ·
    refine ⟨6742514367960444573069251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17980038314561185528184669 6742514367960444573069251)
    ·
      refine ⟨10113771551940666859603877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6742514367960444573069251 10113771551940666859603877)
      ·
        refine ⟨1896332165988875036175727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10113771551940666859603877 1896332165988875036175727)
        ·
          refine ⟨2844498248983312554263591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896332165988875036175727 2844498248983312554263591)
          ·
            refine ⟨4266747373474968831395387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844498248983312554263591 4266747373474968831395387)
            ·
              refine ⟨6400121060212453247093081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266747373474968831395387 6400121060212453247093081)
              ·
                refine ⟨4800090795159339935319811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6400121060212453247093081 4800090795159339935319811)
                ·
                  refine ⟨7200136192739009902979717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800090795159339935319811 7200136192739009902979717)
                  ·
                    refine ⟨1350025536138564356808697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200136192739009902979717 1350025536138564356808697)
                    ·
                      refine ⟨1012519152103923267606523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350025536138564356808697 1012519152103923267606523)
                      ·
                        rfl

theorem cell23_1971874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1971874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971874 prefixEnd_1971874 := by exact prefixLift 1971874
  have htrace : WordTrace (prefixWord ++ tailWord_1971874) baseStart_1971874 baseEnd_1971874 := by
    simpa [prefixWord, tailWord_1971874, baseEnd_1971874] using wordTrace_append hprefix tailTrace_1971874
  have hstable : (prefixWord ++ tailWord_1971874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971874).length < 2 ^ (prefixWord ++ tailWord_1971874).sum := by decide
  have hdescent : baseEnd_1971874 < baseStart_1971874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971900 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_1971900 : Nat := 118140960795 + 1971900 * 2 ^ 59
def prefixEnd_1971900 : Nat := 4983230072969 + 3 ^ 40 * 1971900 * 2
def baseEnd_1971900 : Nat := 1012532502600940165881403

theorem tailTrace_1971900 : CollatzResearch.WordTrace tailWord_1971900 prefixEnd_1971900 1012532502600940165881403 := by
  unfold tailWord_1971900
  simp only [CollatzResearch.WordTrace]
  refine ⟨35960550778075274276592577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47947401037433699035456769 35960550778075274276592577)
  ·
    refine ⟨26970413083556455707444433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35960550778075274276592577 26970413083556455707444433)
    ·
      refine ⟨20227809812667341780583325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26970413083556455707444433 20227809812667341780583325)
      ·
        refine ⟨7585428679750253167718747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20227809812667341780583325 7585428679750253167718747)
        ·
          refine ⟨11378143019625379751578121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7585428679750253167718747 11378143019625379751578121)
          ·
            refine ⟨8533607264719034813683591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11378143019625379751578121 8533607264719034813683591)
            ·
              refine ⟨12800410897078552220525387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8533607264719034813683591 12800410897078552220525387)
              ·
                refine ⟨19200616345617828330788081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12800410897078552220525387 19200616345617828330788081)
                ·
                  refine ⟨14400462259213371248091061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19200616345617828330788081 14400462259213371248091061)
                  ·
                    refine ⟨1350043336801253554508537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14400462259213371248091061 1350043336801253554508537)
                    ·
                      refine ⟨1012532502600940165881403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350043336801253554508537 1012532502600940165881403)
                      ·
                        rfl

theorem cell23_1971900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_1971900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971900 prefixEnd_1971900 := by exact prefixLift 1971900
  have htrace : WordTrace (prefixWord ++ tailWord_1971900) baseStart_1971900 baseEnd_1971900 := by
    simpa [prefixWord, tailWord_1971900, baseEnd_1971900] using wordTrace_append hprefix tailTrace_1971900
  have hstable : (prefixWord ++ tailWord_1971900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971900).length < 2 ^ (prefixWord ++ tailWord_1971900).sum := by decide
  have hdescent : baseEnd_1971900 < baseStart_1971900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971930 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_1971930 : Nat := 118140960795 + 1971930 * 2 ^ 59
def prefixEnd_1971930 : Nat := 4983230072969 + 3 ^ 40 * 1971930 * 2
def baseEnd_1971930 : Nat := 1012547907020575048506265

theorem tailTrace_1971930 : CollatzResearch.WordTrace tailWord_1971930 prefixEnd_1971930 1012547907020575048506265 := by
  unfold tailWord_1971930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980548936510465919194311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47948130497361242451184829 17980548936510465919194311)
  ·
    refine ⟨26970823404765698878791467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17980548936510465919194311 26970823404765698878791467)
    ·
      refine ⟨40456235107148548318187201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26970823404765698878791467 40456235107148548318187201)
      ·
        refine ⟨30342176330361411238640401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40456235107148548318187201 30342176330361411238640401)
        ·
          refine ⟨22756632247771058428980301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30342176330361411238640401 22756632247771058428980301)
          ·
            refine ⟨8533737092914146910867613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22756632247771058428980301 8533737092914146910867613)
            ·
              refine ⟨3200151409842805091575355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8533737092914146910867613 3200151409842805091575355)
              ·
                refine ⟨4800227114764207637363033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200151409842805091575355 4800227114764207637363033)
                ·
                  refine ⟨3600170336073155728022275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4800227114764207637363033 3600170336073155728022275)
                  ·
                    refine ⟨5400255504109733592033413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3600170336073155728022275 5400255504109733592033413)
                    ·
                      refine ⟨1012547907020575048506265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5400255504109733592033413 1012547907020575048506265)
                      ·
                        rfl

theorem cell23_1971930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_1971930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971930 prefixEnd_1971930 := by exact prefixLift 1971930
  have htrace : WordTrace (prefixWord ++ tailWord_1971930) baseStart_1971930 baseEnd_1971930 := by
    simpa [prefixWord, tailWord_1971930, baseEnd_1971930] using wordTrace_append hprefix tailTrace_1971930
  have hstable : (prefixWord ++ tailWord_1971930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971930).length < 2 ^ (prefixWord ++ tailWord_1971930).sum := by decide
  have hdescent : baseEnd_1971930 < baseStart_1971930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971950 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_1971950 : Nat := 118140960795 + 1971950 * 2 ^ 59
def prefixEnd_1971950 : Nat := 4983230072969 + 3 ^ 40 * 1971950 * 2
def baseEnd_1971950 : Nat := 1012558176633664970256173

theorem tailTrace_1971950 : CollatzResearch.WordTrace tailWord_1971950 prefixEnd_1971950 1012558176633664970256173 := by
  unfold tailWord_1971950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990365650746175886563163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47948616803979604728336869 8990365650746175886563163)
  ·
    refine ⟨13485548476119263829844745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8990365650746175886563163 13485548476119263829844745)
    ·
      refine ⟨10114161357089447872383559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13485548476119263829844745 10114161357089447872383559)
      ·
        refine ⟨15171242035634171808575339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10114161357089447872383559 15171242035634171808575339)
        ·
          refine ⟨22756863053451257712863009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15171242035634171808575339 22756863053451257712863009)
          ·
            refine ⟨17067647290088443284647257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22756863053451257712863009 17067647290088443284647257)
            ·
              refine ⟨12800735467566332463485443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17067647290088443284647257 12800735467566332463485443)
              ·
                refine ⟨19201103201349498695228165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12800735467566332463485443 19201103201349498695228165)
                ·
                  refine ⟨3600206850253031005355281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19201103201349498695228165 3600206850253031005355281)
                  ·
                    refine ⟨2700155137689773254016461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3600206850253031005355281 2700155137689773254016461)
                    ·
                      refine ⟨1012558176633664970256173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2700155137689773254016461 1012558176633664970256173)
                      ·
                        rfl

theorem cell23_1971950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_1971950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971950 prefixEnd_1971950 := by exact prefixLift 1971950
  have htrace : WordTrace (prefixWord ++ tailWord_1971950) baseStart_1971950 baseEnd_1971950 := by
    simpa [prefixWord, tailWord_1971950, baseEnd_1971950] using wordTrace_append hprefix tailTrace_1971950
  have hstable : (prefixWord ++ tailWord_1971950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971950).length < 2 ^ (prefixWord ++ tailWord_1971950).sum := by decide
  have hdescent : baseEnd_1971950 < baseStart_1971950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971953 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 8]
def baseStart_1971953 : Nat := 118140960795 + 1971953 * 2 ^ 59
def prefixEnd_1971953 : Nat := 4983230072969 + 3 ^ 40 * 1971953 * 2
def baseEnd_1971953 : Nat := 112506635230625384279851

theorem tailTrace_1971953 : CollatzResearch.WordTrace tailWord_1971953 prefixEnd_1971953 112506635230625384279851 := by
  unfold tailWord_1971953
  simp only [CollatzResearch.WordTrace]
  refine ⟨71923034624958538604864513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47948689749972359069909675 71923034624958538604864513)
  ·
    refine ⟨53942275968718903953648385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71923034624958538604864513 53942275968718903953648385)
    ·
      refine ⟨40456706976539177965236289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53942275968718903953648385 40456706976539177965236289)
      ·
        refine ⟨30342530232404383473927217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40456706976539177965236289 30342530232404383473927217)
        ·
          refine ⟨22756897674303287605445413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30342530232404383473927217 22756897674303287605445413)
          ·
            refine ⟨4266918313931866426021015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22756897674303287605445413 4266918313931866426021015)
            ·
              refine ⟨6400377470897799639031523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266918313931866426021015 6400377470897799639031523)
              ·
                refine ⟨9600566206346699458547285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6400377470897799639031523 9600566206346699458547285)
                ·
                  refine ⟨112506635230625384279851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9600566206346699458547285 112506635230625384279851)
                  ·
                    rfl

theorem cell23_1971953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 8].length) (baseStart_1971953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1971953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1971953 prefixEnd_1971953 := by exact prefixLift 1971953
  have htrace : WordTrace (prefixWord ++ tailWord_1971953) baseStart_1971953 baseEnd_1971953 := by
    simpa [prefixWord, tailWord_1971953, baseEnd_1971953] using wordTrace_append hprefix tailTrace_1971953
  have hstable : (prefixWord ++ tailWord_1971953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971953).length < 2 ^ (prefixWord ++ tailWord_1971953).sum := by decide
  have hdescent : baseEnd_1971953 < baseStart_1971953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972000 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 1, 5]
def baseStart_1972000 : Nat := 118140960795 + 1972000 * 2 ^ 59
def prefixEnd_1972000 : Nat := 4983230072969 + 3 ^ 40 * 1972000 * 2
def baseEnd_1972000 : Nat := 337527950222129924876981

theorem tailTrace_1972000 : CollatzResearch.WordTrace tailWord_1972000 prefixEnd_1972000 337527950222129924876981 := by
  unfold tailWord_1972000
  simp only [CollatzResearch.WordTrace]
  refine ⟨35962374427894132815912727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47949832570525510421216969 35962374427894132815912727)
  ·
    refine ⟨53943561641841199223869091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35962374427894132815912727 53943561641841199223869091)
    ·
      refine ⟨80915342462761798835803637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53943561641841199223869091 80915342462761798835803637)
      ·
        refine ⟨7585813355883918640856591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80915342462761798835803637 7585813355883918640856591)
        ·
          refine ⟨11378720033825877961284887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7585813355883918640856591 11378720033825877961284887)
          ·
            refine ⟨17068080050738816941927331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11378720033825877961284887 17068080050738816941927331)
            ·
              refine ⟨25602120076108225412890997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17068080050738816941927331 25602120076108225412890997)
              ·
                refine ⟨2400198757135146132458531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25602120076108225412890997 2400198757135146132458531)
                ·
                  refine ⟨3600298135702719198687797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400198757135146132458531 3600298135702719198687797)
                  ·
                    refine ⟨337527950222129924876981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3600298135702719198687797 337527950222129924876981)
                    ·
                      rfl

theorem cell23_1972000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 5].length) (baseStart_1972000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972000 prefixEnd_1972000 := by exact prefixLift 1972000
  have htrace : WordTrace (prefixWord ++ tailWord_1972000) baseStart_1972000 baseEnd_1972000 := by
    simpa [prefixWord, tailWord_1972000, baseEnd_1972000] using wordTrace_append hprefix tailTrace_1972000
  have hstable : (prefixWord ++ tailWord_1972000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972000).length < 2 ^ (prefixWord ++ tailWord_1972000).sum := by decide
  have hdescent : baseEnd_1972000 < baseStart_1972000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972023 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_1972023 : Nat := 118140960795 + 1972023 * 2 ^ 59
def prefixEnd_1972023 : Nat := 4983230072969 + 3 ^ 40 * 1972023 * 2
def baseEnd_1972023 : Nat := 1012595660721443184643337

theorem tailTrace_1972023 : CollatzResearch.WordTrace tailWord_1972023 prefixEnd_1972023 1012595660721443184643337 := by
  unfold tailWord_1972023
  simp only [CollatzResearch.WordTrace]
  refine ⟨71925587734704940559912723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47950391823136627039941815 71925587734704940559912723)
  ·
    refine ⟨107888381602057410839869085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71925587734704940559912723 107888381602057410839869085)
    ·
      refine ⟨40458143100771529064950907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107888381602057410839869085 40458143100771529064950907)
      ·
        refine ⟨60687214651157293597426361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40458143100771529064950907 60687214651157293597426361)
        ·
          refine ⟨45515410988367970198069771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60687214651157293597426361 45515410988367970198069771)
          ·
            refine ⟨68273116482551955297104657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45515410988367970198069771 68273116482551955297104657)
            ·
              refine ⟨51204837361913966472828493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68273116482551955297104657 51204837361913966472828493)
              ·
                refine ⟨19201814010717737427310685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51204837361913966472828493 19201814010717737427310685)
                ·
                  refine ⟨7200680254019151535241507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19201814010717737427310685 7200680254019151535241507)
                  ·
                    refine ⟨10801020381028727302862261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7200680254019151535241507 10801020381028727302862261)
                    ·
                      refine ⟨1012595660721443184643337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10801020381028727302862261 1012595660721443184643337)
                      ·
                        rfl

theorem cell23_1972023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_1972023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972023 prefixEnd_1972023 := by exact prefixLift 1972023
  have htrace : WordTrace (prefixWord ++ tailWord_1972023) baseStart_1972023 baseEnd_1972023 := by
    simpa [prefixWord, tailWord_1972023, baseEnd_1972023] using wordTrace_append hprefix tailTrace_1972023
  have hstable : (prefixWord ++ tailWord_1972023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972023).length < 2 ^ (prefixWord ++ tailWord_1972023).sum := by decide
  have hdescent : baseEnd_1972023 < baseStart_1972023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972037 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 5, 2, 2]
def baseStart_1972037 : Nat := 118140960795 + 1972037 * 2 ^ 59
def prefixEnd_1972037 : Nat := 4983230072969 + 3 ^ 40 * 1972037 * 2
def baseEnd_1972037 : Nat := 1012602849450606129868273

theorem tailTrace_1972037 : CollatzResearch.WordTrace tailWord_1972037 prefixEnd_1972037 1012602849450606129868273 := by
  unfold tailWord_1972037
  simp only [CollatzResearch.WordTrace]
  refine ⟨71926098356654220950922365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47950732237769480633948243 71926098356654220950922365)
  ·
    refine ⟨26972286883745332856595887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71926098356654220950922365 26972286883745332856595887)
    ·
      refine ⟨40458430325617999284893831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26972286883745332856595887 40458430325617999284893831)
      ·
        refine ⟨60687645488426998927340747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40458430325617999284893831 60687645488426998927340747)
        ·
          refine ⟨91031468232640498391011121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60687645488426998927340747 91031468232640498391011121)
          ·
            refine ⟨68273601174480373793258341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91031468232640498391011121 68273601174480373793258341)
            ·
              refine ⟨12801300220215070086235939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68273601174480373793258341 12801300220215070086235939)
              ·
                refine ⟨19201950330322605129353909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12801300220215070086235939 19201950330322605129353909)
                ·
                  refine ⟨1800182843467744230876929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19201950330322605129353909 1800182843467744230876929)
                  ·
                    refine ⟨1350137132600808173157697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1800182843467744230876929 1350137132600808173157697)
                    ·
                      refine ⟨1012602849450606129868273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350137132600808173157697 1012602849450606129868273)
                      ·
                        rfl

theorem cell23_1972037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_1972037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972037 prefixEnd_1972037 := by exact prefixLift 1972037
  have htrace : WordTrace (prefixWord ++ tailWord_1972037) baseStart_1972037 baseEnd_1972037 := by
    simpa [prefixWord, tailWord_1972037, baseEnd_1972037] using wordTrace_append hprefix tailTrace_1972037
  have hstable : (prefixWord ++ tailWord_1972037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972037).length < 2 ^ (prefixWord ++ tailWord_1972037).sum := by decide
  have hdescent : baseEnd_1972037 < baseStart_1972037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972050 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1972050 : Nat := 118140960795 + 1972050 * 2 ^ 59
def prefixEnd_1972050 : Nat := 4983230072969 + 3 ^ 40 * 1972050 * 2
def baseEnd_1972050 : Nat := 1012609524699114579005713

theorem tailTrace_1972050 : CollatzResearch.WordTrace tailWord_1972050 prefixEnd_1972050 1012609524699114579005713 := by
  unfold tailWord_1972050
  simp only [CollatzResearch.WordTrace]
  refine ⟨17981643126401781042786401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47951048337071416114097069 17981643126401781042786401)
  ·
    refine ⟨13486232344801335782089801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17981643126401781042786401 13486232344801335782089801)
    ·
      refine ⟨10114674258601001836567351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13486232344801335782089801 10114674258601001836567351)
      ·
        refine ⟨15172011387901502754851027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10114674258601001836567351 15172011387901502754851027)
        ·
          refine ⟨22758017081852254132276541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15172011387901502754851027 22758017081852254132276541)
          ·
            refine ⟨8534256405694595299603703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22758017081852254132276541 8534256405694595299603703)
            ·
              refine ⟨12801384608541892949405555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534256405694595299603703 12801384608541892949405555)
              ·
                refine ⟨19202076912812839424108333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12801384608541892949405555 19202076912812839424108333)
                ·
                  refine ⟨7200778842304814784040625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19202076912812839424108333 7200778842304814784040625)
                  ·
                    refine ⟨5400584131728611088030469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7200778842304814784040625 5400584131728611088030469)
                    ·
                      refine ⟨1012609524699114579005713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5400584131728611088030469 1012609524699114579005713)
                      ·
                        rfl

theorem cell23_1972050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1972050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972050 prefixEnd_1972050 := by exact prefixLift 1972050
  have htrace : WordTrace (prefixWord ++ tailWord_1972050) baseStart_1972050 baseEnd_1972050 := by
    simpa [prefixWord, tailWord_1972050, baseEnd_1972050] using wordTrace_append hprefix tailTrace_1972050
  have hstable : (prefixWord ++ tailWord_1972050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972050).length < 2 ^ (prefixWord ++ tailWord_1972050).sum := by decide
  have hdescent : baseEnd_1972050 < baseStart_1972050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972060 : List Nat := [2, 2, 4, 2, 2, 11]
def baseStart_1972060 : Nat := 118140960795 + 1972060 * 2 ^ 59
def prefixEnd_1972060 : Nat := 4983230072969 + 3 ^ 40 * 1972060 * 2
def baseEnd_1972060 : Nat := 4167138516484195637369

theorem tailTrace_1972060 : CollatzResearch.WordTrace tailWord_1972060 prefixEnd_1972060 4167138516484195637369 := by
  unfold tailWord_1972060
  simp only [CollatzResearch.WordTrace]
  refine ⟨35963468617785447939504817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47951291490380597252673089 35963468617785447939504817)
  ·
    refine ⟨26972601463339085954628613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35963468617785447939504817 26972601463339085954628613)
    ·
      refine ⟨5057362774376078616492865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26972601463339085954628613 5057362774376078616492865)
      ·
        refine ⟨3793022080782058962369649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5057362774376078616492865 3793022080782058962369649)
        ·
          refine ⟨2844766560586544221777237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3793022080782058962369649 2844766560586544221777237)
          ·
            refine ⟨4167138516484195637369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2844766560586544221777237 4167138516484195637369)
            ·
              rfl

theorem cell23_1972060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 11].length) (baseStart_1972060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972060 prefixEnd_1972060 := by exact prefixLift 1972060
  have htrace : WordTrace (prefixWord ++ tailWord_1972060) baseStart_1972060 baseEnd_1972060 := by
    simpa [prefixWord, tailWord_1972060, baseEnd_1972060] using wordTrace_append hprefix tailTrace_1972060
  have hstable : (prefixWord ++ tailWord_1972060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972060).length < 2 ^ (prefixWord ++ tailWord_1972060).sum := by decide
  have hdescent : baseEnd_1972060 < baseStart_1972060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972071 : List Nat := [1, 1, 5, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_1972071 : Nat := 118140960795 + 1972071 * 2 ^ 59
def prefixEnd_1972071 : Nat := 4983230072969 + 3 ^ 40 * 1972071 * 2
def baseEnd_1972071 : Nat := 1012620307792858996843117

theorem tailTrace_1972071 : CollatzResearch.WordTrace tailWord_1972071 prefixEnd_1972071 1012620307792858996843117 := by
  unfold tailWord_1972071
  simp only [CollatzResearch.WordTrace]
  refine ⟨71927338438531044757660067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47951558959020696505106711 71927338438531044757660067)
  ·
    refine ⟨107891007657796567136490101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71927338438531044757660067 107891007657796567136490101)
    ·
      refine ⟨10114781967918428169045947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107891007657796567136490101 10114781967918428169045947)
      ·
        refine ⟨15172172951877642253568921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10114781967918428169045947 15172172951877642253568921)
        ·
          refine ⟨11379129713908231690176691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15172172951877642253568921 11379129713908231690176691)
          ·
            refine ⟨17068694570862347535265037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11379129713908231690176691 17068694570862347535265037)
            ·
              refine ⟨6400760464073380325724389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17068694570862347535265037 6400760464073380325724389)
              ·
                refine ⟨1200142587013758811073323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6400760464073380325724389 1200142587013758811073323)
                ·
                  refine ⟨1800213880520638216609985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200142587013758811073323 1800213880520638216609985)
                  ·
                    refine ⟨1350160410390478662457489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1800213880520638216609985 1350160410390478662457489)
                    ·
                      refine ⟨1012620307792858996843117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350160410390478662457489 1012620307792858996843117)
                      ·
                        rfl

theorem cell23_1972071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_1972071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972071 prefixEnd_1972071 := by exact prefixLift 1972071
  have htrace : WordTrace (prefixWord ++ tailWord_1972071) baseStart_1972071 baseEnd_1972071 := by
    simpa [prefixWord, tailWord_1972071, baseEnd_1972071] using wordTrace_append hprefix tailTrace_1972071
  have hstable : (prefixWord ++ tailWord_1972071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972071).length < 2 ^ (prefixWord ++ tailWord_1972071).sum := by decide
  have hdescent : baseEnd_1972071 < baseStart_1972071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972083 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 5]
def baseStart_1972083 : Nat := 118140960795 + 1972083 * 2 ^ 59
def prefixEnd_1972083 : Nat := 4983230072969 + 3 ^ 40 * 1972083 * 2
def baseEnd_1972083 : Nat := 1012626469560712949893061

theorem tailTrace_1972083 : CollatzResearch.WordTrace tailWord_1972083 prefixEnd_1972083 1012626469560712949893061 := by
  unfold tailWord_1972083
  simp only [CollatzResearch.WordTrace]
  refine ⟨71927776114487570807096903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47951850742991713871397935 71927776114487570807096903)
  ·
    refine ⟨107891664171731356210645355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71927776114487570807096903 107891664171731356210645355)
    ·
      refine ⟨161837496257597034315968033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107891664171731356210645355 161837496257597034315968033)
      ·
        refine ⟨121378122193197775736976025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161837496257597034315968033 121378122193197775736976025)
        ·
          refine ⟨91033591644898331802732019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121378122193197775736976025 91033591644898331802732019)
          ·
            refine ⟨136550387467347497704098029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91033591644898331802732019 136550387467347497704098029)
            ·
              refine ⟨51206395300255311639036761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136550387467347497704098029 51206395300255311639036761)
              ·
                refine ⟨38404796475191483729277571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51206395300255311639036761 38404796475191483729277571)
                ·
                  refine ⟨57607194712787225593916357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38404796475191483729277571 57607194712787225593916357)
                  ·
                    refine ⟨10801349008647604798859317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57607194712787225593916357 10801349008647604798859317)
                    ·
                      refine ⟨1012626469560712949893061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10801349008647604798859317 1012626469560712949893061)
                      ·
                        rfl

theorem cell23_1972083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_1972083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972083 prefixEnd_1972083 := by exact prefixLift 1972083
  have htrace : WordTrace (prefixWord ++ tailWord_1972083) baseStart_1972083 baseEnd_1972083 := by
    simpa [prefixWord, tailWord_1972083, baseEnd_1972083] using wordTrace_append hprefix tailTrace_1972083
  have hstable : (prefixWord ++ tailWord_1972083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972083).length < 2 ^ (prefixWord ++ tailWord_1972083).sum := by decide
  have hdescent : baseEnd_1972083 < baseStart_1972083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972094 : List Nat := [4, 2, 3, 1, 1, 2, 3, 7]
def baseStart_1972094 : Nat := 118140960795 + 1972094 * 2 ^ 59
def prefixEnd_1972094 : Nat := 4983230072969 + 3 ^ 40 * 1972094 * 2
def baseEnd_1972094 : Nat := 37504893253626385439093

theorem tailTrace_1972094 : CollatzResearch.WordTrace tailWord_1972094 prefixEnd_1972094 37504893253626385439093 := by
  unfold tailWord_1972094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8991022164680964960718417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47952118211631813123831557 8991022164680964960718417)
  ·
    refine ⟨6743266623510723720538813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8991022164680964960718417 6743266623510723720538813)
    ·
      refine ⟨2528724983816521395202055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6743266623510723720538813 2528724983816521395202055)
      ·
        refine ⟨3793087475724782092803083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528724983816521395202055 3793087475724782092803083)
        ·
          refine ⟨5689631213587173139204625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793087475724782092803083 5689631213587173139204625)
          ·
            refine ⟨4267223410190379854403469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5689631213587173139204625 4267223410190379854403469)
            ·
              refine ⟨1600208778821392445401301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4267223410190379854403469 1600208778821392445401301)
              ·
                refine ⟨37504893253626385439093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1600208778821392445401301 37504893253626385439093)
                ·
                  rfl

theorem cell23_1972094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_1972094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972094 prefixEnd_1972094 := by exact prefixLift 1972094
  have htrace : WordTrace (prefixWord ++ tailWord_1972094) baseStart_1972094 baseEnd_1972094 := by
    simpa [prefixWord, tailWord_1972094, baseEnd_1972094] using wordTrace_append hprefix tailTrace_1972094
  have hstable : (prefixWord ++ tailWord_1972094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972094).length < 2 ^ (prefixWord ++ tailWord_1972094).sum := by decide
  have hdescent : baseEnd_1972094 < baseStart_1972094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972184 : List Nat := [2, 1, 2, 2, 2, 2, 5, 2, 5]
def baseStart_1972184 : Nat := 118140960795 + 1972184 * 2 ^ 59
def prefixEnd_1972184 : Nat := 4983230072969 + 3 ^ 40 * 1972184 * 2
def baseEnd_1972184 : Nat := 112519814567424117192233

theorem tailTrace_1972184 : CollatzResearch.WordTrace tailWord_1972184 prefixEnd_1972184 112519814567424117192233 := by
  unfold tailWord_1972184
  simp only [CollatzResearch.WordTrace]
  refine ⟨35965729943560832528261803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47954306591414443371015737 35965729943560832528261803)
  ·
    refine ⟨53948594915341248792392705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35965729943560832528261803 53948594915341248792392705)
    ·
      refine ⟨40461446186505936594294529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53948594915341248792392705 40461446186505936594294529)
      ·
        refine ⟨30346084639879452445720897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40461446186505936594294529 30346084639879452445720897)
        ·
          refine ⟨22759563479909589334290673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30346084639879452445720897 22759563479909589334290673)
          ·
            refine ⟨17069672609932192000718005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22759563479909589334290673 17069672609932192000718005)
            ·
              refine ⟨1600281807181143000067313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17069672609932192000718005 1600281807181143000067313)
              ·
                refine ⟨1200211355385857250050485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600281807181143000067313 1200211355385857250050485)
                ·
                  refine ⟨112519814567424117192233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1200211355385857250050485 112519814567424117192233)
                  ·
                    rfl

theorem cell23_1972184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 5].length) (baseStart_1972184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972184 prefixEnd_1972184 := by exact prefixLift 1972184
  have htrace : WordTrace (prefixWord ++ tailWord_1972184) baseStart_1972184 baseEnd_1972184 := by
    simpa [prefixWord, tailWord_1972184, baseEnd_1972184] using wordTrace_append hprefix tailTrace_1972184
  have hstable : (prefixWord ++ tailWord_1972184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972184).length < 2 ^ (prefixWord ++ tailWord_1972184).sum := by decide
  have hdescent : baseEnd_1972184 < baseStart_1972184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972217 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1972217 : Nat := 118140960795 + 1972217 * 2 ^ 59
def prefixEnd_1972217 : Nat := 4983230072969 + 3 ^ 40 * 1972217 * 2
def baseEnd_1972217 : Nat := 1012695275968415425617445

theorem tailTrace_1972217 : CollatzResearch.WordTrace tailWord_1972217 prefixEnd_1972217 1012695275968415425617445 := by
  unfold tailWord_1972217
  simp only [CollatzResearch.WordTrace]
  refine ⟨71932663496002111692474905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47955108997334741128316603 71932663496002111692474905)
  ·
    refine ⟨53949497622001583769356179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71932663496002111692474905 53949497622001583769356179)
    ·
      refine ⟨80924246433002375654034269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53949497622001583769356179 80924246433002375654034269)
      ·
        refine ⟨30346592412375890870262851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80924246433002375654034269 30346592412375890870262851)
        ·
          refine ⟨45519888618563836305394277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30346592412375890870262851 45519888618563836305394277)
          ·
            refine ⟨8534979115980719307261427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45519888618563836305394277 8534979115980719307261427)
            ·
              refine ⟨12802468673971078960892141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534979115980719307261427 12802468673971078960892141)
              ·
                refine ⟨4800925752739154610334553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12802468673971078960892141 4800925752739154610334553)
                ·
                  refine ⟨3600694314554365957750915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4800925752739154610334553 3600694314554365957750915)
                  ·
                    refine ⟨5401041471831548936626373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3600694314554365957750915 5401041471831548936626373)
                    ·
                      refine ⟨1012695275968415425617445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5401041471831548936626373 1012695275968415425617445)
                      ·
                        rfl

theorem cell23_1972217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1972217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972217 prefixEnd_1972217 := by exact prefixLift 1972217
  have htrace : WordTrace (prefixWord ++ tailWord_1972217) baseStart_1972217 baseEnd_1972217 := by
    simpa [prefixWord, tailWord_1972217, baseEnd_1972217] using wordTrace_append hprefix tailTrace_1972217
  have hstable : (prefixWord ++ tailWord_1972217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972217).length < 2 ^ (prefixWord ++ tailWord_1972217).sum := by decide
  have hdescent : baseEnd_1972217 < baseStart_1972217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972278 : List Nat := [5, 1, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1972278 : Nat := 118140960795 + 1972278 * 2 ^ 59
def prefixEnd_1972278 : Nat := 4983230072969 + 3 ^ 40 * 1972278 * 2
def baseEnd_1972278 : Nat := 337575532762779895651555

theorem tailTrace_1972278 : CollatzResearch.WordTrace tailWord_1972278 prefixEnd_1972278 337575532762779895651555 := by
  unfold tailWord_1972278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495930521798819944402843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47956592232520746073630325 4495930521798819944402843)
  ·
    refine ⟨6743895782698229916604265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4495930521798819944402843 6743895782698229916604265)
    ·
      refine ⟨5057921837023672437453199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6743895782698229916604265 5057921837023672437453199)
      ·
        refine ⟨7586882755535508656179799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5057921837023672437453199 7586882755535508656179799)
        ·
          refine ⟨11380324133303262984269699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7586882755535508656179799 11380324133303262984269699)
          ·
            refine ⟨17070486199954894476404549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11380324133303262984269699 17070486199954894476404549)
            ·
              refine ⟨3200716162491542714325853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17070486199954894476404549 3200716162491542714325853)
              ·
                refine ⟨1200268560934328517872195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3200716162491542714325853 1200268560934328517872195)
                ·
                  refine ⟨1800402841401492776808293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200268560934328517872195 1800402841401492776808293)
                  ·
                    refine ⟨337575532762779895651555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1800402841401492776808293 337575532762779895651555)
                    ·
                      rfl

theorem cell23_1972278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1972278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972278 prefixEnd_1972278 := by exact prefixLift 1972278
  have htrace : WordTrace (prefixWord ++ tailWord_1972278) baseStart_1972278 baseEnd_1972278 := by
    simpa [prefixWord, tailWord_1972278, baseEnd_1972278] using wordTrace_append hprefix tailTrace_1972278
  have hstable : (prefixWord ++ tailWord_1972278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972278).length < 2 ^ (prefixWord ++ tailWord_1972278).sum := by decide
  have hdescent : baseEnd_1972278 < baseStart_1972278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972284 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1972284 : Nat := 118140960795 + 1972284 * 2 ^ 59
def prefixEnd_1972284 : Nat := 4983230072969 + 3 ^ 40 * 1972284 * 2
def baseEnd_1972284 : Nat := 1012729679172266663479637

theorem tailTrace_1972284 : CollatzResearch.WordTrace tailWord_1972284 prefixEnd_1972284 1012729679172266663479637 := by
  unfold tailWord_1972284
  simp only [CollatzResearch.WordTrace]
  refine ⟨35967553593379691067581953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47956738124506254756775937 35967553593379691067581953)
  ·
    refine ⟨26975665195034768300686465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35967553593379691067581953 26975665195034768300686465)
    ·
      refine ⟨20231748896276076225514849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26975665195034768300686465 20231748896276076225514849)
      ·
        refine ⟨15173811672207057169136137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20231748896276076225514849 15173811672207057169136137)
        ·
          refine ⟨11380358754155292876852103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15173811672207057169136137 11380358754155292876852103)
          ·
            refine ⟨17070538131232939315278155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11380358754155292876852103 17070538131232939315278155)
            ·
              refine ⟨25605807196849408972917233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17070538131232939315278155 25605807196849408972917233)
              ·
                refine ⟨19204355397637056729687925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25605807196849408972917233 19204355397637056729687925)
                ·
                  refine ⟨1800408318528474068408243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19204355397637056729687925 1800408318528474068408243)
                  ·
                    refine ⟨2700612477792711102612365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1800408318528474068408243 2700612477792711102612365)
                    ·
                      refine ⟨1012729679172266663479637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2700612477792711102612365 1012729679172266663479637)
                      ·
                        rfl

theorem cell23_1972284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1972284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972284 prefixEnd_1972284 := by exact prefixLift 1972284
  have htrace : WordTrace (prefixWord ++ tailWord_1972284) baseStart_1972284 baseEnd_1972284 := by
    simpa [prefixWord, tailWord_1972284, baseEnd_1972284] using wordTrace_append hprefix tailTrace_1972284
  have hstable : (prefixWord ++ tailWord_1972284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972284).length < 2 ^ (prefixWord ++ tailWord_1972284).sum := by decide
  have hdescent : baseEnd_1972284 < baseStart_1972284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972294 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1972294 : Nat := 118140960795 + 1972294 * 2 ^ 59
def prefixEnd_1972294 : Nat := 4983230072969 + 3 ^ 40 * 1972294 * 2
def baseEnd_1972294 : Nat := 1012734813978811624354591

theorem tailTrace_1972294 : CollatzResearch.WordTrace tailWord_1972294 prefixEnd_1972294 1012734813978811624354591 := by
  unfold tailWord_1972294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247983497397598557594623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47956981277815435895351957 2247983497397598557594623)
  ·
    refine ⟨3371975246096397836391935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2247983497397598557594623 3371975246096397836391935)
    ·
      refine ⟨5057962869144596754587903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371975246096397836391935 5057962869144596754587903)
      ·
        refine ⟨7586944303716895131881855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5057962869144596754587903 7586944303716895131881855)
        ·
          refine ⟨11380416455575342697822783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7586944303716895131881855 11380416455575342697822783)
          ·
            refine ⟨17070624683363014046734175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11380416455575342697822783 17070624683363014046734175)
            ·
              refine ⟨25605937025044521070101263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17070624683363014046734175 25605937025044521070101263)
              ·
                refine ⟨38408905537566781605151895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25605937025044521070101263 38408905537566781605151895)
                ·
                  refine ⟨57613358306350172407727843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38408905537566781605151895 57613358306350172407727843)
                  ·
                    refine ⟨86420037459525258611591765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57613358306350172407727843 86420037459525258611591765)
                    ·
                      refine ⟨1012734813978811624354591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 86420037459525258611591765 1012734813978811624354591)
                      ·
                        rfl

theorem cell23_1972294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1972294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972294 prefixEnd_1972294 := by exact prefixLift 1972294
  have htrace : WordTrace (prefixWord ++ tailWord_1972294) baseStart_1972294 baseEnd_1972294 := by
    simpa [prefixWord, tailWord_1972294, baseEnd_1972294] using wordTrace_append hprefix tailTrace_1972294
  have hstable : (prefixWord ++ tailWord_1972294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972294).length < 2 ^ (prefixWord ++ tailWord_1972294).sum := by decide
  have hdescent : baseEnd_1972294 < baseStart_1972294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972324 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_1972324 : Nat := 118140960795 + 1972324 * 2 ^ 59
def prefixEnd_1972324 : Nat := 4983230072969 + 3 ^ 40 * 1972324 * 2
def baseEnd_1972324 : Nat := 1012750218398446506979453

theorem tailTrace_1972324 : CollatzResearch.WordTrace tailWord_1972324 prefixEnd_1972324 1012750218398446506979453 := by
  unfold tailWord_1972324
  simp only [CollatzResearch.WordTrace]
  refine ⟨35968283053307234483310013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47957710737742979311080017 35968283053307234483310013)
  ·
    refine ⟨13488106144990212931241255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35968283053307234483310013 13488106144990212931241255)
    ·
      refine ⟨20232159217485319396861883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13488106144990212931241255 20232159217485319396861883)
      ·
        refine ⟨30348238826227979095292825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20232159217485319396861883 30348238826227979095292825)
        ·
          refine ⟨22761179119670984321469619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30348238826227979095292825 22761179119670984321469619)
          ·
            refine ⟨34141768679506476482204429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22761179119670984321469619 34141768679506476482204429)
            ·
              refine ⟨12803163254814928680826661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34141768679506476482204429 12803163254814928680826661)
              ·
                refine ⟨2400593110277799127654999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12803163254814928680826661 2400593110277799127654999)
                ·
                  refine ⟨3600889665416698691482499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400593110277799127654999 3600889665416698691482499)
                  ·
                    refine ⟨5401334498125048037223749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3600889665416698691482499 5401334498125048037223749)
                    ·
                      refine ⟨1012750218398446506979453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5401334498125048037223749 1012750218398446506979453)
                      ·
                        rfl

theorem cell23_1972324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_1972324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972324 prefixEnd_1972324 := by exact prefixLift 1972324
  have htrace : WordTrace (prefixWord ++ tailWord_1972324) baseStart_1972324 baseEnd_1972324 := by
    simpa [prefixWord, tailWord_1972324, baseEnd_1972324] using wordTrace_append hprefix tailTrace_1972324
  have hstable : (prefixWord ++ tailWord_1972324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972324).length < 2 ^ (prefixWord ++ tailWord_1972324).sum := by decide
  have hdescent : baseEnd_1972324 < baseStart_1972324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972327 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1972327 : Nat := 118140960795 + 1972327 * 2 ^ 59
def prefixEnd_1972327 : Nat := 4983230072969 + 3 ^ 40 * 1972327 * 2
def baseEnd_1972327 : Nat := 1012751758840409995241939

theorem tailTrace_1972327 : CollatzResearch.WordTrace tailWord_1972327 prefixEnd_1972327 1012751758840409995241939 := by
  unfold tailWord_1972327
  simp only [CollatzResearch.WordTrace]
  refine ⟨71936675525603600478979235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47957783683735733652652823 71936675525603600478979235)
  ·
    refine ⟨107905013288405400718468853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71936675525603600478979235 107905013288405400718468853)
    ·
      refine ⟨10116094995788006317356455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107905013288405400718468853 10116094995788006317356455)
      ·
        refine ⟨15174142493682009476034683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10116094995788006317356455 15174142493682009476034683)
        ·
          refine ⟨22761213740523014214052025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15174142493682009476034683 22761213740523014214052025)
          ·
            refine ⟨17070910305392260660539019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22761213740523014214052025 17070910305392260660539019)
            ·
              refine ⟨25606365458088390990808529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17070910305392260660539019 25606365458088390990808529)
              ·
                refine ⟨19204774093566293243106397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25606365458088390990808529 19204774093566293243106397)
                ·
                  refine ⟨7201790285087359966164899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19204774093566293243106397 7201790285087359966164899)
                  ·
                    refine ⟨10802685427631039949247349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7201790285087359966164899 10802685427631039949247349)
                    ·
                      refine ⟨1012751758840409995241939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10802685427631039949247349 1012751758840409995241939)
                      ·
                        rfl

theorem cell23_1972327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1972327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972327 prefixEnd_1972327 := by exact prefixLift 1972327
  have htrace : WordTrace (prefixWord ++ tailWord_1972327) baseStart_1972327 baseEnd_1972327 := by
    simpa [prefixWord, tailWord_1972327, baseEnd_1972327] using wordTrace_append hprefix tailTrace_1972327
  have hstable : (prefixWord ++ tailWord_1972327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972327).length < 2 ^ (prefixWord ++ tailWord_1972327).sum := by decide
  have hdescent : baseEnd_1972327 < baseStart_1972327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972334 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_1972334 : Nat := 118140960795 + 1972334 * 2 ^ 59
def prefixEnd_1972334 : Nat := 4983230072969 + 3 ^ 40 * 1972334 * 2
def baseEnd_1972334 : Nat := 337585117734997155951469

theorem tailTrace_1972334 : CollatzResearch.WordTrace tailWord_1972334 prefixEnd_1972334 337585117734997155951469 := by
  unfold tailWord_1972334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8992116354572280084310507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47957953891052160449656037 8992116354572280084310507)
  ·
    refine ⟨13488174531858420126465761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8992116354572280084310507 13488174531858420126465761)
    ·
      refine ⟨10116130898893815094849321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13488174531858420126465761 10116130898893815094849321)
      ·
        refine ⟨7587098174170361321136991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10116130898893815094849321 7587098174170361321136991)
        ·
          refine ⟨11380647261255541981705487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7587098174170361321136991 11380647261255541981705487)
          ·
            refine ⟨17070970891883312972558231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11380647261255541981705487 17070970891883312972558231)
            ·
              refine ⟨25606456337824969458837347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17070970891883312972558231 25606456337824969458837347)
              ·
                refine ⟨38409684506737454188256021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25606456337824969458837347 38409684506737454188256021)
                ·
                  refine ⟨1800453961253318165074501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38409684506737454188256021 1800453961253318165074501)
                  ·
                    refine ⟨337585117734997155951469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1800453961253318165074501 337585117734997155951469)
                    ·
                      rfl

theorem cell23_1972334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1972334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972334 prefixEnd_1972334 := by exact prefixLift 1972334
  have htrace : WordTrace (prefixWord ++ tailWord_1972334) baseStart_1972334 baseEnd_1972334 := by
    simpa [prefixWord, tailWord_1972334, baseEnd_1972334] using wordTrace_append hprefix tailTrace_1972334
  have hstable : (prefixWord ++ tailWord_1972334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972334).length < 2 ^ (prefixWord ++ tailWord_1972334).sum := by decide
  have hdescent : baseEnd_1972334 < baseStart_1972334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972337 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_1972337 : Nat := 118140960795 + 1972337 * 2 ^ 59
def prefixEnd_1972337 : Nat := 4983230072969 + 3 ^ 40 * 1972337 * 2
def baseEnd_1972337 : Nat := 1012756893646954956116893

theorem tailTrace_1972337 : CollatzResearch.WordTrace tailWord_1972337 prefixEnd_1972337 1012756893646954956116893 := by
  unfold tailWord_1972337
  simp only [CollatzResearch.WordTrace]
  refine ⟨71937040255567372186843265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47958026837044914791228843 71937040255567372186843265)
  ·
    refine ⟨53952780191675529140132449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71937040255567372186843265 53952780191675529140132449)
    ·
      refine ⟨40464585143756646855099337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53952780191675529140132449 40464585143756646855099337)
      ·
        refine ⟨30348438857817485141324503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40464585143756646855099337 30348438857817485141324503)
        ·
          refine ⟨45522658286726227711986755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30348438857817485141324503 45522658286726227711986755)
          ·
            refine ⟨68283987430089341567980133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45522658286726227711986755 68283987430089341567980133)
            ·
              refine ⟨12803247643141751543996275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68283987430089341567980133 12803247643141751543996275)
              ·
                refine ⟨19204871464712627315994413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12803247643141751543996275 19204871464712627315994413)
                ·
                  refine ⟨7201826799267235243497905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19204871464712627315994413 7201826799267235243497905)
                  ·
                    refine ⟨5401370099450426432623429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7201826799267235243497905 5401370099450426432623429)
                    ·
                      refine ⟨1012756893646954956116893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5401370099450426432623429 1012756893646954956116893)
                      ·
                        rfl

theorem cell23_1972337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_1972337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972337 prefixEnd_1972337 := by exact prefixLift 1972337
  have htrace : WordTrace (prefixWord ++ tailWord_1972337) baseStart_1972337 baseEnd_1972337 := by
    simpa [prefixWord, tailWord_1972337, baseEnd_1972337] using wordTrace_append hprefix tailTrace_1972337
  have hstable : (prefixWord ++ tailWord_1972337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972337).length < 2 ^ (prefixWord ++ tailWord_1972337).sum := by decide
  have hdescent : baseEnd_1972337 < baseStart_1972337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972431 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 1, 4, 2]
def baseStart_1972431 : Nat := 118140960795 + 1972431 * 2 ^ 59
def prefixEnd_1972431 : Nat := 4983230072969 + 3 ^ 40 * 1972431 * 2
def baseEnd_1972431 : Nat := 1012805160828477588341461

theorem tailTrace_1972431 : CollatzResearch.WordTrace tailWord_1972431 prefixEnd_1972431 1012805160828477588341461 := by
  unfold tailWord_1972431
  simp only [CollatzResearch.WordTrace]
  refine ⟨71940468717226826240765147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47960312478151217493843431 71940468717226826240765147)
  ·
    refine ⟨107910703075840239361147721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71940468717226826240765147 107910703075840239361147721)
    ·
      refine ⟨80933027306880179520860791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107910703075840239361147721 80933027306880179520860791)
      ·
        refine ⟨121399540960320269281291187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80933027306880179520860791 121399540960320269281291187)
        ·
          refine ⟨182099311440480403921936781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121399540960320269281291187 182099311440480403921936781)
          ·
            refine ⟨68287241790180151470726293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182099311440480403921936781 68287241790180151470726293)
            ·
              refine ⟨3200964458914694600190295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68287241790180151470726293 3200964458914694600190295)
              ·
                refine ⟨4801446688372041900285443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200964458914694600190295 4801446688372041900285443)
                ·
                  refine ⟨7202170032558062850428165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801446688372041900285443 7202170032558062850428165)
                  ·
                    refine ⟨1350406881104636784455281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202170032558062850428165 1350406881104636784455281)
                    ·
                      refine ⟨1012805160828477588341461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350406881104636784455281 1012805160828477588341461)
                      ·
                        rfl

theorem cell23_1972431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 4, 2].length) (baseStart_1972431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972431 prefixEnd_1972431 := by exact prefixLift 1972431
  have htrace : WordTrace (prefixWord ++ tailWord_1972431) baseStart_1972431 baseEnd_1972431 := by
    simpa [prefixWord, tailWord_1972431, baseEnd_1972431] using wordTrace_append hprefix tailTrace_1972431
  have hstable : (prefixWord ++ tailWord_1972431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972431).length < 2 ^ (prefixWord ++ tailWord_1972431).sum := by decide
  have hdescent : baseEnd_1972431 < baseStart_1972431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972447 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_1972447 : Nat := 118140960795 + 1972447 * 2 ^ 59
def prefixEnd_1972447 : Nat := 4983230072969 + 3 ^ 40 * 1972447 * 2
def baseEnd_1972447 : Nat := 1012813376518949525741387

theorem tailTrace_1972447 : CollatzResearch.WordTrace tailWord_1972447 prefixEnd_1972447 1012813376518949525741387 := by
  unfold tailWord_1972447
  simp only [CollatzResearch.WordTrace]
  refine ⟨71941052285168860973347595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47960701523445907315565063 71941052285168860973347595)
  ·
    refine ⟨107911578427753291460021393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71941052285168860973347595 107911578427753291460021393)
    ·
      refine ⟨80933683820814968595016045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107911578427753291460021393 80933683820814968595016045)
      ·
        refine ⟨30350131432805613223131017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80933683820814968595016045 30350131432805613223131017)
        ·
          refine ⟨22762598574604209917348263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30350131432805613223131017 22762598574604209917348263)
          ·
            refine ⟨34143897861906314876022395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22762598574604209917348263 34143897861906314876022395)
            ·
              refine ⟨51215846792859472314033593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34143897861906314876022395 51215846792859472314033593)
              ·
                refine ⟨38411885094644604235525195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51215846792859472314033593 38411885094644604235525195)
                ·
                  refine ⟨57617827641966906353287793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38411885094644604235525195 57617827641966906353287793)
                  ·
                    refine ⟨43213370731475179764965845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57617827641966906353287793 43213370731475179764965845)
                    ·
                      refine ⟨1012813376518949525741387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43213370731475179764965845 1012813376518949525741387)
                      ·
                        rfl

theorem cell23_1972447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_1972447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972447 prefixEnd_1972447 := by exact prefixLift 1972447
  have htrace : WordTrace (prefixWord ++ tailWord_1972447) baseStart_1972447 baseEnd_1972447 := by
    simpa [prefixWord, tailWord_1972447, baseEnd_1972447] using wordTrace_append hprefix tailTrace_1972447
  have hstable : (prefixWord ++ tailWord_1972447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972447).length < 2 ^ (prefixWord ++ tailWord_1972447).sum := by decide
  have hdescent : baseEnd_1972447 < baseStart_1972447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972504 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1972504 : Nat := 118140960795 + 1972504 * 2 ^ 59
def prefixEnd_1972504 : Nat := 4983230072969 + 3 ^ 40 * 1972504 * 2
def baseEnd_1972504 : Nat := 1012842644916255802728625

theorem tailTrace_1972504 : CollatzResearch.WordTrace tailWord_1972504 prefixEnd_1972504 1012842644916255802728625 := by
  unfold tailWord_1972504
  simp only [CollatzResearch.WordTrace]
  refine ⟨35971565622981179854086283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47962087497308239805448377 35971565622981179854086283)
  ·
    refine ⟨53957348434471769781129425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35971565622981179854086283 53957348434471769781129425)
    ·
      refine ⟨40468011325853827335847069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53957348434471769781129425 40468011325853827335847069)
      ·
        refine ⟨15175504247195185250942651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40468011325853827335847069 15175504247195185250942651)
        ·
          refine ⟨22763256370792777876413977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15175504247195185250942651 22763256370792777876413977)
          ·
            refine ⟨17072442278094583407310483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22763256370792777876413977 17072442278094583407310483)
            ·
              refine ⟨25608663417141875110965725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17072442278094583407310483 25608663417141875110965725)
              ·
                refine ⟨9603248781428203166612147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25608663417141875110965725 9603248781428203166612147)
                ·
                  refine ⟨14404873172142304749918221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9603248781428203166612147 14404873172142304749918221)
                  ·
                    refine ⟨5401827439553364281219333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14404873172142304749918221 5401827439553364281219333)
                    ·
                      refine ⟨1012842644916255802728625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5401827439553364281219333 1012842644916255802728625)
                      ·
                        rfl

theorem cell23_1972504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1972504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972504 prefixEnd_1972504 := by exact prefixLift 1972504
  have htrace : WordTrace (prefixWord ++ tailWord_1972504) baseStart_1972504 baseEnd_1972504 := by
    simpa [prefixWord, tailWord_1972504, baseEnd_1972504] using wordTrace_append hprefix tailTrace_1972504
  have hstable : (prefixWord ++ tailWord_1972504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972504).length < 2 ^ (prefixWord ++ tailWord_1972504).sum := by decide
  have hdescent : baseEnd_1972504 < baseStart_1972504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972578 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1972578 : Nat := 118140960795 + 1972578 * 2 ^ 59
def prefixEnd_1972578 : Nat := 4983230072969 + 3 ^ 40 * 1972578 * 2
def baseEnd_1972578 : Nat := 112542293609409834800365

theorem tailTrace_1972578 : CollatzResearch.WordTrace tailWord_1972578 prefixEnd_1972578 112542293609409834800365 := by
  unfold tailWord_1972578
  simp only [CollatzResearch.WordTrace]
  refine ⟨17986457561923567586591597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47963886831796180230910925 17986457561923567586591597)
  ·
    refine ⟨6744921585721337844971849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17986457561923567586591597 6744921585721337844971849)
    ·
      refine ⟨5058691189291003383728887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6744921585721337844971849 5058691189291003383728887)
      ·
        refine ⟨7588036783936505075593331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5058691189291003383728887 7588036783936505075593331)
        ·
          refine ⟨11382055175904757613389997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588036783936505075593331 11382055175904757613389997)
          ·
            refine ⟨4268270690964284105021249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11382055175904757613389997 4268270690964284105021249)
            ·
              refine ⟨3201203018223213078765937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4268270690964284105021249 3201203018223213078765937)
              ·
                refine ⟨2400902263667409809074453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201203018223213078765937 2400902263667409809074453)
                ·
                  refine ⟨112542293609409834800365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2400902263667409809074453 112542293609409834800365)
                  ·
                    rfl

theorem cell23_1972578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1972578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972578 prefixEnd_1972578 := by exact prefixLift 1972578
  have htrace : WordTrace (prefixWord ++ tailWord_1972578) baseStart_1972578 baseEnd_1972578 := by
    simpa [prefixWord, tailWord_1972578, baseEnd_1972578] using wordTrace_append hprefix tailTrace_1972578
  have hstable : (prefixWord ++ tailWord_1972578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972578).length < 2 ^ (prefixWord ++ tailWord_1972578).sum := by decide
  have hdescent : baseEnd_1972578 < baseStart_1972578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972622 : List Nat := [4, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1972622 : Nat := 118140960795 + 1972622 * 2 ^ 59
def prefixEnd_1972622 : Nat := 4983230072969 + 3 ^ 40 * 1972622 * 2
def baseEnd_1972622 : Nat := 1012903235633486341053083

theorem tailTrace_1972622 : CollatzResearch.WordTrace tailWord_1972622 prefixEnd_1972622 1012903235633486341053083 := by
  unfold tailWord_1972622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8993429382441858232621015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47964956706356577240645413 8993429382441858232621015)
  ·
    refine ⟨13490144073662787348931523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8993429382441858232621015 13490144073662787348931523)
    ·
      refine ⟨20235216110494181023397285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13490144073662787348931523 20235216110494181023397285)
      ·
        refine ⟨3794103020717658941886991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20235216110494181023397285 3794103020717658941886991)
        ·
          refine ⟨5691154531076488412830487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794103020717658941886991 5691154531076488412830487)
          ·
            refine ⟨8536731796614732619245731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691154531076488412830487 8536731796614732619245731)
            ·
              refine ⟨12805097694922098928868597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8536731796614732619245731 12805097694922098928868597)
              ·
                refine ⟨1200477908898946774581431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12805097694922098928868597 1200477908898946774581431)
                ·
                  refine ⟨1800716863348420161872147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200477908898946774581431 1800716863348420161872147)
                  ·
                    refine ⟨2701075295022630242808221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1800716863348420161872147 2701075295022630242808221)
                    ·
                      refine ⟨1012903235633486341053083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2701075295022630242808221 1012903235633486341053083)
                      ·
                        rfl

theorem cell23_1972622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1972622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972622 prefixEnd_1972622 := by exact prefixLift 1972622
  have htrace : WordTrace (prefixWord ++ tailWord_1972622) baseStart_1972622 baseEnd_1972622 := by
    simpa [prefixWord, tailWord_1972622, baseEnd_1972622] using wordTrace_append hprefix tailTrace_1972622
  have hstable : (prefixWord ++ tailWord_1972622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972622).length < 2 ^ (prefixWord ++ tailWord_1972622).sum := by decide
  have hdescent : baseEnd_1972622 < baseStart_1972622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972645 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 3, 2, 2]
def baseStart_1972645 : Nat := 118140960795 + 1972645 * 2 ^ 59
def prefixEnd_1972645 : Nat := 4983230072969 + 3 ^ 40 * 1972645 * 2
def baseEnd_1972645 : Nat := 1012915045688539751065477

theorem tailTrace_1972645 : CollatzResearch.WordTrace tailWord_1972645 prefixEnd_1972645 1012915045688539751065477 := by
  unfold tailWord_1972645
  simp only [CollatzResearch.WordTrace]
  refine ⟨71948273938451540789055389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47965515958967693859370259 71948273938451540789055389)
  ·
    refine ⟨26980602726919327795895771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71948273938451540789055389 26980602726919327795895771)
    ·
      refine ⟨40470904090378991693843657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26980602726919327795895771 40470904090378991693843657)
      ·
        refine ⟨30353178067784243770382743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40470904090378991693843657 30353178067784243770382743)
        ·
          refine ⟨45529767101676365655574115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30353178067784243770382743 45529767101676365655574115)
          ·
            refine ⟨68294650652514548483361173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45529767101676365655574115 68294650652514548483361173)
            ·
              refine ⟨3201311749336619460157555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68294650652514548483361173 3201311749336619460157555)
              ·
                refine ⟨4801967624004929190236333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201311749336619460157555 4801967624004929190236333)
                ·
                  refine ⟨1800737859001848446338625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4801967624004929190236333 1800737859001848446338625)
                  ·
                    refine ⟨1350553394251386334753969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1800737859001848446338625 1350553394251386334753969)
                    ·
                      refine ⟨1012915045688539751065477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350553394251386334753969 1012915045688539751065477)
                      ·
                        rfl

theorem cell23_1972645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_1972645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972645 prefixEnd_1972645 := by exact prefixLift 1972645
  have htrace : WordTrace (prefixWord ++ tailWord_1972645) baseStart_1972645 baseEnd_1972645 := by
    simpa [prefixWord, tailWord_1972645, baseEnd_1972645] using wordTrace_append hprefix tailTrace_1972645
  have hstable : (prefixWord ++ tailWord_1972645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972645).length < 2 ^ (prefixWord ++ tailWord_1972645).sum := by decide
  have hdescent : baseEnd_1972645 < baseStart_1972645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972648 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1972648 : Nat := 118140960795 + 1972648 * 2 ^ 59
def prefixEnd_1972648 : Nat := 4983230072969 + 3 ^ 40 * 1972648 * 2
def baseEnd_1972648 : Nat := 1012916586130503239327963

theorem tailTrace_1972648 : CollatzResearch.WordTrace tailWord_1972648 prefixEnd_1972648 1012916586130503239327963 := by
  unfold tailWord_1972648
  simp only [CollatzResearch.WordTrace]
  refine ⟨35974191678720336150707299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47965588904960448200943065 35974191678720336150707299)
  ·
    refine ⟨53961287518080504226060949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35974191678720336150707299 53961287518080504226060949)
    ·
      refine ⟨2529435352410023635596607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53961287518080504226060949 2529435352410023635596607)
      ·
        refine ⟨3794153028615035453394911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2529435352410023635596607 3794153028615035453394911)
        ·
          refine ⟨5691229542922553180092367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794153028615035453394911 5691229542922553180092367)
          ·
            refine ⟨8536844314383829770138551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691229542922553180092367 8536844314383829770138551)
            ·
              refine ⟨12805266471575744655207827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8536844314383829770138551 12805266471575744655207827)
              ·
                refine ⟨19207899707363616982811741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12805266471575744655207827 19207899707363616982811741)
                ·
                  refine ⟨7202962390261356368554403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19207899707363616982811741 7202962390261356368554403)
                  ·
                    refine ⟨10804443585392034552831605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7202962390261356368554403 10804443585392034552831605)
                    ·
                      refine ⟨1012916586130503239327963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10804443585392034552831605 1012916586130503239327963)
                      ·
                        rfl

theorem cell23_1972648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1972648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972648 prefixEnd_1972648 := by exact prefixLift 1972648
  have htrace : WordTrace (prefixWord ++ tailWord_1972648) baseStart_1972648 baseEnd_1972648 := by
    simpa [prefixWord, tailWord_1972648, baseEnd_1972648] using wordTrace_append hprefix tailTrace_1972648
  have hstable : (prefixWord ++ tailWord_1972648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972648).length < 2 ^ (prefixWord ++ tailWord_1972648).sum := by decide
  have hdescent : baseEnd_1972648 < baseStart_1972648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972665 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1972665 : Nat := 118140960795 + 1972665 * 2 ^ 59
def prefixEnd_1972665 : Nat := 4983230072969 + 3 ^ 40 * 1972665 * 2
def baseEnd_1972665 : Nat := 1012925315301629672815385

theorem tailTrace_1972665 : CollatzResearch.WordTrace tailWord_1972665 prefixEnd_1972665 1012925315301629672815385 := by
  unfold tailWord_1972665
  simp only [CollatzResearch.WordTrace]
  refine ⟨71949003398379084204783449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47966002265586056136522299 71949003398379084204783449)
  ·
    refine ⟨53961752548784313153587587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71949003398379084204783449 53961752548784313153587587)
    ·
      refine ⟨80942628823176469730381381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53961752548784313153587587 80942628823176469730381381)
      ·
        refine ⟨15176742904345588074446509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80942628823176469730381381 15176742904345588074446509)
        ·
          refine ⟨5691278589129595527917441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15176742904345588074446509 5691278589129595527917441)
          ·
            refine ⟨4268458941847196645938081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5691278589129595527917441 4268458941847196645938081)
            ·
              refine ⟨3201344206385397484453561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4268458941847196645938081 3201344206385397484453561)
              ·
                refine ⟨2401008154789048113340171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201344206385397484453561 2401008154789048113340171)
                ·
                  refine ⟨3601512232183572170010257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401008154789048113340171 3601512232183572170010257)
                  ·
                    refine ⟨2701134174137679127507693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3601512232183572170010257 2701134174137679127507693)
                    ·
                      refine ⟨1012925315301629672815385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2701134174137679127507693 1012925315301629672815385)
                      ·
                        rfl

theorem cell23_1972665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1972665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972665 prefixEnd_1972665 := by exact prefixLift 1972665
  have htrace : WordTrace (prefixWord ++ tailWord_1972665) baseStart_1972665 baseEnd_1972665 := by
    simpa [prefixWord, tailWord_1972665, baseEnd_1972665] using wordTrace_append hprefix tailTrace_1972665
  have hstable : (prefixWord ++ tailWord_1972665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972665).length < 2 ^ (prefixWord ++ tailWord_1972665).sum := by decide
  have hdescent : baseEnd_1972665 < baseStart_1972665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972668 : List Nat := [2, 2, 2, 4, 1, 1, 4, 7]
def baseStart_1972668 : Nat := 118140960795 + 1972668 * 2 ^ 59
def prefixEnd_1972668 : Nat := 4983230072969 + 3 ^ 40 * 1972668 * 2
def baseEnd_1972668 : Nat := 37515809471984931891773

theorem tailTrace_1972668 : CollatzResearch.WordTrace tailWord_1972668 prefixEnd_1972668 37515809471984931891773 := by
  unfold tailWord_1972668
  simp only [CollatzResearch.WordTrace]
  refine ⟨35974556408684107858571329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47966075211578810478095105 35974556408684107858571329)
  ·
    refine ⟨26980917306513080893928497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35974556408684107858571329 26980917306513080893928497)
    ·
      refine ⟨20235687979884810670446373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26980917306513080893928497 20235687979884810670446373)
      ·
        refine ⟨3794191496228402000708695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20235687979884810670446373 3794191496228402000708695)
        ·
          refine ⟨5691287244342603001063043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794191496228402000708695 5691287244342603001063043)
          ·
            refine ⟨8536930866513904501594565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691287244342603001063043 8536930866513904501594565)
            ·
              refine ⟨1600674537471357094048981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8536930866513904501594565 1600674537471357094048981)
              ·
                refine ⟨37515809471984931891773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1600674537471357094048981 37515809471984931891773)
                ·
                  rfl

theorem cell23_1972668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 7].length) (baseStart_1972668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972668 prefixEnd_1972668 := by exact prefixLift 1972668
  have htrace : WordTrace (prefixWord ++ tailWord_1972668) baseStart_1972668 baseEnd_1972668 := by
    simpa [prefixWord, tailWord_1972668, baseEnd_1972668] using wordTrace_append hprefix tailTrace_1972668
  have hstable : (prefixWord ++ tailWord_1972668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972668).length < 2 ^ (prefixWord ++ tailWord_1972668).sum := by decide
  have hdescent : baseEnd_1972668 < baseStart_1972668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972673 : List Nat := [1, 2, 7, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1972673 : Nat := 118140960795 + 1972673 * 2 ^ 59
def prefixEnd_1972673 : Nat := 4983230072969 + 3 ^ 40 * 1972673 * 2
def baseEnd_1972673 : Nat := 1012929423146865641515349

theorem tailTrace_1972673 : CollatzResearch.WordTrace tailWord_1972673 prefixEnd_1972673 1012929423146865641515349 := by
  unfold tailWord_1972673
  simp only [CollatzResearch.WordTrace]
  refine ⟨71949295182350101571074673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47966196788233401047383115 71949295182350101571074673)
  ·
    refine ⟨53961971386762576178306005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71949295182350101571074673 53961971386762576178306005)
    ·
      refine ⟨1264733704377247879179047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 53961971386762576178306005 1264733704377247879179047)
      ·
        refine ⟨1897100556565871818768571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264733704377247879179047 1897100556565871818768571)
        ·
          refine ⟨2845650834848807728152857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897100556565871818768571 2845650834848807728152857)
          ·
            refine ⟨2134238126136605796114643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845650834848807728152857 2134238126136605796114643)
            ·
              refine ⟨3201357189204908694171965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134238126136605796114643 3201357189204908694171965)
              ·
                refine ⟨1200508945951840760314487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3201357189204908694171965 1200508945951840760314487)
                ·
                  refine ⟨1800763418927761140471731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200508945951840760314487 1800763418927761140471731)
                  ·
                    refine ⟨2701145128391641710707597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1800763418927761140471731 2701145128391641710707597)
                    ·
                      refine ⟨1012929423146865641515349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2701145128391641710707597 1012929423146865641515349)
                      ·
                        rfl

theorem cell23_1972673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1972673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972673 prefixEnd_1972673 := by exact prefixLift 1972673
  have htrace : WordTrace (prefixWord ++ tailWord_1972673) baseStart_1972673 baseEnd_1972673 := by
    simpa [prefixWord, tailWord_1972673, baseEnd_1972673] using wordTrace_append hprefix tailTrace_1972673
  have hstable : (prefixWord ++ tailWord_1972673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972673).length < 2 ^ (prefixWord ++ tailWord_1972673).sum := by decide
  have hdescent : baseEnd_1972673 < baseStart_1972673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972679 : List Nat := [1, 1, 4, 1, 1, 6, 1, 3, 1, 2, 2]
def baseStart_1972679 : Nat := 118140960795 + 1972679 * 2 ^ 59
def prefixEnd_1972679 : Nat := 4983230072969 + 3 ^ 40 * 1972679 * 2
def baseEnd_1972679 : Nat := 1012932504030792618040321

theorem tailTrace_1972679 : CollatzResearch.WordTrace tailWord_1972679 prefixEnd_1972679 1012932504030792618040321 := by
  unfold tailWord_1972679
  simp only [CollatzResearch.WordTrace]
  refine ⟨71949514020328364595793091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47966342680218909730528727 71949514020328364595793091)
  ·
    refine ⟨107924271030492546893689637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71949514020328364595793091 107924271030492546893689637)
    ·
      refine ⟨20235800818217352542566807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107924271030492546893689637 20235800818217352542566807)
      ·
        refine ⟨30353701227326028813850211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20235800818217352542566807 30353701227326028813850211)
        ·
          refine ⟨45530551840989043220775317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30353701227326028813850211 45530551840989043220775317)
          ·
            refine ⟨2134244617546361400973843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45530551840989043220775317 2134244617546361400973843)
            ·
              refine ⟨3201366926319542101460765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134244617546361400973843 3201366926319542101460765)
              ·
                refine ⟨1200512597369828288047787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3201366926319542101460765 1200512597369828288047787)
                ·
                  refine ⟨1800768896054742432071681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200512597369828288047787 1800768896054742432071681)
                  ·
                    refine ⟨1350576672041056824053761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1800768896054742432071681 1350576672041056824053761)
                    ·
                      refine ⟨1012932504030792618040321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350576672041056824053761 1012932504030792618040321)
                      ·
                        rfl

theorem cell23_1972679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_1972679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972679 prefixEnd_1972679 := by exact prefixLift 1972679
  have htrace : WordTrace (prefixWord ++ tailWord_1972679) baseStart_1972679 baseEnd_1972679 := by
    simpa [prefixWord, tailWord_1972679, baseEnd_1972679] using wordTrace_append hprefix tailTrace_1972679
  have hstable : (prefixWord ++ tailWord_1972679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972679).length < 2 ^ (prefixWord ++ tailWord_1972679).sum := by decide
  have hdescent : baseEnd_1972679 < baseStart_1972679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972706 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1972706 : Nat := 118140960795 + 1972706 * 2 ^ 59
def prefixEnd_1972706 : Nat := 4983230072969 + 3 ^ 40 * 1972706 * 2
def baseEnd_1972706 : Nat := 337648789336154670800899

theorem tailTrace_1972706 : CollatzResearch.WordTrace tailWord_1972706 prefixEnd_1972706 337648789336154670800899 := by
  unfold tailWord_1972706
  simp only [CollatzResearch.WordTrace]
  refine ⟨17987624697807637051756493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47966999194153698804683981 17987624697807637051756493)
  ·
    refine ⟨6745359261677863894408685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17987624697807637051756493 6745359261677863894408685)
    ·
      refine ⟨2529509723129198960403257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6745359261677863894408685 2529509723129198960403257)
      ·
        refine ⟨1897132292346899220302443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529509723129198960403257 1897132292346899220302443)
        ·
          refine ⟨2845698438520348830453665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897132292346899220302443 2845698438520348830453665)
          ·
            refine ⟨2134273828890261622840249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845698438520348830453665 2134273828890261622840249)
            ·
              refine ⟨1600705371667696217130187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134273828890261622840249 1600705371667696217130187)
              ·
                refine ⟨2401058057501544325695281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600705371667696217130187 2401058057501544325695281)
                ·
                  refine ⟨1800793543126158244271461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2401058057501544325695281 1800793543126158244271461)
                  ·
                    refine ⟨337648789336154670800899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1800793543126158244271461 337648789336154670800899)
                    ·
                      rfl

theorem cell23_1972706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1972706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972706 prefixEnd_1972706 := by exact prefixLift 1972706
  have htrace : WordTrace (prefixWord ++ tailWord_1972706) baseStart_1972706 baseEnd_1972706 := by
    simpa [prefixWord, tailWord_1972706, baseEnd_1972706] using wordTrace_append hprefix tailTrace_1972706
  have hstable : (prefixWord ++ tailWord_1972706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972706).length < 2 ^ (prefixWord ++ tailWord_1972706).sum := by decide
  have hdescent : baseEnd_1972706 < baseStart_1972706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972711 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1972711 : Nat := 118140960795 + 1972711 * 2 ^ 59
def prefixEnd_1972711 : Nat := 4983230072969 + 3 ^ 40 * 1972711 * 2
def baseEnd_1972711 : Nat := 337649645137245497613391

theorem tailTrace_1972711 : CollatzResearch.WordTrace tailWord_1972711 prefixEnd_1972711 337649645137245497613391 := by
  unfold tailWord_1972711
  simp only [CollatzResearch.WordTrace]
  refine ⟨71950681156212434060957987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47967120770808289373971991 71950681156212434060957987)
  ·
    refine ⟨107926021734318651091436981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71950681156212434060957987 107926021734318651091436981)
    ·
      refine ⟨10118064537592373539822217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107926021734318651091436981 10118064537592373539822217)
      ·
        refine ⟨7588548403194280154866663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10118064537592373539822217 7588548403194280154866663)
        ·
          refine ⟨11382822604791420232299995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588548403194280154866663 11382822604791420232299995)
          ·
            refine ⟨17074233907187130348449993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382822604791420232299995 17074233907187130348449993)
            ·
              refine ⟨12805675430390347761337495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17074233907187130348449993 12805675430390347761337495)
              ·
                refine ⟨19208513145585521642006243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12805675430390347761337495 19208513145585521642006243)
                ·
                  refine ⟨28812769718378282463009365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19208513145585521642006243 28812769718378282463009365)
                  ·
                    refine ⟨337649645137245497613391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28812769718378282463009365 337649645137245497613391)
                    ·
                      rfl

theorem cell23_1972711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1972711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972711 prefixEnd_1972711 := by exact prefixLift 1972711
  have htrace : WordTrace (prefixWord ++ tailWord_1972711) baseStart_1972711 baseEnd_1972711 := by
    simpa [prefixWord, tailWord_1972711, baseEnd_1972711] using wordTrace_append hprefix tailTrace_1972711
  have hstable : (prefixWord ++ tailWord_1972711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972711).length < 2 ^ (prefixWord ++ tailWord_1972711).sum := by decide
  have hdescent : baseEnd_1972711 < baseStart_1972711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972712 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_1972712 : Nat := 118140960795 + 1972712 * 2 ^ 59
def prefixEnd_1972712 : Nat := 4983230072969 + 3 ^ 40 * 1972712 * 2
def baseEnd_1972712 : Nat := 1012949448892390988927669

theorem tailTrace_1972712 : CollatzResearch.WordTrace tailWord_1972712 prefixEnd_1972712 1012949448892390988927669 := by
  unfold tailWord_1972712
  simp only [CollatzResearch.WordTrace]
  refine ⟨35975358814604405615872195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47967145086139207487829593 35975358814604405615872195)
  ·
    refine ⟨53963038221906608423808293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35975358814604405615872195 53963038221906608423808293)
    ·
      refine ⟨10118069666607489079464055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53963038221906608423808293 10118069666607489079464055)
      ·
        refine ⟨15177104499911233619196083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10118069666607489079464055 15177104499911233619196083)
        ·
          refine ⟨22765656749866850428794125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15177104499911233619196083 22765656749866850428794125)
          ·
            refine ⟨8537121281200068910797797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22765656749866850428794125 8537121281200068910797797)
            ·
              refine ⟨1600710240225012920774587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8537121281200068910797797 1600710240225012920774587)
              ·
                refine ⟨2401065360337519381161881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600710240225012920774587 2401065360337519381161881)
                ·
                  refine ⟨1800799020253139535871411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2401065360337519381161881 1800799020253139535871411)
                  ·
                    refine ⟨2701198530379709303807117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1800799020253139535871411 2701198530379709303807117)
                    ·
                      refine ⟨1012949448892390988927669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2701198530379709303807117 1012949448892390988927669)
                      ·
                        rfl

theorem cell23_1972712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_1972712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972712 prefixEnd_1972712 := by exact prefixLift 1972712
  have htrace : WordTrace (prefixWord ++ tailWord_1972712) baseStart_1972712 baseEnd_1972712 := by
    simpa [prefixWord, tailWord_1972712, baseEnd_1972712] using wordTrace_append hprefix tailTrace_1972712
  have hstable : (prefixWord ++ tailWord_1972712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972712).length < 2 ^ (prefixWord ++ tailWord_1972712).sum := by decide
  have hdescent : baseEnd_1972712 < baseStart_1972712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972721 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_1972721 : Nat := 118140960795 + 1972721 * 2 ^ 59
def prefixEnd_1972721 : Nat := 4983230072969 + 3 ^ 40 * 1972721 * 2
def baseEnd_1972721 : Nat := 1012954070218281453715127

theorem tailTrace_1972721 : CollatzResearch.WordTrace tailWord_1972721 prefixEnd_1972721 1012954070218281453715127 := by
  unfold tailWord_1972721
  simp only [CollatzResearch.WordTrace]
  refine ⟨71951045886176205768822017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47967363924117470512548011 71951045886176205768822017)
  ·
    refine ⟨53963284414632154326616513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71951045886176205768822017 53963284414632154326616513)
    ·
      refine ⟨40472463310974115744962385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53963284414632154326616513 40472463310974115744962385)
      ·
        refine ⟨30354347483230586808721789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40472463310974115744962385 30354347483230586808721789)
        ·
          refine ⟨11382880306211470053270671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30354347483230586808721789 11382880306211470053270671)
          ·
            refine ⟨17074320459317205079906007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382880306211470053270671 17074320459317205079906007)
            ·
              refine ⟨25611480688975807619859011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17074320459317205079906007 25611480688975807619859011)
              ·
                refine ⟨38417221033463711429788517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25611480688975807619859011 38417221033463711429788517)
                ·
                  refine ⟨7203228943774445893085347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38417221033463711429788517 7203228943774445893085347)
                  ·
                    refine ⟨10804843415661668839628021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7203228943774445893085347 10804843415661668839628021)
                    ·
                      refine ⟨1012954070218281453715127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10804843415661668839628021 1012954070218281453715127)
                      ·
                        rfl

theorem cell23_1972721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_1972721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972721 prefixEnd_1972721 := by exact prefixLift 1972721
  have htrace : WordTrace (prefixWord ++ tailWord_1972721) baseStart_1972721 baseEnd_1972721 := by
    simpa [prefixWord, tailWord_1972721, baseEnd_1972721] using wordTrace_append hprefix tailTrace_1972721
  have hstable : (prefixWord ++ tailWord_1972721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972721).length < 2 ^ (prefixWord ++ tailWord_1972721).sum := by decide
  have hdescent : baseEnd_1972721 < baseStart_1972721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972722 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_1972722 : Nat := 118140960795 + 1972722 * 2 ^ 59
def prefixEnd_1972722 : Nat := 4983230072969 + 3 ^ 40 * 1972722 * 2
def baseEnd_1972722 : Nat := 1012954583698935949802623

theorem tailTrace_1972722 : CollatzResearch.WordTrace tailWord_1972722 prefixEnd_1972722 1012954583698935949802623 := by
  unfold tailWord_1972722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17987770589793145734902105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47967388239448388626405613 17987770589793145734902105)
  ·
    refine ⟨13490827942344859301176579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17987770589793145734902105 13490827942344859301176579)
    ·
      refine ⟨20236241913517288951764869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13490827942344859301176579 20236241913517288951764869)
      ·
        refine ⟨3794295358784491678455913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20236241913517288951764869 3794295358784491678455913)
        ·
          refine ⟨2845721519088368758841935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3794295358784491678455913 2845721519088368758841935)
          ·
            refine ⟨4268582278632553138262903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845721519088368758841935 4268582278632553138262903)
            ·
              refine ⟨6402873417948829707394355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268582278632553138262903 6402873417948829707394355)
              ·
                refine ⟨9604310126923244561091533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6402873417948829707394355 9604310126923244561091533)
                ·
                  refine ⟨3601616297596216710409325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9604310126923244561091533 3601616297596216710409325)
                  ·
                    refine ⟨1350606111598581266403497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3601616297596216710409325 1350606111598581266403497)
                    ·
                      refine ⟨1012954583698935949802623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350606111598581266403497 1012954583698935949802623)
                      ·
                        rfl

theorem cell23_1972722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_1972722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972722 prefixEnd_1972722 := by exact prefixLift 1972722
  have htrace : WordTrace (prefixWord ++ tailWord_1972722) baseStart_1972722 baseEnd_1972722 := by
    simpa [prefixWord, tailWord_1972722, baseEnd_1972722] using wordTrace_append hprefix tailTrace_1972722
  have hstable : (prefixWord ++ tailWord_1972722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972722).length < 2 ^ (prefixWord ++ tailWord_1972722).sum := by decide
  have hdescent : baseEnd_1972722 < baseStart_1972722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972808 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1972808 : Nat := 118140960795 + 1972808 * 2 ^ 59
def prefixEnd_1972808 : Nat := 4983230072969 + 3 ^ 40 * 1972808 * 2
def baseEnd_1972808 : Nat := 1012998743035222613327227

theorem tailTrace_1972808 : CollatzResearch.WordTrace tailWord_1972808 prefixEnd_1972808 1012998743035222613327227 := by
  unfold tailWord_1972808
  simp only [CollatzResearch.WordTrace]
  refine ⟨35977109518430509813619539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47969479357907346418159385 35977109518430509813619539)
  ·
    refine ⟨53965664277645764720429309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35977109518430509813619539 53965664277645764720429309)
    ·
      refine ⟨20237124104117161770160991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53965664277645764720429309 20237124104117161770160991)
      ·
        refine ⟨30355686156175742655241487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20237124104117161770160991 30355686156175742655241487)
        ·
          refine ⟨45533529234263613982862231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30355686156175742655241487 45533529234263613982862231)
          ·
            refine ⟨68300293851395420974293347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45533529234263613982862231 68300293851395420974293347)
            ·
              refine ⟨102450440777093131461440021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68300293851395420974293347 102450440777093131461440021)
              ·
                refine ⟨4802364411426240537255001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102450440777093131461440021 4802364411426240537255001)
                ·
                  refine ⟨3601773308569680402941251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4802364411426240537255001 3601773308569680402941251)
                  ·
                    refine ⟨5402659962854520604411877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3601773308569680402941251 5402659962854520604411877)
                    ·
                      refine ⟨1012998743035222613327227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5402659962854520604411877 1012998743035222613327227)
                      ·
                        rfl

theorem cell23_1972808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1972808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972808 prefixEnd_1972808 := by exact prefixLift 1972808
  have htrace : WordTrace (prefixWord ++ tailWord_1972808) baseStart_1972808 baseEnd_1972808 := by
    simpa [prefixWord, tailWord_1972808, baseEnd_1972808] using wordTrace_append hprefix tailTrace_1972808
  have hstable : (prefixWord ++ tailWord_1972808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972808).length < 2 ^ (prefixWord ++ tailWord_1972808).sum := by decide
  have hdescent : baseEnd_1972808 < baseStart_1972808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972811 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 5]
def baseStart_1972811 : Nat := 118140960795 + 1972811 * 2 ^ 59
def prefixEnd_1972811 : Nat := 4983230072969 + 3 ^ 40 * 1972811 * 2
def baseEnd_1972811 : Nat := 1013000283477186101589713

theorem tailTrace_1972811 : CollatzResearch.WordTrace tailWord_1972811 prefixEnd_1972811 1013000283477186101589713 := by
  unfold tailWord_1972811
  simp only [CollatzResearch.WordTrace]
  refine ⟨71954328455850151139598287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47969552303900100759732191 71954328455850151139598287)
  ·
    refine ⟨107931492683775226709397431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71954328455850151139598287 107931492683775226709397431)
    ·
      refine ⟨161897239025662840064096147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107931492683775226709397431 161897239025662840064096147)
      ·
        refine ⟨242845858538494260096144221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161897239025662840064096147 242845858538494260096144221)
        ·
          refine ⟨91067196951935347536054083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242845858538494260096144221 91067196951935347536054083)
          ·
            refine ⟨136600795427903021304081125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91067196951935347536054083 136600795427903021304081125)
            ·
              refine ⟨25612649142731816494515211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136600795427903021304081125 25612649142731816494515211)
              ·
                refine ⟨38418973714097724741772817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25612649142731816494515211 38418973714097724741772817)
                ·
                  refine ⟨28814230285573293556329613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38418973714097724741772817 28814230285573293556329613)
                  ·
                    refine ⟨10805336357089985083623605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28814230285573293556329613 10805336357089985083623605)
                    ·
                      refine ⟨1013000283477186101589713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10805336357089985083623605 1013000283477186101589713)
                      ·
                        rfl

theorem cell23_1972811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_1972811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972811 prefixEnd_1972811 := by exact prefixLift 1972811
  have htrace : WordTrace (prefixWord ++ tailWord_1972811) baseStart_1972811 baseEnd_1972811 := by
    simpa [prefixWord, tailWord_1972811, baseEnd_1972811] using wordTrace_append hprefix tailTrace_1972811
  have hstable : (prefixWord ++ tailWord_1972811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972811).length < 2 ^ (prefixWord ++ tailWord_1972811).sum := by decide
  have hdescent : baseEnd_1972811 < baseStart_1972811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972845 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1972845 : Nat := 118140960795 + 1972845 * 2 ^ 59
def prefixEnd_1972845 : Nat := 4983230072969 + 3 ^ 40 * 1972845 * 2
def baseEnd_1972845 : Nat := 1013017741819438968564557

theorem tailTrace_1972845 : CollatzResearch.WordTrace tailWord_1972845 prefixEnd_1972845 1013017741819438968564557 := by
  unfold tailWord_1972845
  simp only [CollatzResearch.WordTrace]
  refine ⟨71955568537726974946335989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47970379025151316630890659 71955568537726974946335989)
  ·
    refine ⟨6745834550411903901218999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71955568537726974946335989 6745834550411903901218999)
    ·
      refine ⟨10118751825617855851828499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6745834550411903901218999 10118751825617855851828499)
      ·
        refine ⟨15178127738426783777742749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10118751825617855851828499 15178127738426783777742749)
        ·
          refine ⟨5691797901910043916653531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15178127738426783777742749 5691797901910043916653531)
          ·
            refine ⟨8537696852865065874980297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691797901910043916653531 8537696852865065874980297)
            ·
              refine ⟨6403272639648799406235223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8537696852865065874980297 6403272639648799406235223)
              ·
                refine ⟨9604908959473199109352835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403272639648799406235223 9604908959473199109352835)
                ·
                  refine ⟨14407363439209798664029253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9604908959473199109352835 14407363439209798664029253)
                  ·
                    refine ⟨2701380644851837249505485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14407363439209798664029253 2701380644851837249505485)
                    ·
                      refine ⟨1013017741819438968564557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2701380644851837249505485 1013017741819438968564557)
                      ·
                        rfl

theorem cell23_1972845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1972845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972845 prefixEnd_1972845 := by exact prefixLift 1972845
  have htrace : WordTrace (prefixWord ++ tailWord_1972845) baseStart_1972845 baseEnd_1972845 := by
    simpa [prefixWord, tailWord_1972845, baseEnd_1972845] using wordTrace_append hprefix tailTrace_1972845
  have hstable : (prefixWord ++ tailWord_1972845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972845).length < 2 ^ (prefixWord ++ tailWord_1972845).sum := by decide
  have hdescent : baseEnd_1972845 < baseStart_1972845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972851 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 8]
def baseStart_1972851 : Nat := 118140960795 + 1972851 * 2 ^ 59
def prefixEnd_1972851 : Nat := 4983230072969 + 3 ^ 40 * 1972851 * 2
def baseEnd_1972851 : Nat := 1013020822703365945089529

theorem tailTrace_1972851 : CollatzResearch.WordTrace tailWord_1972851 prefixEnd_1972851 1013020822703365945089529 := by
  unfold tailWord_1972851
  simp only [CollatzResearch.WordTrace]
  refine ⟨71955787375705237971054407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47970524917136825314036271 71955787375705237971054407)
  ·
    refine ⟨107933681063557856956581611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71955787375705237971054407 107933681063557856956581611)
    ·
      refine ⟨161900521595336785434872417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107933681063557856956581611 161900521595336785434872417)
      ·
        refine ⟨121425391196502589076154313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161900521595336785434872417 121425391196502589076154313)
        ·
          refine ⟨91069043397376941807115735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121425391196502589076154313 91069043397376941807115735)
          ·
            refine ⟨136603565096065412710673603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91069043397376941807115735 136603565096065412710673603)
            ·
              refine ⟨204905347644098119066010405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136603565096065412710673603 204905347644098119066010405)
              ·
                refine ⟨38419752683268397324876951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204905347644098119066010405 38419752683268397324876951)
                ·
                  refine ⟨57629629024902595987315427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38419752683268397324876951 57629629024902595987315427)
                  ·
                    refine ⟨86444443537353893980973141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57629629024902595987315427 86444443537353893980973141)
                    ·
                      refine ⟨1013020822703365945089529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 86444443537353893980973141 1013020822703365945089529)
                      ·
                        rfl

theorem cell23_1972851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_1972851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972851 prefixEnd_1972851 := by exact prefixLift 1972851
  have htrace : WordTrace (prefixWord ++ tailWord_1972851) baseStart_1972851 baseEnd_1972851 := by
    simpa [prefixWord, tailWord_1972851, baseEnd_1972851] using wordTrace_append hprefix tailTrace_1972851
  have hstable : (prefixWord ++ tailWord_1972851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972851).length < 2 ^ (prefixWord ++ tailWord_1972851).sum := by decide
  have hdescent : baseEnd_1972851 < baseStart_1972851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972869 : List Nat := [1, 3, 1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_1972869 : Nat := 118140960795 + 1972869 * 2 ^ 59
def prefixEnd_1972869 : Nat := 4983230072969 + 3 ^ 40 * 1972869 * 2
def baseEnd_1972869 : Nat := 337676688451715624888149

theorem tailTrace_1972869 : CollatzResearch.WordTrace tailWord_1972869 prefixEnd_1972869 337676688451715624888149 := by
  unfold tailWord_1972869
  simp only [CollatzResearch.WordTrace]
  refine ⟨71956443889640027045209661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47970962593093351363473107 71956443889640027045209661)
  ·
    refine ⟨26983666458615010141953623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71956443889640027045209661 26983666458615010141953623)
    ·
      refine ⟨40475499687922515212930435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26983666458615010141953623 40475499687922515212930435)
      ·
        refine ⟨60713249531883772819395653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40475499687922515212930435 60713249531883772819395653)
        ·
          refine ⟨11383734287228207403636685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60713249531883772819395653 11383734287228207403636685)
          ·
            refine ⟨4268900357710577776363757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11383734287228207403636685 4268900357710577776363757)
            ·
              refine ⟨1600837634141466666136409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4268900357710577776363757 1600837634141466666136409)
              ·
                refine ⟨1200628225606099999602307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600837634141466666136409 1200628225606099999602307)
                ·
                  refine ⟨1800942338409149999403461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200628225606099999602307 1800942338409149999403461)
                  ·
                    refine ⟨337676688451715624888149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1800942338409149999403461 337676688451715624888149)
                    ·
                      rfl

theorem cell23_1972869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_1972869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972869 prefixEnd_1972869 := by exact prefixLift 1972869
  have htrace : WordTrace (prefixWord ++ tailWord_1972869) baseStart_1972869 baseEnd_1972869 := by
    simpa [prefixWord, tailWord_1972869, baseEnd_1972869] using wordTrace_append hprefix tailTrace_1972869
  have hstable : (prefixWord ++ tailWord_1972869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972869).length < 2 ^ (prefixWord ++ tailWord_1972869).sum := by decide
  have hdescent : baseEnd_1972869 < baseStart_1972869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972875 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 3]
def baseStart_1972875 : Nat := 118140960795 + 1972875 * 2 ^ 59
def prefixEnd_1972875 : Nat := 4983230072969 + 3 ^ 40 * 1972875 * 2
def baseEnd_1972875 : Nat := 1013033146239073851189419

theorem tailTrace_1972875 : CollatzResearch.WordTrace tailWord_1972875 prefixEnd_1972875 1013033146239073851189419 := by
  unfold tailWord_1972875
  simp only [CollatzResearch.WordTrace]
  refine ⟨71956662727618290069928079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47971108485078860046618719 71956662727618290069928079)
  ·
    refine ⟨107934994091427435104892119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71956662727618290069928079 107934994091427435104892119)
    ·
      refine ⟨161902491137141152657338179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107934994091427435104892119 161902491137141152657338179)
      ·
        refine ⟨242853736705711728986007269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161902491137141152657338179 242853736705711728986007269)
        ·
          refine ⟨45535075632320949184876363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242853736705711728986007269 45535075632320949184876363)
          ·
            refine ⟨68302613448481423777314545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45535075632320949184876363 68302613448481423777314545)
            ·
              refine ⟨51226960086361067832985909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68302613448481423777314545 51226960086361067832985909)
              ·
                refine ⟨4802527508096350109342429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51226960086361067832985909 4802527508096350109342429)
                ·
                  refine ⟨1800947815536131291003411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4802527508096350109342429 1800947815536131291003411)
                  ·
                    refine ⟨2701421723304196936505117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1800947815536131291003411 2701421723304196936505117)
                    ·
                      refine ⟨1013033146239073851189419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2701421723304196936505117 1013033146239073851189419)
                      ·
                        rfl

theorem cell23_1972875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 3].length) (baseStart_1972875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972875 prefixEnd_1972875 := by exact prefixLift 1972875
  have htrace : WordTrace (prefixWord ++ tailWord_1972875) baseStart_1972875 baseEnd_1972875 := by
    simpa [prefixWord, tailWord_1972875, baseEnd_1972875] using wordTrace_append hprefix tailTrace_1972875
  have hstable : (prefixWord ++ tailWord_1972875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972875).length < 2 ^ (prefixWord ++ tailWord_1972875).sum := by decide
  have hdescent : baseEnd_1972875 < baseStart_1972875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972882 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 6]
def baseStart_1972882 : Nat := 118140960795 + 1972882 * 2 ^ 59
def prefixEnd_1972882 : Nat := 4983230072969 + 3 ^ 40 * 1972882 * 2
def baseEnd_1972882 : Nat := 112559637844850591533543

theorem tailTrace_1972882 : CollatzResearch.WordTrace tailWord_1972882 prefixEnd_1972882 112559637844850591533543 := by
  unfold tailWord_1972882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989229509648232566358225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47971278692395286843621933 17989229509648232566358225)
  ·
    refine ⟨13491922132236174424768669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17989229509648232566358225 13491922132236174424768669)
    ·
      refine ⟨5059470799588565409288251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13491922132236174424768669 5059470799588565409288251)
      ·
        refine ⟨7589206199382848113932377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5059470799588565409288251 7589206199382848113932377)
        ·
          refine ⟨5691904649537136085449283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7589206199382848113932377 5691904649537136085449283)
          ·
            refine ⟨8537856974305704128173925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691904649537136085449283 8537856974305704128173925)
            ·
              refine ⟨1600848182682319524032611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8537856974305704128173925 1600848182682319524032611)
              ·
                refine ⟨2401272274023479286048917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600848182682319524032611 2401272274023479286048917)
                ·
                  refine ⟨112559637844850591533543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2401272274023479286048917 112559637844850591533543)
                  ·
                    rfl

theorem cell23_1972882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_1972882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972882 prefixEnd_1972882 := by exact prefixLift 1972882
  have htrace : WordTrace (prefixWord ++ tailWord_1972882) baseStart_1972882 baseEnd_1972882 := by
    simpa [prefixWord, tailWord_1972882, baseEnd_1972882] using wordTrace_append hprefix tailTrace_1972882
  have hstable : (prefixWord ++ tailWord_1972882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972882).length < 2 ^ (prefixWord ++ tailWord_1972882).sum := by decide
  have hdescent : baseEnd_1972882 < baseStart_1972882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972942 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_1972942 : Nat := 118140960795 + 1972942 * 2 ^ 59
def prefixEnd_1972942 : Nat := 4983230072969 + 3 ^ 40 * 1972942 * 2
def baseEnd_1972942 : Nat := 337689183147641696350537

theorem tailTrace_1972942 : CollatzResearch.WordTrace tailWord_1972942 prefixEnd_1972942 337689183147641696350537 := by
  unfold tailWord_1972942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994888302296945064077135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47972737612250373675078053 8994888302296945064077135)
  ·
    refine ⟨13492332453445417596115703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8994888302296945064077135 13492332453445417596115703)
    ·
      refine ⟨20238498680168126394173555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13492332453445417596115703 20238498680168126394173555)
      ·
        refine ⟨30357748020252189591260333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20238498680168126394173555 30357748020252189591260333)
        ·
          refine ⟨11384155507594571096722625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30357748020252189591260333 11384155507594571096722625)
          ·
            refine ⟨8538116630695928322541969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11384155507594571096722625 8538116630695928322541969)
            ·
              refine ⟨6403587473021946241906477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8538116630695928322541969 6403587473021946241906477)
              ·
                refine ⟨2401345302383229840714929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6403587473021946241906477 2401345302383229840714929)
                ·
                  refine ⟨1801008976787422380536197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2401345302383229840714929 1801008976787422380536197)
                  ·
                    refine ⟨337689183147641696350537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1801008976787422380536197 337689183147641696350537)
                    ·
                      rfl

theorem cell23_1972942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_1972942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972942 prefixEnd_1972942 := by exact prefixLift 1972942
  have htrace : WordTrace (prefixWord ++ tailWord_1972942) baseStart_1972942 baseEnd_1972942 := by
    simpa [prefixWord, tailWord_1972942, baseEnd_1972942] using wordTrace_append hprefix tailTrace_1972942
  have hstable : (prefixWord ++ tailWord_1972942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972942).length < 2 ^ (prefixWord ++ tailWord_1972942).sum := by decide
  have hdescent : baseEnd_1972942 < baseStart_1972942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972945 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_1972945 : Nat := 118140960795 + 1972945 * 2 ^ 59
def prefixEnd_1972945 : Nat := 4983230072969 + 3 ^ 40 * 1972945 * 2
def baseEnd_1972945 : Nat := 1013069089884888577314097

theorem tailTrace_1972945 : CollatzResearch.WordTrace tailWord_1972945 prefixEnd_1972945 1013069089884888577314097 := by
  unfold tailWord_1972945
  simp only [CollatzResearch.WordTrace]
  refine ⟨71959215837364692024976289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47972810558243128016650859 71959215837364692024976289)
  ·
    refine ⟨53969411878023519018732217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71959215837364692024976289 53969411878023519018732217)
    ·
      refine ⟨40477058908517639264049163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53969411878023519018732217 40477058908517639264049163)
      ·
        refine ⟨60715588362776458896073745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40477058908517639264049163 60715588362776458896073745)
        ·
          refine ⟨45536691272082344172055309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60715588362776458896073745 45536691272082344172055309)
          ·
            refine ⟨17076259227030879064520741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45536691272082344172055309 17076259227030879064520741)
            ·
              refine ⟨3201798605068289824597639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17076259227030879064520741 3201798605068289824597639)
              ·
                refine ⟨4802697907602434736896459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201798605068289824597639 4802697907602434736896459)
                ·
                  refine ⟨7204046861403652105344689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802697907602434736896459 7204046861403652105344689)
                  ·
                    refine ⟨5403035146052739079008517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7204046861403652105344689 5403035146052739079008517)
                    ·
                      refine ⟨1013069089884888577314097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5403035146052739079008517 1013069089884888577314097)
                      ·
                        rfl

theorem cell23_1972945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_1972945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972945 prefixEnd_1972945 := by exact prefixLift 1972945
  have htrace : WordTrace (prefixWord ++ tailWord_1972945) baseStart_1972945 baseEnd_1972945 := by
    simpa [prefixWord, tailWord_1972945, baseEnd_1972945] using wordTrace_append hprefix tailTrace_1972945
  have hstable : (prefixWord ++ tailWord_1972945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972945).length < 2 ^ (prefixWord ++ tailWord_1972945).sum := by decide
  have hdescent : baseEnd_1972945 < baseStart_1972945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972999 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1972999 : Nat := 118140960795 + 1972999 * 2 ^ 59
def prefixEnd_1972999 : Nat := 4983230072969 + 3 ^ 40 * 1972999 * 2
def baseEnd_1972999 : Nat := 1013096817840231366038849

theorem tailTrace_1972999 : CollatzResearch.WordTrace tailWord_1972999 prefixEnd_1972999 1013096817840231366038849 := by
  unfold tailWord_1972999
  simp only [CollatzResearch.WordTrace]
  refine ⟨71961185379169059247442051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47974123586112706164961367 71961185379169059247442051)
  ·
    refine ⟨107941778068753588871163077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71961185379169059247442051 107941778068753588871163077)
    ·
      refine ⟨20239083387891297913343077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107941778068753588871163077 20239083387891297913343077)
      ·
        refine ⟨3794828135229618358751827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20239083387891297913343077 3794828135229618358751827)
        ·
          refine ⟨5692242202844427538127741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794828135229618358751827 5692242202844427538127741)
          ·
            refine ⟨2134590826066660326797903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5692242202844427538127741 2134590826066660326797903)
            ·
              refine ⟨3201886239099990490196855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134590826066660326797903 3201886239099990490196855)
              ·
                refine ⟨4802829358649985735295283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201886239099990490196855 4802829358649985735295283)
                ·
                  refine ⟨7204244037974978602942925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4802829358649985735295283 7204244037974978602942925)
                  ·
                    refine ⟨2701591514240616976103597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7204244037974978602942925 2701591514240616976103597)
                    ·
                      refine ⟨1013096817840231366038849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2701591514240616976103597 1013096817840231366038849)
                      ·
                        rfl

theorem cell23_1972999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1972999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1972999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1972999 prefixEnd_1972999 := by exact prefixLift 1972999
  have htrace : WordTrace (prefixWord ++ tailWord_1972999) baseStart_1972999 baseEnd_1972999 := by
    simpa [prefixWord, tailWord_1972999, baseEnd_1972999] using wordTrace_append hprefix tailTrace_1972999
  have hstable : (prefixWord ++ tailWord_1972999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972999).length < 2 ^ (prefixWord ++ tailWord_1972999).sum := by decide
  have hdescent : baseEnd_1972999 < baseStart_1972999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973025 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1973025 : Nat := 118140960795 + 1973025 * 2 ^ 59
def prefixEnd_1973025 : Nat := 4983230072969 + 3 ^ 40 * 1973025 * 2
def baseEnd_1973025 : Nat := 1013110168337248264313729

theorem tailTrace_1973025 : CollatzResearch.WordTrace tailWord_1973025 prefixEnd_1973025 1013110168337248264313729 := by
  unfold tailWord_1973025
  simp only [CollatzResearch.WordTrace]
  refine ⟨71962133677074865687888529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47974755784716577125259019 71962133677074865687888529)
  ·
    refine ⟨53971600257806149265916397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71962133677074865687888529 53971600257806149265916397)
    ·
      refine ⟨20239350096677305974718649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53971600257806149265916397 20239350096677305974718649)
      ·
        refine ⟨15179512572507979481038987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20239350096677305974718649 15179512572507979481038987)
        ·
          refine ⟨22769268858761969221558481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15179512572507979481038987 22769268858761969221558481)
          ·
            refine ⟨17076951644071476916168861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22769268858761969221558481 17076951644071476916168861)
            ·
              refine ⟨6403856866526803843563323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17076951644071476916168861 6403856866526803843563323)
              ·
                refine ⟨9605785299790205765344985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403856866526803843563323 9605785299790205765344985)
                ·
                  refine ⟨7204338974842654324008739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9605785299790205765344985 7204338974842654324008739)
                  ·
                    refine ⟨10806508462263981486013109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7204338974842654324008739 10806508462263981486013109)
                    ·
                      refine ⟨1013110168337248264313729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10806508462263981486013109 1013110168337248264313729)
                      ·
                        rfl

theorem cell23_1973025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1973025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973025 prefixEnd_1973025 := by exact prefixLift 1973025
  have htrace : WordTrace (prefixWord ++ tailWord_1973025) baseStart_1973025 baseEnd_1973025 := by
    simpa [prefixWord, tailWord_1973025, baseEnd_1973025] using wordTrace_append hprefix tailTrace_1973025
  have hstable : (prefixWord ++ tailWord_1973025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973025).length < 2 ^ (prefixWord ++ tailWord_1973025).sum := by decide
  have hdescent : baseEnd_1973025 < baseStart_1973025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973060 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1973060 : Nat := 118140960795 + 1973060 * 2 ^ 59
def prefixEnd_1973060 : Nat := 4983230072969 + 3 ^ 40 * 1973060 * 2
def baseEnd_1973060 : Nat := 1013128140160155627376069

theorem tailTrace_1973060 : CollatzResearch.WordTrace tailWord_1973060 prefixEnd_1973060 1013128140160155627376069 := by
  unfold tailWord_1973060
  simp only [CollatzResearch.WordTrace]
  refine ⟨35981705115974033332706317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47975606821298711110275089 35981705115974033332706317)
  ·
    refine ⟨13493139418490262499764869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35981705115974033332706317 13493139418490262499764869)
    ·
      refine ⟨2529963640966924218705913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13493139418490262499764869 2529963640966924218705913)
      ·
        refine ⟨1897472730725193164029435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529963640966924218705913 1897472730725193164029435)
        ·
          refine ⟨2846209096087789746044153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897472730725193164029435 2846209096087789746044153)
          ·
            refine ⟨2134656822065842309533115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2846209096087789746044153 2134656822065842309533115)
            ·
              refine ⟨3201985233098763464299673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134656822065842309533115 3201985233098763464299673)
              ·
                refine ⟨2401488924824072598224755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201985233098763464299673 2401488924824072598224755)
                ·
                  refine ⟨3602233387236108897337133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401488924824072598224755 3602233387236108897337133)
                  ·
                    refine ⟨1350837520213540836501425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3602233387236108897337133 1350837520213540836501425)
                    ·
                      refine ⟨1013128140160155627376069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350837520213540836501425 1013128140160155627376069)
                      ·
                        rfl

theorem cell23_1973060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1973060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973060 prefixEnd_1973060 := by exact prefixLift 1973060
  have htrace : WordTrace (prefixWord ++ tailWord_1973060) baseStart_1973060 baseEnd_1973060 := by
    simpa [prefixWord, tailWord_1973060, baseEnd_1973060] using wordTrace_append hprefix tailTrace_1973060
  have hstable : (prefixWord ++ tailWord_1973060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973060).length < 2 ^ (prefixWord ++ tailWord_1973060).sum := by decide
  have hdescent : baseEnd_1973060 < baseStart_1973060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973092 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_1973092 : Nat := 118140960795 + 1973092 * 2 ^ 59
def prefixEnd_1973092 : Nat := 4983230072969 + 3 ^ 40 * 1973092 * 2
def baseEnd_1973092 : Nat := 337714857180366500725307

theorem tailTrace_1973092 : CollatzResearch.WordTrace tailWord_1973092 prefixEnd_1973092 337714857180366500725307 := by
  unfold tailWord_1973092
  simp only [CollatzResearch.WordTrace]
  refine ⟨35982288683916068065288765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47976384911888090753718353 35982288683916068065288765)
  ·
    refine ⟨13493358256468525524483287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35982288683916068065288765 13493358256468525524483287)
    ·
      refine ⟨20240037384702788286724931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13493358256468525524483287 20240037384702788286724931)
      ·
        refine ⟨30360056077054182430087397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20240037384702788286724931 30360056077054182430087397)
        ·
          refine ⟨5692510514447659205641387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30360056077054182430087397 5692510514447659205641387)
          ·
            refine ⟨8538765771671488808462081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692510514447659205641387 8538765771671488808462081)
            ·
              refine ⟨6404074328753616606346561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8538765771671488808462081 6404074328753616606346561)
              ·
                refine ⟨4803055746565212454759921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6404074328753616606346561 4803055746565212454759921)
                ·
                  refine ⟨3602291809923909341069941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4803055746565212454759921 3602291809923909341069941)
                  ·
                    refine ⟨337714857180366500725307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3602291809923909341069941 337714857180366500725307)
                    ·
                      rfl

theorem cell23_1973092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_1973092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973092 prefixEnd_1973092 := by exact prefixLift 1973092
  have htrace : WordTrace (prefixWord ++ tailWord_1973092) baseStart_1973092 baseEnd_1973092 := by
    simpa [prefixWord, tailWord_1973092, baseEnd_1973092] using wordTrace_append hprefix tailTrace_1973092
  have hstable : (prefixWord ++ tailWord_1973092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973092).length < 2 ^ (prefixWord ++ tailWord_1973092).sum := by decide
  have hdescent : baseEnd_1973092 < baseStart_1973092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973096 : List Nat := [2, 1, 4, 2, 1, 4, 2, 2, 5]
def baseStart_1973096 : Nat := 118140960795 + 1973096 * 2 ^ 59
def prefixEnd_1973096 : Nat := 4983230072969 + 3 ^ 40 * 1973096 * 2
def baseEnd_1973096 : Nat := 112571847273746387391767

theorem tailTrace_1973096 : CollatzResearch.WordTrace tailWord_1973096 prefixEnd_1973096 112571847273746387391767 := by
  unfold tailWord_1973096
  simp only [CollatzResearch.WordTrace]
  refine ⟨35982361629908822406861571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47976482173211763209148761 35982361629908822406861571)
  ·
    refine ⟨53973542444863233610292357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35982361629908822406861571 53973542444863233610292357)
    ·
      refine ⟨10120039208411856301929817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53973542444863233610292357 10120039208411856301929817)
      ·
        refine ⟨7590029406308892226447363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10120039208411856301929817 7590029406308892226447363)
        ·
          refine ⟨11385044109463338339671045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7590029406308892226447363 11385044109463338339671045)
          ·
            refine ⟨2134695770524375938688321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11385044109463338339671045 2134695770524375938688321)
            ·
              refine ⟨1601021827893281954016241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134695770524375938688321 1601021827893281954016241)
              ·
                refine ⟨1200766370919961465512181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601021827893281954016241 1200766370919961465512181)
                ·
                  refine ⟨112571847273746387391767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1200766370919961465512181 112571847273746387391767)
                  ·
                    rfl

theorem cell23_1973096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 5].length) (baseStart_1973096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973096 prefixEnd_1973096 := by exact prefixLift 1973096
  have htrace : WordTrace (prefixWord ++ tailWord_1973096) baseStart_1973096 baseEnd_1973096 := by
    simpa [prefixWord, tailWord_1973096, baseEnd_1973096] using wordTrace_append hprefix tailTrace_1973096
  have hstable : (prefixWord ++ tailWord_1973096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973096).length < 2 ^ (prefixWord ++ tailWord_1973096).sum := by decide
  have hdescent : baseEnd_1973096 < baseStart_1973096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973129 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 4]
def baseStart_1973129 : Nat := 118140960795 + 1973129 * 2 ^ 59
def prefixEnd_1973129 : Nat := 4983230072969 + 3 ^ 40 * 1973129 * 2
def baseEnd_1973129 : Nat := 1013163570325315857413251

theorem tailTrace_1973129 : CollatzResearch.WordTrace tailWord_1973129 prefixEnd_1973129 1013163570325315857413251 := by
  unfold tailWord_1973129
  simp only [CollatzResearch.WordTrace]
  refine ⟨71965926868698091449674441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47977284579132060966449627 71965926868698091449674441)
  ·
    refine ⟨53974445151523568587255831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71965926868698091449674441 53974445151523568587255831)
    ·
      refine ⟨80961667727285352880883747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53974445151523568587255831 80961667727285352880883747)
      ·
        refine ⟨121442501590928029321325621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80961667727285352880883747 121442501590928029321325621)
        ·
          refine ⟨11385234524149502748874277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121442501590928029321325621 11385234524149502748874277)
          ·
            refine ⟨2134731473278031765413927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11385234524149502748874277 2134731473278031765413927)
            ·
              refine ⟨3202097209917047648120891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134731473278031765413927 3202097209917047648120891)
              ·
                refine ⟨4803145814875571472181337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202097209917047648120891 4803145814875571472181337)
                ·
                  refine ⟨3602359361156678604136003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4803145814875571472181337 3602359361156678604136003)
                  ·
                    refine ⟨5403539041735017906204005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3602359361156678604136003 5403539041735017906204005)
                    ·
                      refine ⟨1013163570325315857413251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5403539041735017906204005 1013163570325315857413251)
                      ·
                        rfl

theorem cell23_1973129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 4].length) (baseStart_1973129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973129 prefixEnd_1973129 := by exact prefixLift 1973129
  have htrace : WordTrace (prefixWord ++ tailWord_1973129) baseStart_1973129 baseEnd_1973129 := by
    simpa [prefixWord, tailWord_1973129, baseEnd_1973129] using wordTrace_append hprefix tailTrace_1973129
  have hstable : (prefixWord ++ tailWord_1973129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973129).length < 2 ^ (prefixWord ++ tailWord_1973129).sum := by decide
  have hdescent : baseEnd_1973129 < baseStart_1973129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973152 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 6]
def baseStart_1973152 : Nat := 118140960795 + 1973152 * 2 ^ 59
def prefixEnd_1973152 : Nat := 4983230072969 + 3 ^ 40 * 1973152 * 2
def baseEnd_1973152 : Nat := 112575042264485474158405

theorem tailTrace_1973152 : CollatzResearch.WordTrace tailWord_1973152 prefixEnd_1973152 112575042264485474158405 := by
  unfold tailWord_1973152
  simp only [CollatzResearch.WordTrace]
  refine ⟨35983382873807383188880855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47977843831743177585174473 35983382873807383188880855)
  ·
    refine ⟨53975074310711074783321283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35983382873807383188880855 53975074310711074783321283)
    ·
      refine ⟨80962611466066612174981925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53975074310711074783321283 80962611466066612174981925)
      ·
        refine ⟨15180489649887489782809111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80962611466066612174981925 15180489649887489782809111)
        ·
          refine ⟨22770734474831234674213667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15180489649887489782809111 22770734474831234674213667)
          ·
            refine ⟨34156101712246852011320501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22770734474831234674213667 34156101712246852011320501)
            ·
              refine ⟨3202134535523142376061297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34156101712246852011320501 3202134535523142376061297)
              ·
                refine ⟨2401600901642356782045973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202134535523142376061297 2401600901642356782045973)
                ·
                  refine ⟨112575042264485474158405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2401600901642356782045973 112575042264485474158405)
                  ·
                    rfl

theorem cell23_1973152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 6].length) (baseStart_1973152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973152 prefixEnd_1973152 := by exact prefixLift 1973152
  have htrace : WordTrace (prefixWord ++ tailWord_1973152) baseStart_1973152 baseEnd_1973152 := by
    simpa [prefixWord, tailWord_1973152, baseEnd_1973152] using wordTrace_append hprefix tailTrace_1973152
  have hstable : (prefixWord ++ tailWord_1973152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973152).length < 2 ^ (prefixWord ++ tailWord_1973152).sum := by decide
  have hdescent : baseEnd_1973152 < baseStart_1973152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973155 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 6]
def baseStart_1973155 : Nat := 118140960795 + 1973155 * 2 ^ 59
def prefixEnd_1973155 : Nat := 4983230072969 + 3 ^ 40 * 1973155 * 2
def baseEnd_1973155 : Nat := 1013176920822332755688131

theorem tailTrace_1973155 : CollatzResearch.WordTrace tailWord_1973155 prefixEnd_1973155 1013176920822332755688131 := by
  unfold tailWord_1973155
  simp only [CollatzResearch.WordTrace]
  refine ⟨71966875166603897890120919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47977916777735931926747279 71966875166603897890120919)
  ·
    refine ⟨107950312749905846835181379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71966875166603897890120919 107950312749905846835181379)
    ·
      refine ⟨161925469124858770252772069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107950312749905846835181379 161925469124858770252772069)
      ·
        refine ⟨30361025460911019422394763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161925469124858770252772069 30361025460911019422394763)
        ·
          refine ⟨45541538191366529133592145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30361025460911019422394763 45541538191366529133592145)
          ·
            refine ⟨34156153643524896850194109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45541538191366529133592145 34156153643524896850194109)
            ·
              refine ⟨12808557616321836318822791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34156153643524896850194109 12808557616321836318822791)
              ·
                refine ⟨19212836424482754478234187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12808557616321836318822791 19212836424482754478234187)
                ·
                  refine ⟨28819254636724131717351281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19212836424482754478234187 28819254636724131717351281)
                  ·
                    refine ⟨21614440977543098788013461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28819254636724131717351281 21614440977543098788013461)
                    ·
                      refine ⟨1013176920822332755688131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21614440977543098788013461 1013176920822332755688131)
                      ·
                        rfl

theorem cell23_1973155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_1973155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973155 prefixEnd_1973155 := by exact prefixLift 1973155
  have htrace : WordTrace (prefixWord ++ tailWord_1973155) baseStart_1973155 baseEnd_1973155 := by
    simpa [prefixWord, tailWord_1973155, baseEnd_1973155] using wordTrace_append hprefix tailTrace_1973155
  have hstable : (prefixWord ++ tailWord_1973155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973155).length < 2 ^ (prefixWord ++ tailWord_1973155).sum := by decide
  have hdescent : baseEnd_1973155 < baseStart_1973155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973175 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_1973175 : Nat := 118140960795 + 1973175 * 2 ^ 59
def prefixEnd_1973175 : Nat := 4983230072969 + 3 ^ 40 * 1973175 * 2
def baseEnd_1973175 : Nat := 1013187190435422677438039

theorem tailTrace_1973175 : CollatzResearch.WordTrace tailWord_1973175 prefixEnd_1973175 1013187190435422677438039 := by
  unfold tailWord_1973175
  simp only [CollatzResearch.WordTrace]
  refine ⟨71967604626531441305848979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47978403084354294203899319 71967604626531441305848979)
  ·
    refine ⟨107951406939797161958773469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71967604626531441305848979 107951406939797161958773469)
    ·
      refine ⟨40481777602423935734540051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107951406939797161958773469 40481777602423935734540051)
      ·
        refine ⟨60722666403635903601810077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40481777602423935734540051 60722666403635903601810077)
        ·
          refine ⟨22770999901363463850678779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60722666403635903601810077 22770999901363463850678779)
          ·
            refine ⟨34156499852045195776018169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22770999901363463850678779 34156499852045195776018169)
            ·
              refine ⟨25617374889033896832013627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34156499852045195776018169 25617374889033896832013627)
              ·
                refine ⟨38426062333550845248020441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25617374889033896832013627 38426062333550845248020441)
                ·
                  refine ⟨28819546750163133936015331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38426062333550845248020441 28819546750163133936015331)
                  ·
                    refine ⟨43229320125244700904022997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28819546750163133936015331 43229320125244700904022997)
                    ·
                      refine ⟨1013187190435422677438039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43229320125244700904022997 1013187190435422677438039)
                      ·
                        rfl

theorem cell23_1973175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_1973175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973175 prefixEnd_1973175 := by exact prefixLift 1973175
  have htrace : WordTrace (prefixWord ++ tailWord_1973175) baseStart_1973175 baseEnd_1973175 := by
    simpa [prefixWord, tailWord_1973175, baseEnd_1973175] using wordTrace_append hprefix tailTrace_1973175
  have hstable : (prefixWord ++ tailWord_1973175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973175).length < 2 ^ (prefixWord ++ tailWord_1973175).sum := by decide
  have hdescent : baseEnd_1973175 < baseStart_1973175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973213 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1973213 : Nat := 118140960795 + 1973213 * 2 ^ 59
def prefixEnd_1973213 : Nat := 4983230072969 + 3 ^ 40 * 1973213 * 2
def baseEnd_1973213 : Nat := 1013206702700293528762865

theorem tailTrace_1973213 : CollatzResearch.WordTrace tailWord_1973213 prefixEnd_1973213 1013206702700293528762865 := by
  unfold tailWord_1973213
  simp only [CollatzResearch.WordTrace]
  refine ⟨71968990600393773795732293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47979327066929182530488195 71968990600393773795732293)
  ·
    refine ⟨13494185737573832586699805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71968990600393773795732293 13494185737573832586699805)
    ·
      refine ⟨5060319651590187220012427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13494185737573832586699805 5060319651590187220012427)
      ·
        refine ⟨7590479477385280830018641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5060319651590187220012427 7590479477385280830018641)
        ·
          refine ⟨5692859608038960622513981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7590479477385280830018641 5692859608038960622513981)
          ·
            refine ⟨2134822353014610233442743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5692859608038960622513981 2134822353014610233442743)
            ·
              refine ⟨3202233529521915350164115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134822353014610233442743 3202233529521915350164115)
              ·
                refine ⟨4803350294282873025246173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202233529521915350164115 4803350294282873025246173)
                ·
                  refine ⟨1801256360356077384467315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4803350294282873025246173 1801256360356077384467315)
                  ·
                    refine ⟨2701884540534116076700973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1801256360356077384467315 2701884540534116076700973)
                    ·
                      refine ⟨1013206702700293528762865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2701884540534116076700973 1013206702700293528762865)
                      ·
                        rfl

theorem cell23_1973213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1973213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973213 prefixEnd_1973213 := by exact prefixLift 1973213
  have htrace : WordTrace (prefixWord ++ tailWord_1973213) baseStart_1973213 baseEnd_1973213 := by
    simpa [prefixWord, tailWord_1973213, baseEnd_1973213] using wordTrace_append hprefix tailTrace_1973213
  have hstable : (prefixWord ++ tailWord_1973213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973213).length < 2 ^ (prefixWord ++ tailWord_1973213).sum := by decide
  have hdescent : baseEnd_1973213 < baseStart_1973213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973232 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_1973232 : Nat := 118140960795 + 1973232 * 2 ^ 59
def prefixEnd_1973232 : Nat := 4983230072969 + 3 ^ 40 * 1973232 * 2
def baseEnd_1973232 : Nat := 1013216458832728954425277

theorem tailTrace_1973232 : CollatzResearch.WordTrace tailWord_1973232 prefixEnd_1973232 1013216458832728954425277 := by
  unfold tailWord_1973232
  simp only [CollatzResearch.WordTrace]
  refine ⟨35984841793662470020336975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47979789058216626693782633 35984841793662470020336975)
  ·
    refine ⟨53977262690493705030505463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35984841793662470020336975 53977262690493705030505463)
    ·
      refine ⟨80965894035740557545758195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53977262690493705030505463 80965894035740557545758195)
      ·
        refine ⟨121448841053610836318637293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80965894035740557545758195 121448841053610836318637293)
        ·
          refine ⟨45543315395104063619488985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121448841053610836318637293 45543315395104063619488985)
          ·
            refine ⟨34157486546328047714616739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45543315395104063619488985 34157486546328047714616739)
            ·
              refine ⟨51236229819492071571925109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34157486546328047714616739 51236229819492071571925109)
              ·
                refine ⟨4803396545577381709867979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51236229819492071571925109 4803396545577381709867979)
                ·
                  refine ⟨7205094818366072564801969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803396545577381709867979 7205094818366072564801969)
                  ·
                    refine ⟨5403821113774554423601477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7205094818366072564801969 5403821113774554423601477)
                    ·
                      refine ⟨1013216458832728954425277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5403821113774554423601477 1013216458832728954425277)
                      ·
                        rfl

theorem cell23_1973232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_1973232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973232 prefixEnd_1973232 := by exact prefixLift 1973232
  have htrace : WordTrace (prefixWord ++ tailWord_1973232) baseStart_1973232 baseEnd_1973232 := by
    simpa [prefixWord, tailWord_1973232, baseEnd_1973232] using wordTrace_append hprefix tailTrace_1973232
  have hstable : (prefixWord ++ tailWord_1973232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973232).length < 2 ^ (prefixWord ++ tailWord_1973232).sum := by decide
  have hdescent : baseEnd_1973232 < baseStart_1973232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973246 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1973246 : Nat := 118140960795 + 1973246 * 2 ^ 59
def prefixEnd_1973246 : Nat := 4983230072969 + 3 ^ 40 * 1973246 * 2
def baseEnd_1973246 : Nat := 337741215853963966550071

theorem tailTrace_1973246 : CollatzResearch.WordTrace tailWord_1973246 prefixEnd_1973246 337741215853963966550071 := by
  unfold tailWord_1973246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8996274276159277553960449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47980129472849480287789061 8996274276159277553960449)
  ·
    refine ⟨6747205707119458165470337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8996274276159277553960449 6747205707119458165470337)
    ·
      refine ⟨5060404280339593624102753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6747205707119458165470337 5060404280339593624102753)
      ·
        refine ⟨3795303210254695218077065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5060404280339593624102753 3795303210254695218077065)
        ·
          refine ⟨2846477407691021413557799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3795303210254695218077065 2846477407691021413557799)
          ·
            refine ⟨4269716111536532120336699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846477407691021413557799 4269716111536532120336699)
            ·
              refine ⟨6404574167304798180505049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269716111536532120336699 6404574167304798180505049)
              ·
                refine ⟨4803430625478598635378787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6404574167304798180505049 4803430625478598635378787)
                ·
                  refine ⟨7205145938217897953068181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803430625478598635378787 7205145938217897953068181)
                  ·
                    refine ⟨337741215853963966550071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7205145938217897953068181 337741215853963966550071)
                    ·
                      rfl

theorem cell23_1973246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1973246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973246 prefixEnd_1973246 := by exact prefixLift 1973246
  have htrace : WordTrace (prefixWord ++ tailWord_1973246) baseStart_1973246 baseEnd_1973246 := by
    simpa [prefixWord, tailWord_1973246, baseEnd_1973246] using wordTrace_append hprefix tailTrace_1973246
  have hstable : (prefixWord ++ tailWord_1973246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973246).length < 2 ^ (prefixWord ++ tailWord_1973246).sum := by decide
  have hdescent : baseEnd_1973246 < baseStart_1973246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973249 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_1973249 : Nat := 118140960795 + 1973249 * 2 ^ 59
def prefixEnd_1973249 : Nat := 4983230072969 + 3 ^ 40 * 1973249 * 2
def baseEnd_1973249 : Nat := 1013225188003855387912699

theorem tailTrace_1973249 : CollatzResearch.WordTrace tailWord_1973249 prefixEnd_1973249 1013225188003855387912699 := by
  unfold tailWord_1973249
  simp only [CollatzResearch.WordTrace]
  refine ⟨71970303628263351944042801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47980202418842234629361867 71970303628263351944042801)
  ·
    refine ⟨53977727721197513958032101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71970303628263351944042801 53977727721197513958032101)
    ·
      refine ⟨10120823947724533867131019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53977727721197513958032101 10120823947724533867131019)
      ·
        refine ⟨15181235921586800800696529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10120823947724533867131019 15181235921586800800696529)
        ·
          refine ⟨11385926941190100600522397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15181235921586800800696529 11385926941190100600522397)
          ·
            refine ⟨4269722602946287725195899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11385926941190100600522397 4269722602946287725195899)
            ·
              refine ⟨6404583904419431587793849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269722602946287725195899 6404583904419431587793849)
              ·
                refine ⟨4803437928314573690845387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6404583904419431587793849 4803437928314573690845387)
                ·
                  refine ⟨7205156892471860536268081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803437928314573690845387 7205156892471860536268081)
                  ·
                    refine ⟨5403867669353895402201061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7205156892471860536268081 5403867669353895402201061)
                    ·
                      refine ⟨1013225188003855387912699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5403867669353895402201061 1013225188003855387912699)
                      ·
                        rfl

theorem cell23_1973249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_1973249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973249 prefixEnd_1973249 := by exact prefixLift 1973249
  have htrace : WordTrace (prefixWord ++ tailWord_1973249) baseStart_1973249 baseEnd_1973249 := by
    simpa [prefixWord, tailWord_1973249, baseEnd_1973249] using wordTrace_append hprefix tailTrace_1973249
  have hstable : (prefixWord ++ tailWord_1973249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973249).length < 2 ^ (prefixWord ++ tailWord_1973249).sum := by decide
  have hdescent : baseEnd_1973249 < baseStart_1973249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973250 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1973250 : Nat := 118140960795 + 1973250 * 2 ^ 59
def prefixEnd_1973250 : Nat := 4983230072969 + 3 ^ 40 * 1973250 * 2
def baseEnd_1973250 : Nat := 337741900494836628000065

theorem tailTrace_1973250 : CollatzResearch.WordTrace tailWord_1973250 prefixEnd_1973250 337741900494836628000065 := by
  unfold tailWord_1973250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17992585025314932278707301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47980226734173152743219469 17992585025314932278707301)
  ·
    refine ⟨3373609692246549802257619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17992585025314932278707301 3373609692246549802257619)
    ·
      refine ⟨5060414538369824703386429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3373609692246549802257619 5060414538369824703386429)
      ·
        refine ⟨1897655451888684263769911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5060414538369824703386429 1897655451888684263769911)
        ·
          refine ⟨2846483177833026395654867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897655451888684263769911 2846483177833026395654867)
          ·
            refine ⟨4269724766749539593482301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846483177833026395654867 4269724766749539593482301)
            ·
              refine ⟨1601146787531077347555863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4269724766749539593482301 1601146787531077347555863)
              ·
                refine ⟨2401720181296616021333795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601146787531077347555863 2401720181296616021333795)
                ·
                  refine ⟨3602580271944924032000693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401720181296616021333795 3602580271944924032000693)
                  ·
                    refine ⟨337741900494836628000065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3602580271944924032000693 337741900494836628000065)
                    ·
                      rfl

theorem cell23_1973250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1973250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973250 prefixEnd_1973250 := by exact prefixLift 1973250
  have htrace : WordTrace (prefixWord ++ tailWord_1973250) baseStart_1973250 baseEnd_1973250 := by
    simpa [prefixWord, tailWord_1973250, baseEnd_1973250] using wordTrace_append hprefix tailTrace_1973250
  have hstable : (prefixWord ++ tailWord_1973250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973250).length < 2 ^ (prefixWord ++ tailWord_1973250).sum := by decide
  have hdescent : baseEnd_1973250 < baseStart_1973250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973253 : List Nat := [1, 3, 1, 1, 2, 3, 2, 5, 1, 2, 2]
def baseStart_1973253 : Nat := 118140960795 + 1973253 * 2 ^ 59
def prefixEnd_1973253 : Nat := 4983230072969 + 3 ^ 40 * 1973253 * 2
def baseEnd_1973253 : Nat := 1013227241926473372262681

theorem tailTrace_1973253 : CollatzResearch.WordTrace tailWord_1973253 prefixEnd_1973253 1013227241926473372262681 := by
  unfold tailWord_1973253
  simp only [CollatzResearch.WordTrace]
  refine ⟨71970449520248860627188413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47980299680165907084792275 71970449520248860627188413)
  ·
    refine ⟨26988918570093322735195655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71970449520248860627188413 26988918570093322735195655)
    ·
      refine ⟨40483377855139984102793483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26988918570093322735195655 40483377855139984102793483)
      ·
        refine ⟨60725066782709976154190225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40483377855139984102793483 60725066782709976154190225)
        ·
          refine ⟨45543800087032482115642669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60725066782709976154190225 45543800087032482115642669)
          ·
            refine ⟨17078925032637180793366001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45543800087032482115642669 17078925032637180793366001)
            ·
              refine ⟨12809193774477885595024501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17078925032637180793366001 12809193774477885595024501)
              ·
                refine ⟨1200861916357301774533547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12809193774477885595024501 1200861916357301774533547)
                ·
                  refine ⟨1801292874535952661800321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200861916357301774533547 1801292874535952661800321)
                  ·
                    refine ⟨1350969655901964496350241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1801292874535952661800321 1350969655901964496350241)
                    ·
                      refine ⟨1013227241926473372262681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350969655901964496350241 1013227241926473372262681)
                      ·
                        rfl

theorem cell23_1973253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 2, 2].length) (baseStart_1973253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973253 prefixEnd_1973253 := by exact prefixLift 1973253
  have htrace : WordTrace (prefixWord ++ tailWord_1973253) baseStart_1973253 baseEnd_1973253 := by
    simpa [prefixWord, tailWord_1973253, baseEnd_1973253] using wordTrace_append hprefix tailTrace_1973253
  have hstable : (prefixWord ++ tailWord_1973253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973253).length < 2 ^ (prefixWord ++ tailWord_1973253).sum := by decide
  have hdescent : baseEnd_1973253 < baseStart_1973253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973272 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 2, 7]
def baseStart_1973272 : Nat := 118140960795 + 1973272 * 2 ^ 59
def prefixEnd_1973272 : Nat := 4983230072969 + 3 ^ 40 * 1973272 * 2
def baseEnd_1973272 : Nat := 337745666019636265975031

theorem tailTrace_1973272 : CollatzResearch.WordTrace tailWord_1973272 prefixEnd_1973272 337745666019636265975031 := by
  unfold tailWord_1973272
  simp only [CollatzResearch.WordTrace]
  refine ⟨35985571253590013436065035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47980761671453351248086713 35985571253590013436065035)
  ·
    refine ⟨53978356880385020154097553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35985571253590013436065035 53978356880385020154097553)
    ·
      refine ⟨40483767660288765115573165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53978356880385020154097553 40483767660288765115573165)
      ·
        refine ⟨15181412872608286918339937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40483767660288765115573165 15181412872608286918339937)
        ·
          refine ⟨11386059654456215188754953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15181412872608286918339937 11386059654456215188754953)
          ·
            refine ⟨8539544740842161391566215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11386059654456215188754953 8539544740842161391566215)
            ·
              refine ⟨12809317111263242087349323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8539544740842161391566215 12809317111263242087349323)
              ·
                refine ⟨19213975666894863131023985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12809317111263242087349323 19213975666894863131023985)
                ·
                  refine ⟨14410481750171147348267989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19213975666894863131023985 14410481750171147348267989)
                  ·
                    refine ⟨337745666019636265975031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14410481750171147348267989 337745666019636265975031)
                    ·
                      rfl

theorem cell23_1973272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_1973272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973272 prefixEnd_1973272 := by exact prefixLift 1973272
  have htrace : WordTrace (prefixWord ++ tailWord_1973272) baseStart_1973272 baseEnd_1973272 := by
    simpa [prefixWord, tailWord_1973272, baseEnd_1973272] using wordTrace_append hprefix tailTrace_1973272
  have hstable : (prefixWord ++ tailWord_1973272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973272).length < 2 ^ (prefixWord ++ tailWord_1973272).sum := by decide
  have hdescent : baseEnd_1973272 < baseStart_1973272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973276 : List Nat := [2, 2, 3, 1, 5, 1, 1, 8]
def baseStart_1973276 : Nat := 118140960795 + 1973276 * 2 ^ 59
def prefixEnd_1973276 : Nat := 4983230072969 + 3 ^ 40 * 1973276 * 2
def baseEnd_1973276 : Nat := 37527372295612103047225

theorem tailTrace_1973276 : CollatzResearch.WordTrace tailWord_1973276 prefixEnd_1973276 37527372295612103047225 := by
  unfold tailWord_1973276
  simp only [CollatzResearch.WordTrace]
  refine ⟨35985644199582767777637841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47980858932777023703517121 35985644199582767777637841)
  ·
    refine ⟨26989233149687075833228381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35985644199582767777637841 26989233149687075833228381)
    ·
      refine ⟨10120962431132653437460643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26989233149687075833228381 10120962431132653437460643)
      ·
        refine ⟨15181443646698980156190965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10120962431132653437460643 15181443646698980156190965)
        ·
          refine ⟨1423260341878029389642903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15181443646698980156190965 1423260341878029389642903)
          ·
            refine ⟨2134890512817044084464355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423260341878029389642903 2134890512817044084464355)
            ·
              refine ⟨3202335769225566126696533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134890512817044084464355 3202335769225566126696533)
              ·
                refine ⟨37527372295612103047225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3202335769225566126696533 37527372295612103047225)
                ·
                  rfl

theorem cell23_1973276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 8].length) (baseStart_1973276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973276 prefixEnd_1973276 := by exact prefixLift 1973276
  have htrace : WordTrace (prefixWord ++ tailWord_1973276) baseStart_1973276 baseEnd_1973276 := by
    simpa [prefixWord, tailWord_1973276, baseEnd_1973276] using wordTrace_append hprefix tailTrace_1973276
  have hstable : (prefixWord ++ tailWord_1973276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973276).length < 2 ^ (prefixWord ++ tailWord_1973276).sum := by decide
  have hdescent : baseEnd_1973276 < baseStart_1973276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973292 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_1973292 : Nat := 118140960795 + 1973292 * 2 ^ 59
def prefixEnd_1973292 : Nat := 4983230072969 + 3 ^ 40 * 1973292 * 2
def baseEnd_1973292 : Nat := 1013247267671998719675001

theorem tailTrace_1973292 : CollatzResearch.WordTrace tailWord_1973292 prefixEnd_1973292 1013247267671998719675001 := by
  unfold tailWord_1973292
  simp only [CollatzResearch.WordTrace]
  refine ⟨35985935983553785143929065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47981247978071713525238753 35985935983553785143929065)
  ·
    refine ⟨26989451987665338857946799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35985935983553785143929065 26989451987665338857946799)
    ·
      refine ⟨40484177981498008286920199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26989451987665338857946799 40484177981498008286920199)
      ·
        refine ⟨60726266972247012430380299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40484177981498008286920199 60726266972247012430380299)
        ·
          refine ⟨91089400458370518645570449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60726266972247012430380299 91089400458370518645570449)
          ·
            refine ⟨68317050343777888984177837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91089400458370518645570449 68317050343777888984177837)
            ·
              refine ⟨25618893878916708369066689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68317050343777888984177837 25618893878916708369066689)
              ·
                refine ⟨19214170409187531276800017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25618893878916708369066689 19214170409187531276800017)
                ·
                  refine ⟨14410627806890648457600013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19214170409187531276800017 14410627806890648457600013)
                  ·
                    refine ⟨5403985427583993171600005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14410627806890648457600013 5403985427583993171600005)
                    ·
                      refine ⟨1013247267671998719675001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5403985427583993171600005 1013247267671998719675001)
                      ·
                        rfl

theorem cell23_1973292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_1973292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973292 prefixEnd_1973292 := by exact prefixLift 1973292
  have htrace : WordTrace (prefixWord ++ tailWord_1973292) baseStart_1973292 baseEnd_1973292 := by
    simpa [prefixWord, tailWord_1973292, baseEnd_1973292] using wordTrace_append hprefix tailTrace_1973292
  have hstable : (prefixWord ++ tailWord_1973292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973292).length < 2 ^ (prefixWord ++ tailWord_1973292).sum := by decide
  have hdescent : baseEnd_1973292 < baseStart_1973292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973296 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 1, 3, 2]
def baseStart_1973296 : Nat := 118140960795 + 1973296 * 2 ^ 59
def prefixEnd_1973296 : Nat := 4983230072969 + 3 ^ 40 * 1973296 * 2
def baseEnd_1973296 : Nat := 1013249321594616704024983

theorem tailTrace_1973296 : CollatzResearch.WordTrace tailWord_1973296 prefixEnd_1973296 1013249321594616704024983 := by
  unfold tailWord_1973296
  simp only [CollatzResearch.WordTrace]
  refine ⟨35986008929546539485501871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47981345239395385980669161 35986008929546539485501871)
  ·
    refine ⟨53979013394319809228252807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35986008929546539485501871 53979013394319809228252807)
    ·
      refine ⟨80968520091479713842379211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53979013394319809228252807 80968520091479713842379211)
      ·
        refine ⟨121452780137219570763568817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80968520091479713842379211 121452780137219570763568817)
        ·
          refine ⟨91089585102914678072676613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121452780137219570763568817 91089585102914678072676613)
          ·
            refine ⟨17079297206796502138626865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91089585102914678072676613 17079297206796502138626865)
            ·
              refine ⟨12809472905097376603970149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17079297206796502138626865 12809472905097376603970149)
              ·
                refine ⟨2401776169705758113244403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12809472905097376603970149 2401776169705758113244403)
                ·
                  refine ⟨3602664254558637169866605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401776169705758113244403 3602664254558637169866605)
                  ·
                    refine ⟨1350999095459488938699977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3602664254558637169866605 1350999095459488938699977)
                    ·
                      refine ⟨1013249321594616704024983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1350999095459488938699977 1013249321594616704024983)
                      ·
                        rfl

theorem cell23_1973296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 3, 2].length) (baseStart_1973296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973296 prefixEnd_1973296 := by exact prefixLift 1973296
  have htrace : WordTrace (prefixWord ++ tailWord_1973296) baseStart_1973296 baseEnd_1973296 := by
    simpa [prefixWord, tailWord_1973296, baseEnd_1973296] using wordTrace_append hprefix tailTrace_1973296
  have hstable : (prefixWord ++ tailWord_1973296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973296).length < 2 ^ (prefixWord ++ tailWord_1973296).sum := by decide
  have hdescent : baseEnd_1973296 < baseStart_1973296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973312 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_1973312 : Nat := 118140960795 + 1973312 * 2 ^ 59
def prefixEnd_1973312 : Nat := 4983230072969 + 3 ^ 40 * 1973312 * 2
def baseEnd_1973312 : Nat := 1013257537285088641424909

theorem tailTrace_1973312 : CollatzResearch.WordTrace tailWord_1973312 prefixEnd_1973312 1013257537285088641424909 := by
  unfold tailWord_1973312
  simp only [CollatzResearch.WordTrace]
  refine ⟨35986300713517556851793095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47981734284690075802390793 35986300713517556851793095)
  ·
    refine ⟨53979451070276335277689643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35986300713517556851793095 53979451070276335277689643)
    ·
      refine ⟨80969176605414502916534465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53979451070276335277689643 80969176605414502916534465)
      ·
        refine ⟨60726882454060877187400849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80969176605414502916534465 60726882454060877187400849)
        ·
          refine ⟨45545161840545657890550637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60726882454060877187400849 45545161840545657890550637)
          ·
            refine ⟨17079435690204621708956489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45545161840545657890550637 17079435690204621708956489)
            ·
              refine ⟨12809576767653466281717367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17079435690204621708956489 12809576767653466281717367)
              ·
                refine ⟨19214365151480199422576051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12809576767653466281717367 19214365151480199422576051)
                ·
                  refine ⟨28821547727220299133864077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19214365151480199422576051 28821547727220299133864077)
                  ·
                    refine ⟨10808080397707612175199029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28821547727220299133864077 10808080397707612175199029)
                    ·
                      refine ⟨1013257537285088641424909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10808080397707612175199029 1013257537285088641424909)
                      ·
                        rfl

theorem cell23_1973312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_1973312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973312 prefixEnd_1973312 := by exact prefixLift 1973312
  have htrace : WordTrace (prefixWord ++ tailWord_1973312) baseStart_1973312 baseEnd_1973312 := by
    simpa [prefixWord, tailWord_1973312, baseEnd_1973312] using wordTrace_append hprefix tailTrace_1973312
  have hstable : (prefixWord ++ tailWord_1973312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973312).length < 2 ^ (prefixWord ++ tailWord_1973312).sum := by decide
  have hdescent : baseEnd_1973312 < baseStart_1973312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973379 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 2, 5]
def baseStart_1973379 : Nat := 118140960795 + 1973379 * 2 ^ 59
def prefixEnd_1973379 : Nat := 4983230072969 + 3 ^ 40 * 1973379 * 2
def baseEnd_1973379 : Nat := 337763980162979959762367

theorem tailTrace_1973379 : CollatzResearch.WordTrace tailWord_1973379 prefixEnd_1973379 337763980162979959762367 := by
  unfold tailWord_1973379
  simp only [CollatzResearch.WordTrace]
  refine ⟨71975045117792384146275191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47983363411861589430850127 71975045117792384146275191)
  ·
    refine ⟨107962567676688576219412787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71975045117792384146275191 107962567676688576219412787)
    ·
      refine ⟨161943851515032864329119181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107962567676688576219412787 161943851515032864329119181)
      ·
        refine ⟨60728944318137324123419693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161943851515032864329119181 60728944318137324123419693)
        ·
          refine ⟨22773354119301496546282385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60728944318137324123419693 22773354119301496546282385)
          ·
            refine ⟨17080015589476122409711789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22773354119301496546282385 17080015589476122409711789)
            ·
              refine ⟨6405005846053545903641921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17080015589476122409711789 6405005846053545903641921)
              ·
                refine ⟨4803754384540159427731441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6405005846053545903641921 4803754384540159427731441)
                ·
                  refine ⟨3602815788405119570798581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4803754384540159427731441 3602815788405119570798581)
                  ·
                    refine ⟨337763980162979959762367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3602815788405119570798581 337763980162979959762367)
                    ·
                      rfl

theorem cell23_1973379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 5].length) (baseStart_1973379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973379 prefixEnd_1973379 := by exact prefixLift 1973379
  have htrace : WordTrace (prefixWord ++ tailWord_1973379) baseStart_1973379 baseEnd_1973379 := by
    simpa [prefixWord, tailWord_1973379, baseEnd_1973379] using wordTrace_append hprefix tailTrace_1973379
  have hstable : (prefixWord ++ tailWord_1973379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973379).length < 2 ^ (prefixWord ++ tailWord_1973379).sum := by decide
  have hdescent : baseEnd_1973379 < baseStart_1973379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973386 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_1973386 : Nat := 118140960795 + 1973386 * 2 ^ 59
def prefixEnd_1973386 : Nat := 4983230072969 + 3 ^ 40 * 1973386 * 2
def baseEnd_1973386 : Nat := 1013295534853521351899569

theorem tailTrace_1973386 : CollatzResearch.WordTrace tailWord_1973386 prefixEnd_1973386 1013295534853521351899569 := by
  unfold tailWord_1973386
  simp only [CollatzResearch.WordTrace]
  refine ⟨17993825107191756085445003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47983533619178016227853341 17993825107191756085445003)
  ·
    refine ⟨26990737660787634128167505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17993825107191756085445003 26990737660787634128167505)
    ·
      refine ⟨20243053245590725596125629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26990737660787634128167505 20243053245590725596125629)
      ·
        refine ⟨7591144967096522098547111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20243053245590725596125629 7591144967096522098547111)
        ·
          refine ⟨11386717450644783147820667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591144967096522098547111 11386717450644783147820667)
          ·
            refine ⟨17080076175967174721731001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11386717450644783147820667 17080076175967174721731001)
            ·
              refine ⟨12810057131975381041298251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17080076175967174721731001 12810057131975381041298251)
              ·
                refine ⟨19215085697963071561947377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12810057131975381041298251 19215085697963071561947377)
                ·
                  refine ⟨14411314273472303671460533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19215085697963071561947377 14411314273472303671460533)
                  ·
                    refine ⟨1351060713138028469199425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14411314273472303671460533 1351060713138028469199425)
                    ·
                      refine ⟨1013295534853521351899569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351060713138028469199425 1013295534853521351899569)
                      ·
                        rfl

theorem cell23_1973386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_1973386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973386 prefixEnd_1973386 := by exact prefixLift 1973386
  have htrace : WordTrace (prefixWord ++ tailWord_1973386) baseStart_1973386 baseEnd_1973386 := by
    simpa [prefixWord, tailWord_1973386, baseEnd_1973386] using wordTrace_append hprefix tailTrace_1973386
  have hstable : (prefixWord ++ tailWord_1973386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973386).length < 2 ^ (prefixWord ++ tailWord_1973386).sum := by decide
  have hdescent : baseEnd_1973386 < baseStart_1973386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973392 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 2, 8]
def baseStart_1973392 : Nat := 118140960795 + 1973392 * 2 ^ 59
def prefixEnd_1973392 : Nat := 4983230072969 + 3 ^ 40 * 1973392 * 2
def baseEnd_1973392 : Nat := 337766205245816109474847

theorem tailTrace_1973392 : CollatzResearch.WordTrace tailWord_1973392 prefixEnd_1973392 337766205245816109474847 := by
  unfold tailWord_1973392
  simp only [CollatzResearch.WordTrace]
  refine ⟨35987759633372643683249215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47983679511163524910998953 35987759633372643683249215)
  ·
    refine ⟨53981639450058965524873823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35987759633372643683249215 53981639450058965524873823)
    ·
      refine ⟨80972459175088448287310735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53981639450058965524873823 80972459175088448287310735)
      ·
        refine ⟨121458688762632672430966103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80972459175088448287310735 121458688762632672430966103)
        ·
          refine ⟨182188033143949008646449155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121458688762632672430966103 182188033143949008646449155)
          ·
            refine ⟨273282049715923512969673733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182188033143949008646449155 273282049715923512969673733)
            ·
              refine ⟨51240384321735658681813825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273282049715923512969673733 51240384321735658681813825)
              ·
                refine ⟨38430288241301744011360369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51240384321735658681813825 38430288241301744011360369)
                ·
                  refine ⟨28822716180976308008520277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38430288241301744011360369 28822716180976308008520277)
                  ·
                    refine ⟨337766205245816109474847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28822716180976308008520277 337766205245816109474847)
                    ·
                      rfl

theorem cell23_1973392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_1973392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973392 prefixEnd_1973392 := by exact prefixLift 1973392
  have htrace : WordTrace (prefixWord ++ tailWord_1973392) baseStart_1973392 baseEnd_1973392 := by
    simpa [prefixWord, tailWord_1973392, baseEnd_1973392] using wordTrace_append hprefix tailTrace_1973392
  have hstable : (prefixWord ++ tailWord_1973392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973392).length < 2 ^ (prefixWord ++ tailWord_1973392).sum := by decide
  have hdescent : baseEnd_1973392 < baseStart_1973392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973439 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 6]
def baseStart_1973439 : Nat := 118140960795 + 1973439 * 2 ^ 59
def prefixEnd_1973439 : Nat := 4983230072969 + 3 ^ 40 * 1973439 * 2
def baseEnd_1973439 : Nat := 112591416592023293837425

theorem tailTrace_1973439 : CollatzResearch.WordTrace tailWord_1973439 prefixEnd_1973439 112591416592023293837425 := by
  unfold tailWord_1973439
  simp only [CollatzResearch.WordTrace]
  refine ⟨71977233497575014393459371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47984822331716676262306247 71977233497575014393459371)
  ·
    refine ⟨107965850246362521590189057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71977233497575014393459371 107965850246362521590189057)
    ·
      refine ⟨80974387684771891192641793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107965850246362521590189057 80974387684771891192641793)
      ·
        refine ⟨60730790763578918394481345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80974387684771891192641793 60730790763578918394481345)
        ·
          refine ⟨45548093072684188795861009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60730790763578918394481345 45548093072684188795861009)
          ·
            refine ⟨34161069804513141596895757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45548093072684188795861009 34161069804513141596895757)
            ·
              refine ⟨12810401176692428098835909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34161069804513141596895757 12810401176692428098835909)
              ·
                refine ⟨2401950220629830268531733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12810401176692428098835909 2401950220629830268531733)
                ·
                  refine ⟨112591416592023293837425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2401950220629830268531733 112591416592023293837425)
                  ·
                    rfl

theorem cell23_1973439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 6].length) (baseStart_1973439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973439 prefixEnd_1973439 := by exact prefixLift 1973439
  have htrace : WordTrace (prefixWord ++ tailWord_1973439) baseStart_1973439 baseEnd_1973439 := by
    simpa [prefixWord, tailWord_1973439, baseEnd_1973439] using wordTrace_append hprefix tailTrace_1973439
  have hstable : (prefixWord ++ tailWord_1973439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973439).length < 2 ^ (prefixWord ++ tailWord_1973439).sum := by decide
  have hdescent : baseEnd_1973439 < baseStart_1973439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973460 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_1973460 : Nat := 118140960795 + 1973460 * 2 ^ 59
def prefixEnd_1973460 : Nat := 4983230072969 + 3 ^ 40 * 1973460 * 2
def baseEnd_1973460 : Nat := 337777844140651354124743

theorem tailTrace_1973460 : CollatzResearch.WordTrace tailWord_1973460 prefixEnd_1973460 337777844140651354124743 := by
  unfold tailWord_1973460
  simp only [CollatzResearch.WordTrace]
  refine ⟨35988999715249467489986917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47985332953665956653315889 35988999715249467489986917)
  ·
    refine ⟨6747937446609275154372547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35988999715249467489986917 6747937446609275154372547)
    ·
      refine ⟨10121906169913912731558821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6747937446609275154372547 10121906169913912731558821)
      ·
        refine ⟨1897857406858858637167279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10121906169913912731558821 1897857406858858637167279)
        ·
          refine ⟨2846786110288287955750919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897857406858858637167279 2846786110288287955750919)
          ·
            refine ⟨4270179165432431933626379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846786110288287955750919 4270179165432431933626379)
            ·
              refine ⟨6405268748148647900439569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4270179165432431933626379 6405268748148647900439569)
              ·
                refine ⟨4803951561111485925329677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6405268748148647900439569 4803951561111485925329677)
                ·
                  refine ⟨1801481835416807221998629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4803951561111485925329677 1801481835416807221998629)
                  ·
                    refine ⟨337777844140651354124743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1801481835416807221998629 337777844140651354124743)
                    ·
                      rfl

theorem cell23_1973460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_1973460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973460 prefixEnd_1973460 := by exact prefixLift 1973460
  have htrace : WordTrace (prefixWord ++ tailWord_1973460) baseStart_1973460 baseEnd_1973460 := by
    simpa [prefixWord, tailWord_1973460, baseEnd_1973460] using wordTrace_append hprefix tailTrace_1973460
  have hstable : (prefixWord ++ tailWord_1973460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973460).length < 2 ^ (prefixWord ++ tailWord_1973460).sum := by decide
  have hdescent : baseEnd_1973460 < baseStart_1973460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973490 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 6]
def baseStart_1973490 : Nat := 118140960795 + 1973490 * 2 ^ 59
def prefixEnd_1973490 : Nat := 4983230072969 + 3 ^ 40 * 1973490 * 2
def baseEnd_1973490 : Nat := 112594326315732104999899

theorem tailTrace_1973490 : CollatzResearch.WordTrace tailWord_1973490 prefixEnd_1973490 112594326315732104999899 := by
  unfold tailWord_1973490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17994773405097562525891481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47986062413593500069043949 17994773405097562525891481)
  ·
    refine ⟨13496080053823171894418611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17994773405097562525891481 13496080053823171894418611)
    ·
      refine ⟨20244120080734757841627917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13496080053823171894418611 20244120080734757841627917)
      ·
        refine ⟨7591545030275534190610469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20244120080734757841627917 7591545030275534190610469)
        ·
          refine ⟨1423414693176662660739463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7591545030275534190610469 1423414693176662660739463)
          ·
            refine ⟨2135122039764993991109195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423414693176662660739463 2135122039764993991109195)
            ·
              refine ⟨3202683059647490986663793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135122039764993991109195 3202683059647490986663793)
              ·
                refine ⟨2402012294735618239997845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202683059647490986663793 2402012294735618239997845)
                ·
                  refine ⟨112594326315732104999899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2402012294735618239997845 112594326315732104999899)
                  ·
                    rfl

theorem cell23_1973490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_1973490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973490 prefixEnd_1973490 := by exact prefixLift 1973490
  have htrace : WordTrace (prefixWord ++ tailWord_1973490) baseStart_1973490 baseEnd_1973490 := by
    simpa [prefixWord, tailWord_1973490, baseEnd_1973490] using wordTrace_append hprefix tailTrace_1973490
  have hstable : (prefixWord ++ tailWord_1973490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973490).length < 2 ^ (prefixWord ++ tailWord_1973490).sum := by decide
  have hdescent : baseEnd_1973490 < baseStart_1973490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973500 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_1973500 : Nat := 118140960795 + 1973500 * 2 ^ 59
def prefixEnd_1973500 : Nat := 4983230072969 + 3 ^ 40 * 1973500 * 2
def baseEnd_1973500 : Nat := 1013354071648133905874045

theorem tailTrace_1973500 : CollatzResearch.WordTrace tailWord_1973500 prefixEnd_1973500 1013354071648133905874045 := by
  unfold tailWord_1973500
  simp only [CollatzResearch.WordTrace]
  refine ⟨35989729175177010905714977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47986305566902681207619969 35989729175177010905714977)
  ·
    refine ⟨26992296881382758179286233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35989729175177010905714977 26992296881382758179286233)
    ·
      refine ⟨20244222661037068634464675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26992296881382758179286233 20244222661037068634464675)
      ·
        refine ⟨30366333991555602951697013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20244222661037068634464675 30366333991555602951697013)
        ·
          refine ⟨2846843811708337776721595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30366333991555602951697013 2846843811708337776721595)
          ·
            refine ⟨4270265717562506665082393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846843811708337776721595 4270265717562506665082393)
            ·
              refine ⟨3202699288171879998811795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270265717562506665082393 3202699288171879998811795)
              ·
                refine ⟨4804048932257819998217693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202699288171879998811795 4804048932257819998217693)
                ·
                  refine ⟨1801518349596682499331635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4804048932257819998217693 1801518349596682499331635)
                  ·
                    refine ⟨2702277524395023748997453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1801518349596682499331635 2702277524395023748997453)
                    ·
                      refine ⟨1013354071648133905874045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2702277524395023748997453 1013354071648133905874045)
                      ·
                        rfl

theorem cell23_1973500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_1973500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973500 prefixEnd_1973500 := by exact prefixLift 1973500
  have htrace : WordTrace (prefixWord ++ tailWord_1973500) baseStart_1973500 baseEnd_1973500 := by
    simpa [prefixWord, tailWord_1973500, baseEnd_1973500] using wordTrace_append hprefix tailTrace_1973500
  have hstable : (prefixWord ++ tailWord_1973500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973500).length < 2 ^ (prefixWord ++ tailWord_1973500).sum := by decide
  have hdescent : baseEnd_1973500 < baseStart_1973500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973516 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_1973516 : Nat := 118140960795 + 1973516 * 2 ^ 59
def prefixEnd_1973516 : Nat := 4983230072969 + 3 ^ 40 * 1973516 * 2
def baseEnd_1973516 : Nat := 337787429112868614424657

theorem tailTrace_1973516 : CollatzResearch.WordTrace tailWord_1973516 prefixEnd_1973516 337787429112868614424657 := by
  unfold tailWord_1973516
  simp only [CollatzResearch.WordTrace]
  refine ⟨35990020959148028272006201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47986694612197371029341601 35990020959148028272006201)
  ·
    refine ⟨26992515719361021204004651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35990020959148028272006201 26992515719361021204004651)
    ·
      refine ⟨40488773579041531806006977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26992515719361021204004651 40488773579041531806006977)
      ·
        refine ⟨30366580184281148854505233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40488773579041531806006977 30366580184281148854505233)
        ·
          refine ⟨22774935138210861640878925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30366580184281148854505233 22774935138210861640878925)
          ·
            refine ⟨8540600676829073115329597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22774935138210861640878925 8540600676829073115329597)
            ·
              refine ⟨3202725253810902418248599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8540600676829073115329597 3202725253810902418248599)
              ·
                refine ⟨4804087880716353627372899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202725253810902418248599 4804087880716353627372899)
                ·
                  refine ⟨7206131821074530441059349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4804087880716353627372899 7206131821074530441059349)
                  ·
                    refine ⟨337787429112868614424657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7206131821074530441059349 337787429112868614424657)
                    ·
                      rfl

theorem cell23_1973516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_1973516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973516 prefixEnd_1973516 := by exact prefixLift 1973516
  have htrace : WordTrace (prefixWord ++ tailWord_1973516) baseStart_1973516 baseEnd_1973516 := by
    simpa [prefixWord, tailWord_1973516, baseEnd_1973516] using wordTrace_append hprefix tailTrace_1973516
  have hstable : (prefixWord ++ tailWord_1973516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973516).length < 2 ^ (prefixWord ++ tailWord_1973516).sum := by decide
  have hdescent : baseEnd_1973516 < baseStart_1973516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973533 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1973533 : Nat := 118140960795 + 1973533 * 2 ^ 59
def prefixEnd_1973533 : Nat := 4983230072969 + 3 ^ 40 * 1973533 * 2
def baseEnd_1973533 : Nat := 337790338836577425587131

theorem tailTrace_1973533 : CollatzResearch.WordTrace tailWord_1973533 prefixEnd_1973533 337790338836577425587131 := by
  unfold tailWord_1973533
  simp only [CollatzResearch.WordTrace]
  refine ⟨71980661959234468447381253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47987107972822978964920835 71980661959234468447381253)
  ·
    refine ⟨13496374117356462833883985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71980661959234468447381253 13496374117356462833883985)
    ·
      refine ⟨10122280588017347125412989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13496374117356462833883985 10122280588017347125412989)
      ·
        refine ⟨3795855220506505172029871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10122280588017347125412989 3795855220506505172029871)
        ·
          refine ⟨5693782830759757758044807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795855220506505172029871 5693782830759757758044807)
          ·
            refine ⟨8540674246139636637067211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693782830759757758044807 8540674246139636637067211)
            ·
              refine ⟨12811011369209454955600817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8540674246139636637067211 12811011369209454955600817)
              ·
                refine ⟨9608258526907091216700613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12811011369209454955600817 9608258526907091216700613)
                ·
                  refine ⟨1801548473795079603131365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9608258526907091216700613 1801548473795079603131365)
                  ·
                    refine ⟨337790338836577425587131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1801548473795079603131365 337790338836577425587131)
                    ·
                      rfl

theorem cell23_1973533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1973533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973533 prefixEnd_1973533 := by exact prefixLift 1973533
  have htrace : WordTrace (prefixWord ++ tailWord_1973533) baseStart_1973533 baseEnd_1973533 := by
    simpa [prefixWord, tailWord_1973533, baseEnd_1973533] using wordTrace_append hprefix tailTrace_1973533
  have hstable : (prefixWord ++ tailWord_1973533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973533).length < 2 ^ (prefixWord ++ tailWord_1973533).sum := by decide
  have hdescent : baseEnd_1973533 < baseStart_1973533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973546 : List Nat := [3, 1, 4, 2, 1, 1, 11]
def baseStart_1973546 : Nat := 118140960795 + 1973546 * 2 ^ 59
def prefixEnd_1973546 : Nat := 4983230072969 + 3 ^ 40 * 1973546 * 2
def baseEnd_1973546 : Nat := 12510835700719021307393

theorem tailTrace_1973546 : CollatzResearch.WordTrace tailWord_1973546 prefixEnd_1973546 12510835700719021307393 := by
  unfold tailWord_1973546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17995284027046842916901123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47987424072124914445069661 17995284027046842916901123)
  ·
    refine ⟨26992926040570264375351685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17995284027046842916901123 26992926040570264375351685)
    ·
      refine ⟨5061173632606924570378441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26992926040570264375351685 5061173632606924570378441)
      ·
        refine ⟨3795880224455193427783831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5061173632606924570378441 3795880224455193427783831)
        ·
          refine ⟨5693820336682790141675747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795880224455193427783831 5693820336682790141675747)
          ·
            refine ⟨8540730505024185212513621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693820336682790141675747 8540730505024185212513621)
            ·
              refine ⟨12510835700719021307393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8540730505024185212513621 12510835700719021307393)
              ·
                rfl

theorem cell23_1973546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 11].length) (baseStart_1973546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973546 prefixEnd_1973546 := by exact prefixLift 1973546
  have htrace : WordTrace (prefixWord ++ tailWord_1973546) baseStart_1973546 baseEnd_1973546 := by
    simpa [prefixWord, tailWord_1973546, baseEnd_1973546] using wordTrace_append hprefix tailTrace_1973546
  have hstable : (prefixWord ++ tailWord_1973546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973546).length < 2 ^ (prefixWord ++ tailWord_1973546).sum := by decide
  have hdescent : baseEnd_1973546 < baseStart_1973546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973557 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_1973557 : Nat := 118140960795 + 1973557 * 2 ^ 59
def prefixEnd_1973557 : Nat := 4983230072969 + 3 ^ 40 * 1973557 * 2
def baseEnd_1973557 : Nat := 1013383340045440182861283

theorem tailTrace_1973557 : CollatzResearch.WordTrace tailWord_1973557 prefixEnd_1973557 1013383340045440182861283 := by
  unfold tailWord_1973557
  simp only [CollatzResearch.WordTrace]
  refine ⟨71981537311147520546254925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47987691540765013697503283 71981537311147520546254925)
  ·
    refine ⟨26993076491680320204845597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71981537311147520546254925 26993076491680320204845597)
    ·
      refine ⟨10122403684380120076817099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26993076491680320204845597 10122403684380120076817099)
      ·
        refine ⟨15183605526570180115225649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10122403684380120076817099 15183605526570180115225649)
        ·
          refine ⟨11387704144927635086419237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15183605526570180115225649 11387704144927635086419237)
          ·
            refine ⟨2135194527173931578703607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11387704144927635086419237 2135194527173931578703607)
            ·
              refine ⟨3202791790760897368055411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135194527173931578703607 3202791790760897368055411)
              ·
                refine ⟨4804187686141346052083117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202791790760897368055411 4804187686141346052083117)
                ·
                  refine ⟨1801570382303004769531169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4804187686141346052083117 1801570382303004769531169)
                  ·
                    refine ⟨1351177786727253577148377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1801570382303004769531169 1351177786727253577148377)
                    ·
                      refine ⟨1013383340045440182861283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351177786727253577148377 1013383340045440182861283)
                      ·
                        rfl

theorem cell23_1973557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_1973557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973557 prefixEnd_1973557 := by exact prefixLift 1973557
  have htrace : WordTrace (prefixWord ++ tailWord_1973557) baseStart_1973557 baseEnd_1973557 := by
    simpa [prefixWord, tailWord_1973557, baseEnd_1973557] using wordTrace_append hprefix tailTrace_1973557
  have hstable : (prefixWord ++ tailWord_1973557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973557).length < 2 ^ (prefixWord ++ tailWord_1973557).sum := by decide
  have hdescent : baseEnd_1973557 < baseStart_1973557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973566 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1973566 : Nat := 118140960795 + 1973566 * 2 ^ 59
def prefixEnd_1973566 : Nat := 4983230072969 + 3 ^ 40 * 1973566 * 2
def baseEnd_1973566 : Nat := 1013387961371330647648741

theorem tailTrace_1973566 : CollatzResearch.WordTrace tailWord_1973566 prefixEnd_1973566 1013387961371330647648741 := by
  unfold tailWord_1973566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8997733196014364385416569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47987910378743276722221701 8997733196014364385416569)
  ·
    refine ⟨6748299897010773289062427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8997733196014364385416569 6748299897010773289062427)
    ·
      refine ⟨10122449845516159933593641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748299897010773289062427 10122449845516159933593641)
      ·
        refine ⟨7591837384137119950195231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10122449845516159933593641 7591837384137119950195231)
        ·
          refine ⟨11387756076205679925292847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591837384137119950195231 11387756076205679925292847)
          ·
            refine ⟨17081634114308519887939271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11387756076205679925292847 17081634114308519887939271)
            ·
              refine ⟨25622451171462779831908907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17081634114308519887939271 25622451171462779831908907)
              ·
                refine ⟨38433676757194169747863361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25622451171462779831908907 38433676757194169747863361)
                ·
                  refine ⟨28825257567895627310897521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38433676757194169747863361 28825257567895627310897521)
                  ·
                    refine ⟨21618943175921720483173141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28825257567895627310897521 21618943175921720483173141)
                    ·
                      refine ⟨1013387961371330647648741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21618943175921720483173141 1013387961371330647648741)
                      ·
                        rfl

theorem cell23_1973566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1973566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973566 prefixEnd_1973566 := by exact prefixLift 1973566
  have htrace : WordTrace (prefixWord ++ tailWord_1973566) baseStart_1973566 baseEnd_1973566 := by
    simpa [prefixWord, tailWord_1973566, baseEnd_1973566] using wordTrace_append hprefix tailTrace_1973566
  have hstable : (prefixWord ++ tailWord_1973566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973566).length < 2 ^ (prefixWord ++ tailWord_1973566).sum := by decide
  have hdescent : baseEnd_1973566 < baseStart_1973566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973607 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_1973607 : Nat := 118140960795 + 1973607 * 2 ^ 59
def prefixEnd_1973607 : Nat := 4983230072969 + 3 ^ 40 * 1973607 * 2
def baseEnd_1973607 : Nat := 1013409014078164987236053

theorem tailTrace_1973607 : CollatzResearch.WordTrace tailWord_1973607 prefixEnd_1973607 1013409014078164987236053 := by
  unfold tailWord_1973607
  simp only [CollatzResearch.WordTrace]
  refine ⟨71983360960966379085575075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47988907307310919390383383 71983360960966379085575075)
  ·
    refine ⟨107975041441449568628362613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71983360960966379085575075 107975041441449568628362613)
    ·
      refine ⟨10122660135135897058908995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107975041441449568628362613 10122660135135897058908995)
      ·
        refine ⟨15183990202703845588363493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10122660135135897058908995 15183990202703845588363493)
        ·
          refine ⟨2846998163006971047818155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15183990202703845588363493 2846998163006971047818155)
          ·
            refine ⟨4270497244510456571727233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846998163006971047818155 4270497244510456571727233)
            ·
              refine ⟨3202872933382842428795425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270497244510456571727233 3202872933382842428795425)
              ·
                refine ⟨2402154700037131821596569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202872933382842428795425 2402154700037131821596569)
                ·
                  refine ⟨1801616025027848866197427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2402154700037131821596569 1801616025027848866197427)
                  ·
                    refine ⟨2702424037541773299296141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1801616025027848866197427 2702424037541773299296141)
                    ·
                      refine ⟨1013409014078164987236053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2702424037541773299296141 1013409014078164987236053)
                      ·
                        rfl

theorem cell23_1973607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_1973607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973607 prefixEnd_1973607 := by exact prefixLift 1973607
  have htrace : WordTrace (prefixWord ++ tailWord_1973607) baseStart_1973607 baseEnd_1973607 := by
    simpa [prefixWord, tailWord_1973607, baseEnd_1973607] using wordTrace_append hprefix tailTrace_1973607
  have hstable : (prefixWord ++ tailWord_1973607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973607).length < 2 ^ (prefixWord ++ tailWord_1973607).sum := by decide
  have hdescent : baseEnd_1973607 < baseStart_1973607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973608 : List Nat := [2, 1, 4, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_1973608 : Nat := 118140960795 + 1973608 * 2 ^ 59
def prefixEnd_1973608 : Nat := 4983230072969 + 3 ^ 40 * 1973608 * 2
def baseEnd_1973608 : Nat := 1013409527558819483323549

theorem tailTrace_1973608 : CollatzResearch.WordTrace tailWord_1973608 prefixEnd_1973608 1013409527558819483323549 := by
  unfold tailWord_1973608
  simp only [CollatzResearch.WordTrace]
  refine ⟨35991698716981378128180739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47988931622641837504240985 35991698716981378128180739)
  ·
    refine ⟨53987548075472067192271109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35991698716981378128180739 53987548075472067192271109)
    ·
      refine ⟨10122665264151012598550833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53987548075472067192271109 10122665264151012598550833)
      ·
        refine ⟨7591998948113259448913125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10122665264151012598550833 7591998948113259448913125)
        ·
          refine ⟨1423499802771236146671211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7591998948113259448913125 1423499802771236146671211)
          ·
            refine ⟨2135249704156854220006817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423499802771236146671211 2135249704156854220006817)
            ·
              refine ⟨1601437278117640665005113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135249704156854220006817 1601437278117640665005113)
              ·
                refine ⟨1201077958588230498753835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601437278117640665005113 1201077958588230498753835)
                ·
                  refine ⟨1801616937882345748130753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201077958588230498753835 1801616937882345748130753)
                  ·
                    refine ⟨1351212703411759311098065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1801616937882345748130753 1351212703411759311098065)
                    ·
                      refine ⟨1013409527558819483323549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351212703411759311098065 1013409527558819483323549)
                      ·
                        rfl

theorem cell23_1973608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_1973608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973608 prefixEnd_1973608 := by exact prefixLift 1973608
  have htrace : WordTrace (prefixWord ++ tailWord_1973608) baseStart_1973608 baseEnd_1973608 := by
    simpa [prefixWord, tailWord_1973608, baseEnd_1973608] using wordTrace_append hprefix tailTrace_1973608
  have hstable : (prefixWord ++ tailWord_1973608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973608).length < 2 ^ (prefixWord ++ tailWord_1973608).sum := by decide
  have hdescent : baseEnd_1973608 < baseStart_1973608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973616 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 3]
def baseStart_1973616 : Nat := 118140960795 + 1973616 * 2 ^ 59
def prefixEnd_1973616 : Nat := 4983230072969 + 3 ^ 40 * 1973616 * 2
def baseEnd_1973616 : Nat := 1013413635404055452023511

theorem tailTrace_1973616 : CollatzResearch.WordTrace tailWord_1973616 prefixEnd_1973616 1013413635404055452023511 := by
  unfold tailWord_1973616
  simp only [CollatzResearch.WordTrace]
  refine ⟨35991844608966886811326351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47989126145289182415101801 35991844608966886811326351)
  ·
    refine ⟨53987766913450330216989527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35991844608966886811326351 53987766913450330216989527)
    ·
      refine ⟨80981650370175495325484291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53987766913450330216989527 80981650370175495325484291)
      ·
        refine ⟨121472475555263242988226437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80981650370175495325484291 121472475555263242988226437)
        ·
          refine ⟨22776089166611858060292457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121472475555263242988226437 22776089166611858060292457)
          ·
            refine ⟨17082066874958893545219343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22776089166611858060292457 17082066874958893545219343)
            ·
              refine ⟨25623100312438340317829015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17082066874958893545219343 25623100312438340317829015)
              ·
                refine ⟨38434650468657510476743523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25623100312438340317829015 38434650468657510476743523)
                ·
                  refine ⟨57651975702986265715115285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38434650468657510476743523 57651975702986265715115285)
                  ·
                    refine ⟨2702436361077481205396029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57651975702986265715115285 2702436361077481205396029)
                    ·
                      refine ⟨1013413635404055452023511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2702436361077481205396029 1013413635404055452023511)
                      ·
                        rfl

theorem cell23_1973616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_1973616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973616 prefixEnd_1973616 := by exact prefixLift 1973616
  have htrace : WordTrace (prefixWord ++ tailWord_1973616) baseStart_1973616 baseEnd_1973616 := by
    simpa [prefixWord, tailWord_1973616, baseEnd_1973616] using wordTrace_append hprefix tailTrace_1973616
  have hstable : (prefixWord ++ tailWord_1973616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973616).length < 2 ^ (prefixWord ++ tailWord_1973616).sum := by decide
  have hdescent : baseEnd_1973616 < baseStart_1973616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973626 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_1973626 : Nat := 118140960795 + 1973626 * 2 ^ 59
def prefixEnd_1973626 : Nat := 4983230072969 + 3 ^ 40 * 1973626 * 2
def baseEnd_1973626 : Nat := 1013418770210600412898465

theorem tailTrace_1973626 : CollatzResearch.WordTrace tailWord_1973626 prefixEnd_1973626 1013418770210600412898465 := by
  unfold tailWord_1973626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17996013486974386332629183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47989369298598363553677821 17996013486974386332629183)
  ·
    refine ⟨26994020230461579498943775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17996013486974386332629183 26994020230461579498943775)
    ·
      refine ⟨40491030345692369248415663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26994020230461579498943775 40491030345692369248415663)
      ·
        refine ⟨60736545518538553872623495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40491030345692369248415663 60736545518538553872623495)
        ·
          refine ⟨91104818277807830808935243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60736545518538553872623495 91104818277807830808935243)
          ·
            refine ⟨136657227416711746213402865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91104818277807830808935243 136657227416711746213402865)
            ·
              refine ⟨102492920562533809660052149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136657227416711746213402865 102492920562533809660052149)
              ·
                refine ⟨9608711302737544655629889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102492920562533809660052149 9608711302737544655629889)
                ·
                  refine ⟨7206533477053158491722417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9608711302737544655629889 7206533477053158491722417)
                  ·
                    refine ⟨5404900107789868868791813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7206533477053158491722417 5404900107789868868791813)
                    ·
                      refine ⟨1013418770210600412898465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5404900107789868868791813 1013418770210600412898465)
                      ·
                        rfl

theorem cell23_1973626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_1973626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973626 prefixEnd_1973626 := by exact prefixLift 1973626
  have htrace : WordTrace (prefixWord ++ tailWord_1973626) baseStart_1973626 baseEnd_1973626 := by
    simpa [prefixWord, tailWord_1973626, baseEnd_1973626] using wordTrace_append hprefix tailTrace_1973626
  have hstable : (prefixWord ++ tailWord_1973626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973626).length < 2 ^ (prefixWord ++ tailWord_1973626).sum := by decide
  have hdescent : baseEnd_1973626 < baseStart_1973626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973636 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 9]
def baseStart_1973636 : Nat := 118140960795 + 1973636 * 2 ^ 59
def prefixEnd_1973636 : Nat := 4983230072969 + 3 ^ 40 * 1973636 * 2
def baseEnd_1973636 : Nat := 112602656113016152641491

theorem tailTrace_1973636 : CollatzResearch.WordTrace tailWord_1973636 prefixEnd_1973636 112602656113016152641491 := by
  unfold tailWord_1973636
  simp only [CollatzResearch.WordTrace]
  refine ⟨35992209338930658519190381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47989612451907544692253841 35992209338930658519190381)
  ·
    refine ⟨13497078502098996944696393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35992209338930658519190381 13497078502098996944696393)
    ·
      refine ⟨10122808876574247708522295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13497078502098996944696393 10122808876574247708522295)
      ·
        refine ⟨15184213314861371562783443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10122808876574247708522295 15184213314861371562783443)
        ·
          refine ⟨22776319972292057344175165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15184213314861371562783443 22776319972292057344175165)
          ·
            refine ⟨8541119989609521504065687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22776319972292057344175165 8541119989609521504065687)
            ·
              refine ⟨12811679984414282256098531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541119989609521504065687 12811679984414282256098531)
              ·
                refine ⟨19217519976621423384147797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12811679984414282256098531 19217519976621423384147797)
                ·
                  refine ⟨112602656113016152641491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19217519976621423384147797 112602656113016152641491)
                  ·
                    rfl

theorem cell23_1973636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_1973636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973636 prefixEnd_1973636 := by exact prefixLift 1973636
  have htrace : WordTrace (prefixWord ++ tailWord_1973636) baseStart_1973636 baseEnd_1973636 := by
    simpa [prefixWord, tailWord_1973636, baseEnd_1973636] using wordTrace_append hprefix tailTrace_1973636
  have hstable : (prefixWord ++ tailWord_1973636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973636).length < 2 ^ (prefixWord ++ tailWord_1973636).sum := by decide
  have hdescent : baseEnd_1973636 < baseStart_1973636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973653 : List Nat := [1, 3, 2, 1, 1, 2, 3, 5, 5]
def baseStart_1973653 : Nat := 118140960795 + 1973653 * 2 ^ 59
def prefixEnd_1973653 : Nat := 4983230072969 + 3 ^ 40 * 1973653 * 2
def baseEnd_1973653 : Nat := 112603626020919089695649

theorem tailTrace_1973653 : CollatzResearch.WordTrace tailWord_1973653 prefixEnd_1973653 112603626020919089695649 := by
  unfold tailWord_1973653
  simp only [CollatzResearch.WordTrace]
  refine ⟨71985038718799728941749613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47990025812533152627833075 71985038718799728941749613)
  ·
    refine ⟨26994389519549898353156105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71985038718799728941749613 26994389519549898353156105)
    ·
      refine ⟨20245792139662423764867079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26994389519549898353156105 20245792139662423764867079)
      ·
        refine ⟨30368688209493635647300619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20245792139662423764867079 30368688209493635647300619)
        ·
          refine ⟨45553032314240453470950929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30368688209493635647300619 45553032314240453470950929)
          ·
            refine ⟨34164774235680340103213197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45553032314240453470950929 34164774235680340103213197)
            ·
              refine ⟨12811790338380127538704949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34164774235680340103213197 12811790338380127538704949)
              ·
                refine ⟨1201105344223136956753589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12811790338380127538704949 1201105344223136956753589)
                ·
                  refine ⟨112603626020919089695649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1201105344223136956753589 112603626020919089695649)
                  ·
                    rfl

theorem cell23_1973653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_1973653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973653 prefixEnd_1973653 := by exact prefixLift 1973653
  have htrace : WordTrace (prefixWord ++ tailWord_1973653) baseStart_1973653 baseEnd_1973653 := by
    simpa [prefixWord, tailWord_1973653, baseEnd_1973653] using wordTrace_append hprefix tailTrace_1973653
  have hstable : (prefixWord ++ tailWord_1973653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973653).length < 2 ^ (prefixWord ++ tailWord_1973653).sum := by decide
  have hdescent : baseEnd_1973653 < baseStart_1973653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973663 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1973663 : Nat := 118140960795 + 1973663 * 2 ^ 59
def prefixEnd_1973663 : Nat := 4983230072969 + 3 ^ 40 * 1973663 * 2
def baseEnd_1973663 : Nat := 1013437768994816768135795

theorem tailTrace_1973663 : CollatzResearch.WordTrace tailWord_1973663 prefixEnd_1973663 1013437768994816768135795 := by
  unfold tailWord_1973663
  simp only [CollatzResearch.WordTrace]
  refine ⟨71985403448763500649613643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47990268965842333766409095 71985403448763500649613643)
  ·
    refine ⟨107978105173145250974420465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71985403448763500649613643 107978105173145250974420465)
    ·
      refine ⟨80983578879858938230815349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107978105173145250974420465 80983578879858938230815349)
      ·
        refine ⟨7592210519986775459138939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80983578879858938230815349 7592210519986775459138939)
        ·
          refine ⟨11388315779980163188708409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7592210519986775459138939 11388315779980163188708409)
          ·
            refine ⟨8541236834985122391531307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11388315779980163188708409 8541236834985122391531307)
            ·
              refine ⟨12811855252477683587296961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541236834985122391531307 12811855252477683587296961)
              ·
                refine ⟨9608891439358262690472721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12811855252477683587296961 9608891439358262690472721)
                ·
                  refine ⟨7206668579518697017854541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9608891439358262690472721 7206668579518697017854541)
                  ·
                    refine ⟨2702500717319511381695453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7206668579518697017854541 2702500717319511381695453)
                    ·
                      refine ⟨1013437768994816768135795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2702500717319511381695453 1013437768994816768135795)
                      ·
                        rfl

theorem cell23_1973663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1973663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973663 prefixEnd_1973663 := by exact prefixLift 1973663
  have htrace : WordTrace (prefixWord ++ tailWord_1973663) baseStart_1973663 baseEnd_1973663 := by
    simpa [prefixWord, tailWord_1973663, baseEnd_1973663] using wordTrace_append hprefix tailTrace_1973663
  have hstable : (prefixWord ++ tailWord_1973663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973663).length < 2 ^ (prefixWord ++ tailWord_1973663).sum := by decide
  have hdescent : baseEnd_1973663 < baseStart_1973663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973676 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_1973676 : Nat := 118140960795 + 1973676 * 2 ^ 59
def prefixEnd_1973676 : Nat := 4983230072969 + 3 ^ 40 * 1973676 * 2
def baseEnd_1973676 : Nat := 1013444444243325217273235

theorem tailTrace_1973676 : CollatzResearch.WordTrace tailWord_1973676 prefixEnd_1973676 1013444444243325217273235 := by
  unfold tailWord_1973676
  simp only [CollatzResearch.WordTrace]
  refine ⟨35992938798858201934918441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47990585065144269246557921 35992938798858201934918441)
  ·
    refine ⟨26994704099143651451188831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35992938798858201934918441 26994704099143651451188831)
    ·
      refine ⟨40492056148715477176783247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26994704099143651451188831 40492056148715477176783247)
      ·
        refine ⟨60738084223073215765174871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40492056148715477176783247 60738084223073215765174871)
        ·
          refine ⟨91107126334609823647762307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60738084223073215765174871 91107126334609823647762307)
          ·
            refine ⟨136660689501914735471643461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91107126334609823647762307 136660689501914735471643461)
            ·
              refine ⟨25623879281609012900933149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136660689501914735471643461 25623879281609012900933149)
              ·
                refine ⟨9608954730603379837849931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25623879281609012900933149 9608954730603379837849931)
                ·
                  refine ⟨14413432095905069756774897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9608954730603379837849931 14413432095905069756774897)
                  ·
                    refine ⟨10810074071928802317581173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14413432095905069756774897 10810074071928802317581173)
                    ·
                      refine ⟨1013444444243325217273235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10810074071928802317581173 1013444444243325217273235)
                      ·
                        rfl

theorem cell23_1973676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_1973676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973676 prefixEnd_1973676 := by exact prefixLift 1973676
  have htrace : WordTrace (prefixWord ++ tailWord_1973676) baseStart_1973676 baseEnd_1973676 := by
    simpa [prefixWord, tailWord_1973676, baseEnd_1973676] using wordTrace_append hprefix tailTrace_1973676
  have hstable : (prefixWord ++ tailWord_1973676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973676).length < 2 ^ (prefixWord ++ tailWord_1973676).sum := by decide
  have hdescent : baseEnd_1973676 < baseStart_1973676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973703 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_1973703 : Nat := 118140960795 + 1973703 * 2 ^ 59
def prefixEnd_1973703 : Nat := 4983230072969 + 3 ^ 40 * 1973703 * 2
def baseEnd_1973703 : Nat := 1013458308220996611635611

theorem tailTrace_1973703 : CollatzResearch.WordTrace tailWord_1973703 prefixEnd_1973703 1013458308220996611635611 := by
  unfold tailWord_1973703
  simp only [CollatzResearch.WordTrace]
  refine ⟨71986862368618587481069763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47991241579079058320713175 71986862368618587481069763)
  ·
    refine ⟨107980293552927881221604645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71986862368618587481069763 107980293552927881221604645)
    ·
      refine ⟨20246305041173977729050871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107980293552927881221604645 20246305041173977729050871)
      ·
        refine ⟨30369457561760966593576307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20246305041173977729050871 30369457561760966593576307)
        ·
          refine ⟨45554186342641449890364461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30369457561760966593576307 45554186342641449890364461)
          ·
            refine ⟨17082819878490543708886673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45554186342641449890364461 17082819878490543708886673)
            ·
              refine ⟨12812114908867907781665005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17082819878490543708886673 12812114908867907781665005)
              ·
                refine ⟨4804543090825465418124377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12812114908867907781665005 4804543090825465418124377)
                ·
                  refine ⟨3603407318119099063593283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4804543090825465418124377 3603407318119099063593283)
                  ·
                    refine ⟨5405110977178648595389925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3603407318119099063593283 5405110977178648595389925)
                    ·
                      refine ⟨1013458308220996611635611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5405110977178648595389925 1013458308220996611635611)
                      ·
                        rfl

theorem cell23_1973703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_1973703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973703 prefixEnd_1973703 := by exact prefixLift 1973703
  have htrace : WordTrace (prefixWord ++ tailWord_1973703) baseStart_1973703 baseEnd_1973703 := by
    simpa [prefixWord, tailWord_1973703, baseEnd_1973703] using wordTrace_append hprefix tailTrace_1973703
  have hstable : (prefixWord ++ tailWord_1973703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973703).length < 2 ^ (prefixWord ++ tailWord_1973703).sum := by decide
  have hdescent : baseEnd_1973703 < baseStart_1973703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973803 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 8, 4]
def baseStart_1973803 : Nat := 118140960795 + 1973803 * 2 ^ 59
def prefixEnd_1973803 : Nat := 4983230072969 + 3 ^ 40 * 1973803 * 2
def baseEnd_1973803 : Nat := 337836552095482073461717

theorem tailTrace_1973803 : CollatzResearch.WordTrace tailWord_1973803 prefixEnd_1973803 337836552095482073461717 := by
  unfold tailWord_1973803
  simp only [CollatzResearch.WordTrace]
  refine ⟨71990509668256304559710063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47993673112170869706473375 71990509668256304559710063)
  ·
    refine ⟨107985764502384456839565095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71990509668256304559710063 107985764502384456839565095)
    ·
      refine ⟨161978646753576685259347643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107985764502384456839565095 161978646753576685259347643)
      ·
        refine ⟨242967970130365027889021465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161978646753576685259347643 242967970130365027889021465)
        ·
          refine ⟨182225977597773770916766099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242967970130365027889021465 182225977597773770916766099)
          ·
            refine ⟨273338966396660656375149149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182225977597773770916766099 273338966396660656375149149)
            ·
              refine ⟨102502112398747746140680931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273338966396660656375149149 102502112398747746140680931)
              ·
                refine ⟨153753168598121619211021397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102502112398747746140680931 153753168598121619211021397)
                ·
                  refine ⟨1801794944509237725129157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 153753168598121619211021397 1801794944509237725129157)
                  ·
                    refine ⟨337836552095482073461717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1801794944509237725129157 337836552095482073461717)
                    ·
                      rfl

theorem cell23_1973803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 4].length) (baseStart_1973803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973803 prefixEnd_1973803 := by exact prefixLift 1973803
  have htrace : WordTrace (prefixWord ++ tailWord_1973803) baseStart_1973803 baseEnd_1973803 := by
    simpa [prefixWord, tailWord_1973803, baseEnd_1973803] using wordTrace_append hprefix tailTrace_1973803
  have hstable : (prefixWord ++ tailWord_1973803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973803).length < 2 ^ (prefixWord ++ tailWord_1973803).sum := by decide
  have hdescent : baseEnd_1973803 < baseStart_1973803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973810 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_1973810 : Nat := 118140960795 + 1973810 * 2 ^ 59
def prefixEnd_1973810 : Nat := 4983230072969 + 3 ^ 40 * 1973810 * 2
def baseEnd_1973810 : Nat := 1013513250651027692997619

theorem tailTrace_1973810 : CollatzResearch.WordTrace tailWord_1973810 prefixEnd_1973810 1013513250651027692997619 := by
  unfold tailWord_1973810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997691244807736188803721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47993843319487296503476589 17997691244807736188803721)
  ·
    refine ⟨13498268433605802141602791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17997691244807736188803721 13498268433605802141602791)
    ·
      refine ⟨20247402650408703212404187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13498268433605802141602791 20247402650408703212404187)
      ·
        refine ⟨30371103975613054818606281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20247402650408703212404187 30371103975613054818606281)
        ·
          refine ⟨22778327981709791113954711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30371103975613054818606281 22778327981709791113954711)
          ·
            refine ⟨34167491972564686670932067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22778327981709791113954711 34167491972564686670932067)
            ·
              refine ⟨51251237958847030006398101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34167491972564686670932067 51251237958847030006398101)
              ·
                refine ⟨2402401779320954531549911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51251237958847030006398101 2402401779320954531549911)
                ·
                  refine ⟨3603602668981431797324867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402401779320954531549911 3603602668981431797324867)
                  ·
                    refine ⟨5405404003472147695987301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3603602668981431797324867 5405404003472147695987301)
                    ·
                      refine ⟨1013513250651027692997619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5405404003472147695987301 1013513250651027692997619)
                      ·
                        rfl

theorem cell23_1973810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_1973810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973810 prefixEnd_1973810 := by exact prefixLift 1973810
  have htrace : WordTrace (prefixWord ++ tailWord_1973810) baseStart_1973810 baseEnd_1973810 := by
    simpa [prefixWord, tailWord_1973810, baseEnd_1973810] using wordTrace_append hprefix tailTrace_1973810
  have hstable : (prefixWord ++ tailWord_1973810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973810).length < 2 ^ (prefixWord ++ tailWord_1973810).sum := by decide
  have hdescent : baseEnd_1973810 < baseStart_1973810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973814 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_1973814 : Nat := 118140960795 + 1973814 * 2 ^ 59
def prefixEnd_1973814 : Nat := 4983230072969 + 3 ^ 40 * 1973814 * 2
def baseEnd_1973814 : Nat := 1013515304573645677347601

theorem tailTrace_1973814 : CollatzResearch.WordTrace tailWord_1973814 prefixEnd_1973814 1013515304573645677347601 := by
  unfold tailWord_1973814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4499431929451028339897531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47993940580810968958906997 4499431929451028339897531)
  ·
    refine ⟨6749147894176542509846297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4499431929451028339897531 6749147894176542509846297)
    ·
      refine ⟨5061860920632406882384723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6749147894176542509846297 5061860920632406882384723)
      ·
        refine ⟨7592791380948610323577085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061860920632406882384723 7592791380948610323577085)
        ·
          refine ⟨2847296767855728871341407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7592791380948610323577085 2847296767855728871341407)
          ·
            refine ⟨4270945151783593307012111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847296767855728871341407 4270945151783593307012111)
            ·
              refine ⟨6406417727675389960518167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4270945151783593307012111 6406417727675389960518167)
              ·
                refine ⟨9609626591513084940777251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6406417727675389960518167 9609626591513084940777251)
                ·
                  refine ⟨14414439887269627411165877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9609626591513084940777251 14414439887269627411165877)
                  ·
                    refine ⟨1351353739431527569796801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14414439887269627411165877 1351353739431527569796801)
                    ·
                      refine ⟨1013515304573645677347601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351353739431527569796801 1013515304573645677347601)
                      ·
                        rfl

theorem cell23_1973814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_1973814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973814 prefixEnd_1973814 := by exact prefixLift 1973814
  have htrace : WordTrace (prefixWord ++ tailWord_1973814) baseStart_1973814 baseEnd_1973814 := by
    simpa [prefixWord, tailWord_1973814, baseEnd_1973814] using wordTrace_append hprefix tailTrace_1973814
  have hstable : (prefixWord ++ tailWord_1973814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973814).length < 2 ^ (prefixWord ++ tailWord_1973814).sum := by decide
  have hdescent : baseEnd_1973814 < baseStart_1973814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973821 : List Nat := [1, 4, 1, 3, 3, 1, 2, 3, 1, 1, 3]
def baseStart_1973821 : Nat := 118140960795 + 1973821 * 2 ^ 59
def prefixEnd_1973821 : Nat := 4983230072969 + 3 ^ 40 * 1973821 * 2
def baseEnd_1973821 : Nat := 1013518898938227149960069

theorem tailTrace_1973821 : CollatzResearch.WordTrace tailWord_1973821 prefixEnd_1973821 1013518898938227149960069 := by
  unfold tailWord_1973821
  simp only [CollatzResearch.WordTrace]
  refine ⟨71991166182191093633865317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47994110788127395755910211 71991166182191093633865317)
  ·
    refine ⟨13498343659160830056349747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71991166182191093633865317 13498343659160830056349747)
    ·
      refine ⟨20247515488741245084524621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13498343659160830056349747 20247515488741245084524621)
      ·
        refine ⟨7592818308277966906696733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20247515488741245084524621 7592818308277966906696733)
        ·
          refine ⟨2847306865604237590011275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7592818308277966906696733 2847306865604237590011275)
          ·
            refine ⟨4270960298406356385016913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847306865604237590011275 4270960298406356385016913)
            ·
              refine ⟨3203220223804767288762685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270960298406356385016913 3203220223804767288762685)
              ·
                refine ⟨1201207583926787733286007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3203220223804767288762685 1201207583926787733286007)
                ·
                  refine ⟨1801811375890181599929011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201207583926787733286007 1801811375890181599929011)
                  ·
                    refine ⟨2702717063835272399893517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1801811375890181599929011 2702717063835272399893517)
                    ·
                      refine ⟨1013518898938227149960069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2702717063835272399893517 1013518898938227149960069)
                      ·
                        rfl

theorem cell23_1973821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_1973821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973821 prefixEnd_1973821 := by exact prefixLift 1973821
  have htrace : WordTrace (prefixWord ++ tailWord_1973821) baseStart_1973821 baseEnd_1973821 := by
    simpa [prefixWord, tailWord_1973821, baseEnd_1973821] using wordTrace_append hprefix tailTrace_1973821
  have hstable : (prefixWord ++ tailWord_1973821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973821).length < 2 ^ (prefixWord ++ tailWord_1973821).sum := by decide
  have hdescent : baseEnd_1973821 < baseStart_1973821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973844 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_1973844 : Nat := 118140960795 + 1973844 * 2 ^ 59
def prefixEnd_1973844 : Nat := 4983230072969 + 3 ^ 40 * 1973844 * 2
def baseEnd_1973844 : Nat := 1013530708993280559972463

theorem tailTrace_1973844 : CollatzResearch.WordTrace tailWord_1973844 prefixEnd_1973844 1013530708993280559972463 := by
  unfold tailWord_1973844
  simp only [CollatzResearch.WordTrace]
  refine ⟨35996002530553884280976293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47994670040738512374635057 35996002530553884280976293)
  ·
    refine ⟨6749250474478853302683055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35996002530553884280976293 6749250474478853302683055)
    ·
      refine ⟨10123875711718279954024583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6749250474478853302683055 10123875711718279954024583)
      ·
        refine ⟨15185813567577419931036875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10123875711718279954024583 15185813567577419931036875)
        ·
          refine ⟨22778720351366129896555313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15185813567577419931036875 22778720351366129896555313)
          ·
            refine ⟨17084040263524597422416485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22778720351366129896555313 17084040263524597422416485)
            ·
              refine ⟨3203257549410862016703091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17084040263524597422416485 3203257549410862016703091)
              ·
                refine ⟨4804886324116293025054637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203257549410862016703091 4804886324116293025054637)
                ·
                  refine ⟨1801832371543609884395489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4804886324116293025054637 1801832371543609884395489)
                  ·
                    refine ⟨1351374278657707413296617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1801832371543609884395489 1351374278657707413296617)
                    ·
                      refine ⟨1013530708993280559972463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351374278657707413296617 1013530708993280559972463)
                      ·
                        rfl

theorem cell23_1973844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_1973844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973844 prefixEnd_1973844 := by exact prefixLift 1973844
  have htrace : WordTrace (prefixWord ++ tailWord_1973844) baseStart_1973844 baseEnd_1973844 := by
    simpa [prefixWord, tailWord_1973844, baseEnd_1973844] using wordTrace_append hprefix tailTrace_1973844
  have hstable : (prefixWord ++ tailWord_1973844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973844).length < 2 ^ (prefixWord ++ tailWord_1973844).sum := by decide
  have hdescent : baseEnd_1973844 < baseStart_1973844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973863 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1973863 : Nat := 118140960795 + 1973863 * 2 ^ 59
def prefixEnd_1973863 : Nat := 4983230072969 + 3 ^ 40 * 1973863 * 2
def baseEnd_1973863 : Nat := 337846821708571995211625

theorem tailTrace_1973863 : CollatzResearch.WordTrace tailWord_1973863 prefixEnd_1973863 337846821708571995211625 := by
  unfold tailWord_1973863
  simp only [CollatzResearch.WordTrace]
  refine ⟨71992698048038934806894243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47995132032025956537929495 71992698048038934806894243)
  ·
    refine ⟨107989047072058402210341365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71992698048038934806894243 107989047072058402210341365)
    ·
      refine ⟨10123973163005475207219503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107989047072058402210341365 10123973163005475207219503)
      ·
        refine ⟨15185959744508212810829255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10123973163005475207219503 15185959744508212810829255)
        ·
          refine ⟨22778939616762319216243883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15185959744508212810829255 22778939616762319216243883)
          ·
            refine ⟨34168409425143478824365825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22778939616762319216243883 34168409425143478824365825)
            ·
              refine ⟨25626307068857609118274369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34168409425143478824365825 25626307068857609118274369)
              ·
                refine ⟨19219730301643206838705777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25626307068857609118274369 19219730301643206838705777)
                ·
                  refine ⟨14414797726232405129029333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19219730301643206838705777 14414797726232405129029333)
                  ·
                    refine ⟨337846821708571995211625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14414797726232405129029333 337846821708571995211625)
                    ·
                      rfl

theorem cell23_1973863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1973863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973863 prefixEnd_1973863 := by exact prefixLift 1973863
  have htrace : WordTrace (prefixWord ++ tailWord_1973863) baseStart_1973863 baseEnd_1973863 := by
    simpa [prefixWord, tailWord_1973863, baseEnd_1973863] using wordTrace_append hprefix tailTrace_1973863
  have hstable : (prefixWord ++ tailWord_1973863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973863).length < 2 ^ (prefixWord ++ tailWord_1973863).sum := by decide
  have hdescent : baseEnd_1973863 < baseStart_1973863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973864 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1973864 : Nat := 118140960795 + 1973864 * 2 ^ 59
def prefixEnd_1973864 : Nat := 4983230072969 + 3 ^ 40 * 1973864 * 2
def baseEnd_1973864 : Nat := 1013540978606370481722371

theorem tailTrace_1973864 : CollatzResearch.WordTrace tailWord_1973864 prefixEnd_1973864 1013540978606370481722371 := by
  unfold tailWord_1973864
  simp only [CollatzResearch.WordTrace]
  refine ⟨35996367260517655988840323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47995156347356874651787097 35996367260517655988840323)
  ·
    refine ⟨53994550890776483983260485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35996367260517655988840323 53994550890776483983260485)
    ·
      refine ⟨10123978292020590746861341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53994550890776483983260485 10123978292020590746861341)
      ·
        refine ⟨3796491859507721530073003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10123978292020590746861341 3796491859507721530073003)
        ·
          refine ⟨5694737789261582295109505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796491859507721530073003 5694737789261582295109505)
          ·
            refine ⟨4271053341946186721332129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5694737789261582295109505 4271053341946186721332129)
            ·
              refine ⟨3203290006459640040999097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271053341946186721332129 3203290006459640040999097)
              ·
                refine ⟨2402467504844730030749323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203290006459640040999097 2402467504844730030749323)
                ·
                  refine ⟨3603701257267095046123985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402467504844730030749323 3603701257267095046123985)
                  ·
                    refine ⟨2702775942950321284592989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3603701257267095046123985 2702775942950321284592989)
                    ·
                      refine ⟨1013540978606370481722371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2702775942950321284592989 1013540978606370481722371)
                      ·
                        rfl

theorem cell23_1973864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1973864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973864 prefixEnd_1973864 := by exact prefixLift 1973864
  have htrace : WordTrace (prefixWord ++ tailWord_1973864) baseStart_1973864 baseEnd_1973864 := by
    simpa [prefixWord, tailWord_1973864, baseEnd_1973864] using wordTrace_append hprefix tailTrace_1973864
  have hstable : (prefixWord ++ tailWord_1973864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973864).length < 2 ^ (prefixWord ++ tailWord_1973864).sum := by decide
  have hdescent : baseEnd_1973864 < baseStart_1973864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973878 : List Nat := [5, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_1973878 : Nat := 118140960795 + 1973878 * 2 ^ 59
def prefixEnd_1973878 : Nat := 4983230072969 + 3 ^ 40 * 1973878 * 2
def baseEnd_1973878 : Nat := 1013548167335533426947307

theorem tailTrace_1973878 : CollatzResearch.WordTrace tailWord_1973878 prefixEnd_1973878 1013548167335533426947307 := by
  unfold tailWord_1973878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4499577821436537023043143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47995496761989728245793525 4499577821436537023043143)
  ·
    refine ⟨6749366732154805534564715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4499577821436537023043143 6749366732154805534564715)
    ·
      refine ⟨10124050098232208301847073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6749366732154805534564715 10124050098232208301847073)
      ·
        refine ⟨7593037573674156226385305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10124050098232208301847073 7593037573674156226385305)
        ·
          refine ⟨5694778180255617169788979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7593037573674156226385305 5694778180255617169788979)
          ·
            refine ⟨8542167270383425754683469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694778180255617169788979 8542167270383425754683469)
            ·
              refine ⟨3203312726393784658006301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8542167270383425754683469 3203312726393784658006301)
              ·
                refine ⟨1201242272397669246752363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3203312726393784658006301 1201242272397669246752363)
                ·
                  refine ⟨1801863408596503870128545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201242272397669246752363 1801863408596503870128545)
                  ·
                    refine ⟨1351397556447377902596409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1801863408596503870128545 1351397556447377902596409)
                    ·
                      refine ⟨1013548167335533426947307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351397556447377902596409 1013548167335533426947307)
                      ·
                        rfl

theorem cell23_1973878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_1973878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973878 prefixEnd_1973878 := by exact prefixLift 1973878
  have htrace : WordTrace (prefixWord ++ tailWord_1973878) baseStart_1973878 baseEnd_1973878 := by
    simpa [prefixWord, tailWord_1973878, baseEnd_1973878] using wordTrace_append hprefix tailTrace_1973878
  have hstable : (prefixWord ++ tailWord_1973878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973878).length < 2 ^ (prefixWord ++ tailWord_1973878).sum := by decide
  have hdescent : baseEnd_1973878 < baseStart_1973878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973903 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_1973903 : Nat := 118140960795 + 1973903 * 2 ^ 59
def prefixEnd_1973903 : Nat := 4983230072969 + 3 ^ 40 * 1973903 * 2
def baseEnd_1973903 : Nat := 1013561004351895829134691

theorem tailTrace_1973903 : CollatzResearch.WordTrace tailWord_1973903 prefixEnd_1973903 1013561004351895829134691 := by
  unfold tailWord_1973903
  simp only [CollatzResearch.WordTrace]
  refine ⟨71994156967894021638350363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47996104645262681092233575 71994156967894021638350363)
  ·
    refine ⟨107991235451841032457525545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71994156967894021638350363 107991235451841032457525545)
    ·
      refine ⟨80993426588880774343144159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107991235451841032457525545 80993426588880774343144159)
      ·
        refine ⟨121490139883321161514716239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80993426588880774343144159 121490139883321161514716239)
        ·
          refine ⟨182235209824981742272074359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121490139883321161514716239 182235209824981742272074359)
          ·
            refine ⟨273352814737472613408111539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182235209824981742272074359 273352814737472613408111539)
            ·
              refine ⟨410029222106208920112167309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273352814737472613408111539 410029222106208920112167309)
              ·
                refine ⟨153760958289828345042062741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410029222106208920112167309 153760958289828345042062741)
                ·
                  refine ⟨7207544919835703673846691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153760958289828345042062741 7207544919835703673846691)
                  ·
                    refine ⟨10811317379753555510770037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7207544919835703673846691 10811317379753555510770037)
                    ·
                      refine ⟨1013561004351895829134691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10811317379753555510770037 1013561004351895829134691)
                      ·
                        rfl

theorem cell23_1973903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_1973903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973903 prefixEnd_1973903 := by exact prefixLift 1973903
  have htrace : WordTrace (prefixWord ++ tailWord_1973903) baseStart_1973903 baseEnd_1973903 := by
    simpa [prefixWord, tailWord_1973903, baseEnd_1973903] using wordTrace_append hprefix tailTrace_1973903
  have hstable : (prefixWord ++ tailWord_1973903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973903).length < 2 ^ (prefixWord ++ tailWord_1973903).sum := by decide
  have hdescent : baseEnd_1973903 < baseStart_1973903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973911 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 2, 1, 3]
def baseStart_1973911 : Nat := 118140960795 + 1973911 * 2 ^ 59
def prefixEnd_1973911 : Nat := 4983230072969 + 3 ^ 40 * 1973911 * 2
def baseEnd_1973911 : Nat := 1013565112197131797834655

theorem tailTrace_1973911 : CollatzResearch.WordTrace tailWord_1973911 prefixEnd_1973911 1013565112197131797834655 := by
  unfold tailWord_1973911
  simp only [CollatzResearch.WordTrace]
  refine ⟨71994448751865039004641587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47996299167910026003094391 71994448751865039004641587)
  ·
    refine ⟨107991673127797558506962381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71994448751865039004641587 107991673127797558506962381)
    ·
      refine ⟨40496877422924084440110893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107991673127797558506962381 40496877422924084440110893)
      ·
        refine ⟨15186329033596531665041585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40496877422924084440110893 15186329033596531665041585)
        ·
          refine ⟨11389746775197398748781189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15186329033596531665041585 11389746775197398748781189)
          ·
            refine ⟨2135577520349512265396473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11389746775197398748781189 2135577520349512265396473)
            ·
              refine ⟨1601683140262134199047355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135577520349512265396473 1601683140262134199047355)
              ·
                refine ⟨2402524710393201298571033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601683140262134199047355 2402524710393201298571033)
                ·
                  refine ⟨1801893532794900973928275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2402524710393201298571033 1801893532794900973928275)
                  ·
                    refine ⟨2702840299192351460892413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1801893532794900973928275 2702840299192351460892413)
                    ·
                      refine ⟨1013565112197131797834655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2702840299192351460892413 1013565112197131797834655)
                      ·
                        rfl

theorem cell23_1973911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_1973911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973911 prefixEnd_1973911 := by exact prefixLift 1973911
  have htrace : WordTrace (prefixWord ++ tailWord_1973911) baseStart_1973911 baseEnd_1973911 := by
    simpa [prefixWord, tailWord_1973911, baseEnd_1973911] using wordTrace_append hprefix tailTrace_1973911
  have hstable : (prefixWord ++ tailWord_1973911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973911).length < 2 ^ (prefixWord ++ tailWord_1973911).sum := by decide
  have hdescent : baseEnd_1973911 < baseStart_1973911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973917 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_1973917 : Nat := 118140960795 + 1973917 * 2 ^ 59
def prefixEnd_1973917 : Nat := 4983230072969 + 3 ^ 40 * 1973917 * 2
def baseEnd_1973917 : Nat := 1013568193081058774359627

theorem tailTrace_1973917 : CollatzResearch.WordTrace tailWord_1973917 prefixEnd_1973917 1013568193081058774359627 := by
  unfold tailWord_1973917
  simp only [CollatzResearch.WordTrace]
  refine ⟨71994667589843302029360005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47996445059895534686240003 71994667589843302029360005)
  ·
    refine ⟨13499000173095619130505001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71994667589843302029360005 13499000173095619130505001)
    ·
      refine ⟨10124250129821714347878751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13499000173095619130505001 10124250129821714347878751)
      ·
        refine ⟨15186375194732571521818127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10124250129821714347878751 15186375194732571521818127)
        ·
          refine ⟨22779562792098857282727191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15186375194732571521818127 22779562792098857282727191)
          ·
            refine ⟨34169344188148285924090787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22779562792098857282727191 34169344188148285924090787)
            ·
              refine ⟨51254016282222428886136181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34169344188148285924090787 51254016282222428886136181)
              ·
                refine ⟨4805064026458352708075267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51254016282222428886136181 4805064026458352708075267)
                ·
                  refine ⟨7207596039687529062112901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805064026458352708075267 7207596039687529062112901)
                  ·
                    refine ⟨1351424257441411699146169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7207596039687529062112901 1351424257441411699146169)
                    ·
                      refine ⟨1013568193081058774359627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351424257441411699146169 1013568193081058774359627)
                      ·
                        rfl

theorem cell23_1973917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_1973917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973917 prefixEnd_1973917 := by exact prefixLift 1973917
  have htrace : WordTrace (prefixWord ++ tailWord_1973917) baseStart_1973917 baseEnd_1973917 := by
    simpa [prefixWord, tailWord_1973917, baseEnd_1973917] using wordTrace_append hprefix tailTrace_1973917
  have hstable : (prefixWord ++ tailWord_1973917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973917).length < 2 ^ (prefixWord ++ tailWord_1973917).sum := by decide
  have hdescent : baseEnd_1973917 < baseStart_1973917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973920 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1973920 : Nat := 118140960795 + 1973920 * 2 ^ 59
def prefixEnd_1973920 : Nat := 4983230072969 + 3 ^ 40 * 1973920 * 2
def baseEnd_1973920 : Nat := 1013569733523022262622113

theorem tailTrace_1973920 : CollatzResearch.WordTrace tailWord_1973920 prefixEnd_1973920 1013569733523022262622113 := by
  unfold tailWord_1973920
  simp only [CollatzResearch.WordTrace]
  refine ⟨35997388504416216770859607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47996518005888289027812809 35997388504416216770859607)
  ·
    refine ⟨53996082756624325156289411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35997388504416216770859607 53996082756624325156289411)
    ·
      refine ⟨80994124134936487734434117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53996082756624325156289411 80994124134936487734434117)
      ·
        refine ⟨15186398275300591450206397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80994124134936487734434117 15186398275300591450206397)
        ·
          refine ⟨5694899353237721793827399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15186398275300591450206397 5694899353237721793827399)
          ·
            refine ⟨8542349029856582690741099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694899353237721793827399 8542349029856582690741099)
            ·
              refine ⟨12813523544784874036111649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8542349029856582690741099 12813523544784874036111649)
              ·
                refine ⟨9610142658588655527083737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12813523544784874036111649 9610142658588655527083737)
                ·
                  refine ⟨7207606993941491645312803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9610142658588655527083737 7207606993941491645312803)
                  ·
                    refine ⟨10811410490912237467969205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7207606993941491645312803 10811410490912237467969205)
                    ·
                      refine ⟨1013569733523022262622113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10811410490912237467969205 1013569733523022262622113)
                      ·
                        rfl

theorem cell23_1973920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1973920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973920 prefixEnd_1973920 := by exact prefixLift 1973920
  have htrace : WordTrace (prefixWord ++ tailWord_1973920) baseStart_1973920 baseEnd_1973920 := by
    simpa [prefixWord, tailWord_1973920, baseEnd_1973920] using wordTrace_append hprefix tailTrace_1973920
  have hstable : (prefixWord ++ tailWord_1973920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973920).length < 2 ^ (prefixWord ++ tailWord_1973920).sum := by decide
  have hdescent : baseEnd_1973920 < baseStart_1973920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973921 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_1973921 : Nat := 118140960795 + 1973921 * 2 ^ 59
def prefixEnd_1973921 : Nat := 4983230072969 + 3 ^ 40 * 1973921 * 2
def baseEnd_1973921 : Nat := 1013570247003676758709609

theorem tailTrace_1973921 : CollatzResearch.WordTrace tailWord_1973921 prefixEnd_1973921 1013570247003676758709609 := by
  unfold tailWord_1973921
  simp only [CollatzResearch.WordTrace]
  refine ⟨71994813481828810712505617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47996542321219207141670411 71994813481828810712505617)
  ·
    refine ⟨53996110111371608034379213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71994813481828810712505617 53996110111371608034379213)
    ·
      refine ⟨20248541291764353012892205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53996110111371608034379213 20248541291764353012892205)
      ·
        refine ⟨7593202984411632379834577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20248541291764353012892205 7593202984411632379834577)
        ·
          refine ⟨5694902238308724284875933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7593202984411632379834577 5694902238308724284875933)
          ·
            refine ⟨2135588339365771606828475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5694902238308724284875933 2135588339365771606828475)
            ·
              refine ⟨3203382509048657410242713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135588339365771606828475 3203382509048657410242713)
              ·
                refine ⟨2402536881786493057682035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203382509048657410242713 2402536881786493057682035)
                ·
                  refine ⟨3603805322679739586523053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402536881786493057682035 3603805322679739586523053)
                  ·
                    refine ⟨1351426996004902344946145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3603805322679739586523053 1351426996004902344946145)
                    ·
                      refine ⟨1013570247003676758709609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351426996004902344946145 1013570247003676758709609)
                      ·
                        rfl

theorem cell23_1973921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_1973921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973921 prefixEnd_1973921 := by exact prefixLift 1973921
  have htrace : WordTrace (prefixWord ++ tailWord_1973921) baseStart_1973921 baseEnd_1973921 := by
    simpa [prefixWord, tailWord_1973921, baseEnd_1973921] using wordTrace_append hprefix tailTrace_1973921
  have hstable : (prefixWord ++ tailWord_1973921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973921).length < 2 ^ (prefixWord ++ tailWord_1973921).sum := by decide
  have hdescent : baseEnd_1973921 < baseStart_1973921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
