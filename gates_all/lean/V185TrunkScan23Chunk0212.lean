import V185TrunkScan23Chunk0211

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1254053 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_1254053 : Nat := 118140960795 + 1254053 * 2 ^ 59
def prefixEnd_1254053 : Nat := 4983230072969 + 3 ^ 40 * 1254053 * 2
def baseEnd_1254053 : Nat := 643931955212887245570221

theorem tailTrace_1254053 : CollatzResearch.WordTrace tailWord_1254053 prefixEnd_1254053 643931955212887245570221 := by
  unfold tailWord_1254053
  simp only [CollatzResearch.WordTrace]
  refine ⟨45739070525787631046150813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30492713683858420697433875 45739070525787631046150813)
  ·
    refine ⟨17152151447170361642306555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45739070525787631046150813 17152151447170361642306555)
    ·
      refine ⟨25728227170755542463459833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17152151447170361642306555 25728227170755542463459833)
      ·
        refine ⟨19296170378066656847594875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25728227170755542463459833 19296170378066656847594875)
        ·
          refine ⟨28944255567099985271392313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19296170378066656847594875 28944255567099985271392313)
          ·
            refine ⟨21708191675324988953544235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28944255567099985271392313 21708191675324988953544235)
            ·
              refine ⟨32562287512987483430316353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21708191675324988953544235 32562287512987483430316353)
              ·
                refine ⟨24421715634740612572737265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32562287512987483430316353 24421715634740612572737265)
                ·
                  refine ⟨18316286726055459429552949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24421715634740612572737265 18316286726055459429552949)
                  ·
                    refine ⟨1717151880567699321520589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18316286726055459429552949 1717151880567699321520589)
                    ·
                      refine ⟨643931955212887245570221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1717151880567699321520589 643931955212887245570221)
                      ·
                        rfl

theorem cell23_1254053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_1254053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254053 prefixEnd_1254053 := by exact prefixLift 1254053
  have htrace : WordTrace (prefixWord ++ tailWord_1254053) baseStart_1254053 baseEnd_1254053 := by
    simpa [prefixWord, tailWord_1254053, baseEnd_1254053] using wordTrace_append hprefix tailTrace_1254053
  have hstable : (prefixWord ++ tailWord_1254053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254053).length < 2 ^ (prefixWord ++ tailWord_1254053).sum := by decide
  have hdescent : baseEnd_1254053 < baseStart_1254053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254104 : List Nat := [2, 1, 2, 2, 3, 2, 2, 4, 1, 1, 3]
def baseStart_1254104 : Nat := 118140960795 + 1254104 * 2 ^ 59
def prefixEnd_1254104 : Nat := 4983230072969 + 3 ^ 40 * 1254104 * 2
def baseEnd_1254104 : Nat := 643958142726266546032487

theorem tailTrace_1254104 : CollatzResearch.WordTrace tailWord_1254104 prefixEnd_1254104 643958142726266546032487 := by
  unfold tailWord_1254104
  simp only [CollatzResearch.WordTrace]
  refine ⟨22870465324301433378128683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30493953765735244504171577 22870465324301433378128683)
  ·
    refine ⟨34305697986452150067193025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22870465324301433378128683 34305697986452150067193025)
    ·
      refine ⟨25729273489839112550394769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34305697986452150067193025 25729273489839112550394769)
      ·
        refine ⟨19296955117379334412796077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25729273489839112550394769 19296955117379334412796077)
        ·
          refine ⟨7236358169017250404798529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19296955117379334412796077 7236358169017250404798529)
          ·
            refine ⟨5427268626762937803598897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7236358169017250404798529 5427268626762937803598897)
            ·
              refine ⟨4070451470072203352699173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5427268626762937803598897 4070451470072203352699173)
              ·
                refine ⟨763209650638538128631095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4070451470072203352699173 763209650638538128631095)
                ·
                  refine ⟨1144814475957807192946643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763209650638538128631095 1144814475957807192946643)
                  ·
                    refine ⟨1717221713936710789419965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1144814475957807192946643 1717221713936710789419965)
                    ·
                      refine ⟨643958142726266546032487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1717221713936710789419965 643958142726266546032487)
                      ·
                        rfl

theorem cell23_1254104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_1254104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254104 prefixEnd_1254104 := by exact prefixLift 1254104
  have htrace : WordTrace (prefixWord ++ tailWord_1254104) baseStart_1254104 baseEnd_1254104 := by
    simpa [prefixWord, tailWord_1254104, baseEnd_1254104] using wordTrace_append hprefix tailTrace_1254104
  have hstable : (prefixWord ++ tailWord_1254104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254104).length < 2 ^ (prefixWord ++ tailWord_1254104).sum := by decide
  have hdescent : baseEnd_1254104 < baseStart_1254104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254127 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 4]
def baseStart_1254127 : Nat := 118140960795 + 1254127 * 2 ^ 59
def prefixEnd_1254127 : Nat := 4983230072969 + 3 ^ 40 * 1254127 * 2
def baseEnd_1254127 : Nat := 643969952781319956044881

theorem tailTrace_1254127 : CollatzResearch.WordTrace tailWord_1254127 prefixEnd_1254127 643969952781319956044881 := by
  unfold tailWord_1254127
  simp only [CollatzResearch.WordTrace]
  refine ⟨45741769527519541684344635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30494513018346361122896423 45741769527519541684344635)
  ·
    refine ⟨68612654291279312526516953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45741769527519541684344635 68612654291279312526516953)
    ·
      refine ⟨51459490718459484394887715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68612654291279312526516953 51459490718459484394887715)
      ·
        refine ⟨77189236077689226592331573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51459490718459484394887715 77189236077689226592331573)
        ·
          refine ⟨7236490882283364993031085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77189236077689226592331573 7236490882283364993031085)
          ·
            refine ⟨2713684080856261872386657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7236490882283364993031085 2713684080856261872386657)
            ·
              refine ⟨2035263060642196404289993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2713684080856261872386657 2035263060642196404289993)
              ·
                refine ⟨1526447295481647303217495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035263060642196404289993 1526447295481647303217495)
                ·
                  refine ⟨2289670943222470954826243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526447295481647303217495 2289670943222470954826243)
                  ·
                    refine ⟨3434506414833706432239365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2289670943222470954826243 3434506414833706432239365)
                    ·
                      refine ⟨643969952781319956044881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3434506414833706432239365 643969952781319956044881)
                      ·
                        rfl

theorem cell23_1254127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 4].length) (baseStart_1254127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254127 prefixEnd_1254127 := by exact prefixLift 1254127
  have htrace : WordTrace (prefixWord ++ tailWord_1254127) baseStart_1254127 baseEnd_1254127 := by
    simpa [prefixWord, tailWord_1254127, baseEnd_1254127] using wordTrace_append hprefix tailTrace_1254127
  have hstable : (prefixWord ++ tailWord_1254127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254127).length < 2 ^ (prefixWord ++ tailWord_1254127).sum := by decide
  have hdescent : baseEnd_1254127 < baseStart_1254127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254163 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 2, 7]
def baseStart_1254163 : Nat := 118140960795 + 1254163 * 2 ^ 59
def prefixEnd_1254163 : Nat := 4983230072969 + 3 ^ 40 * 1254163 * 2
def baseEnd_1254163 : Nat := 214662812694960605064905

theorem tailTrace_1254163 : CollatzResearch.WordTrace tailWord_1254163 prefixEnd_1254163 214662812694960605064905 := by
  unfold tailWord_1254163
  simp only [CollatzResearch.WordTrace]
  refine ⟨45743082555389119832655143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30495388370259413221770095 45743082555389119832655143)
  ·
    refine ⟨68614623833083679748982715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45743082555389119832655143 68614623833083679748982715)
    ·
      refine ⟨102921935749625519623474073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68614623833083679748982715 102921935749625519623474073)
      ·
        refine ⟨77191451812219139717605555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102921935749625519623474073 77191451812219139717605555)
        ·
          refine ⟨115787177718328709576408333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77191451812219139717605555 115787177718328709576408333)
          ·
            refine ⟨43420191644373266091153125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115787177718328709576408333 43420191644373266091153125)
            ·
              refine ⟨8141285933319987392091211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43420191644373266091153125 8141285933319987392091211)
              ·
                refine ⟨12211928899979981088136817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8141285933319987392091211 12211928899979981088136817)
                ·
                  refine ⟨9158946674984985816102613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12211928899979981088136817 9158946674984985816102613)
                  ·
                    refine ⟨214662812694960605064905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9158946674984985816102613 214662812694960605064905)
                    ·
                      rfl

theorem cell23_1254163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 7].length) (baseStart_1254163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254163 prefixEnd_1254163 := by exact prefixLift 1254163
  have htrace : WordTrace (prefixWord ++ tailWord_1254163) baseStart_1254163 baseEnd_1254163 := by
    simpa [prefixWord, tailWord_1254163, baseEnd_1254163] using wordTrace_append hprefix tailTrace_1254163
  have hstable : (prefixWord ++ tailWord_1254163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254163).length < 2 ^ (prefixWord ++ tailWord_1254163).sum := by decide
  have hdescent : baseEnd_1254163 < baseStart_1254163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254198 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1254198 : Nat := 118140960795 + 1254198 * 2 ^ 59
def prefixEnd_1254198 : Nat := 4983230072969 + 3 ^ 40 * 1254198 * 2
def baseEnd_1254198 : Nat := 644006409907789178257055

theorem tailTrace_1254198 : CollatzResearch.WordTrace tailWord_1254198 prefixEnd_1254198 644006409907789178257055 := by
  unfold tailWord_1254198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859022444391395050636203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30496239406841547206786165 2859022444391395050636203)
  ·
    refine ⟨4288533666587092575954305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2859022444391395050636203 4288533666587092575954305)
    ·
      refine ⟨3216400249940319431965729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4288533666587092575954305 3216400249940319431965729)
      ·
        refine ⟨2412300187455239573974297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3216400249940319431965729 2412300187455239573974297)
        ·
          refine ⟨1809225140591429680480723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2412300187455239573974297 1809225140591429680480723)
          ·
            refine ⟨2713837710887144520721085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809225140591429680480723 2713837710887144520721085)
            ·
              refine ⟨1017689141582679195270407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2713837710887144520721085 1017689141582679195270407)
              ·
                refine ⟨1526533712374018792905611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017689141582679195270407 1526533712374018792905611)
                ·
                  refine ⟨2289800568561028189358417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526533712374018792905611 2289800568561028189358417)
                  ·
                    refine ⟨1717350426420771142018813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2289800568561028189358417 1717350426420771142018813)
                    ·
                      refine ⟨644006409907789178257055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1717350426420771142018813 644006409907789178257055)
                      ·
                        rfl

theorem cell23_1254198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1254198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254198 prefixEnd_1254198 := by exact prefixLift 1254198
  have htrace : WordTrace (prefixWord ++ tailWord_1254198) baseStart_1254198 baseEnd_1254198 := by
    simpa [prefixWord, tailWord_1254198, baseEnd_1254198] using wordTrace_append hprefix tailTrace_1254198
  have hstable : (prefixWord ++ tailWord_1254198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254198).length < 2 ^ (prefixWord ++ tailWord_1254198).sum := by decide
  have hdescent : baseEnd_1254198 < baseStart_1254198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254223 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 13]
def baseStart_1254223 : Nat := 118140960795 + 1254223 * 2 ^ 59
def prefixEnd_1254223 : Nat := 4983230072969 + 3 ^ 40 * 1254223 * 2
def baseEnd_1254223 : Nat := 71557694102683508938271

theorem tailTrace_1254223 : CollatzResearch.WordTrace tailWord_1254223 prefixEnd_1254223 71557694102683508938271 := by
  unfold tailWord_1254223
  simp only [CollatzResearch.WordTrace]
  refine ⟨45745270935171750079839323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30496847290114500053226215 45745270935171750079839323)
  ·
    refine ⟨68617906402757625119758985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45745270935171750079839323 68617906402757625119758985)
    ·
      refine ⟨51463429802068218839819239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68617906402757625119758985 51463429802068218839819239)
      ·
        refine ⟨77195144703102328259728859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51463429802068218839819239 77195144703102328259728859)
        ·
          refine ⟨115792717054653492389593289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77195144703102328259728859 115792717054653492389593289)
          ·
            refine ⟨86844537790990119292194967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115792717054653492389593289 86844537790990119292194967)
            ·
              refine ⟨130266806686485178938292451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86844537790990119292194967 130266806686485178938292451)
              ·
                refine ⟨195400210029727768407438677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130266806686485178938292451 195400210029727768407438677)
                ·
                  refine ⟨71557694102683508938271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 195400210029727768407438677 71557694102683508938271)
                  ·
                    rfl

theorem cell23_1254223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 13].length) (baseStart_1254223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254223 prefixEnd_1254223 := by exact prefixLift 1254223
  have htrace : WordTrace (prefixWord ++ tailWord_1254223) baseStart_1254223 baseEnd_1254223 := by
    simpa [prefixWord, tailWord_1254223, baseEnd_1254223] using wordTrace_append hprefix tailTrace_1254223
  have hstable : (prefixWord ++ tailWord_1254223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254223).length < 2 ^ (prefixWord ++ tailWord_1254223).sum := by decide
  have hdescent : baseEnd_1254223 < baseStart_1254223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254234 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2]
def baseStart_1254234 : Nat := 118140960795 + 1254234 * 2 ^ 59
def prefixEnd_1254234 : Nat := 4983230072969 + 3 ^ 40 * 1254234 * 2
def baseEnd_1254234 : Nat := 644024895211351037406889

theorem tailTrace_1254234 : CollatzResearch.WordTrace tailWord_1254234 prefixEnd_1254234 644024895211351037406889 := by
  unfold tailWord_1254234
  simp only [CollatzResearch.WordTrace]
  refine ⟨11436418034532974739622439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30497114758754599305659837 11436418034532974739622439)
  ·
    refine ⟨17154627051799462109433659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11436418034532974739622439 17154627051799462109433659)
    ·
      refine ⟨25731940577699193164150489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17154627051799462109433659 25731940577699193164150489)
      ·
        refine ⟨19298955433274394873112867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25731940577699193164150489 19298955433274394873112867)
        ·
          refine ⟨28948433149911592309669301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19298955433274394873112867 28948433149911592309669301)
          ·
            refine ⟨2713915607804211779031497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28948433149911592309669301 2713915607804211779031497)
            ·
              refine ⟨2035436705853158834273623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2713915607804211779031497 2035436705853158834273623)
              ·
                refine ⟨3053155058779738251410435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035436705853158834273623 3053155058779738251410435)
                ·
                  refine ⟨4579732588169607377115653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053155058779738251410435 4579732588169607377115653)
                  ·
                    refine ⟨858699860281801383209185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4579732588169607377115653 858699860281801383209185)
                    ·
                      refine ⟨644024895211351037406889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858699860281801383209185 644024895211351037406889)
                      ·
                        rfl

theorem cell23_1254234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_1254234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254234 prefixEnd_1254234 := by exact prefixLift 1254234
  have htrace : WordTrace (prefixWord ++ tailWord_1254234) baseStart_1254234 baseEnd_1254234 := by
    simpa [prefixWord, tailWord_1254234, baseEnd_1254234] using wordTrace_append hprefix tailTrace_1254234
  have hstable : (prefixWord ++ tailWord_1254234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254234).length < 2 ^ (prefixWord ++ tailWord_1254234).sum := by decide
  have hdescent : baseEnd_1254234 < baseStart_1254234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254240 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 7]
def baseStart_1254240 : Nat := 118140960795 + 1254240 * 2 ^ 59
def prefixEnd_1254240 : Nat := 4983230072969 + 3 ^ 40 * 1254240 * 2
def baseEnd_1254240 : Nat := 71558664010586445992429

theorem tailTrace_1254240 : CollatzResearch.WordTrace tailWord_1254240 prefixEnd_1254240 71558664010586445992429 := by
  unfold tailWord_1254240
  simp only [CollatzResearch.WordTrace]
  refine ⟨22872945488055080991604087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30497260650740107988805449 22872945488055080991604087)
  ·
    refine ⟨34309418232082621487406131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22872945488055080991604087 34309418232082621487406131)
    ·
      refine ⟨51464127348123932231109197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34309418232082621487406131 51464127348123932231109197)
      ·
        refine ⟨19299047755546474586665949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51464127348123932231109197 19299047755546474586665949)
        ·
          refine ⟨7237142908329927969999731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19299047755546474586665949 7237142908329927969999731)
          ·
            refine ⟨10855714362494891954999597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7237142908329927969999731 10855714362494891954999597)
            ·
              refine ⟨4070892885935584483124849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10855714362494891954999597 4070892885935584483124849)
              ·
                refine ⟨3053169664451688362343637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4070892885935584483124849 3053169664451688362343637)
                ·
                  refine ⟨71558664010586445992429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3053169664451688362343637 71558664010586445992429)
                  ·
                    rfl

theorem cell23_1254240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 7].length) (baseStart_1254240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254240 prefixEnd_1254240 := by exact prefixLift 1254240
  have htrace : WordTrace (prefixWord ++ tailWord_1254240) baseStart_1254240 baseEnd_1254240 := by
    simpa [prefixWord, tailWord_1254240, baseEnd_1254240] using wordTrace_append hprefix tailTrace_1254240
  have hstable : (prefixWord ++ tailWord_1254240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254240).length < 2 ^ (prefixWord ++ tailWord_1254240).sum := by decide
  have hdescent : baseEnd_1254240 < baseStart_1254240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254257 : List Nat := [1, 2, 2, 2, 1, 4, 1, 5, 5]
def baseStart_1254257 : Nat := 118140960795 + 1254257 * 2 ^ 59
def prefixEnd_1254257 : Nat := 4983230072969 + 3 ^ 40 * 1254257 * 2
def baseEnd_1254257 : Nat := 71559633918489383046587

theorem tailTrace_1254257 : CollatzResearch.WordTrace tailWord_1254257 prefixEnd_1254257 71559633918489383046587 := by
  unfold tailWord_1254257
  simp only [CollatzResearch.WordTrace]
  refine ⟨45746511017048573886577025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30497674011365715924384683 45746511017048573886577025)
  ·
    refine ⟨34309883262786430414932769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45746511017048573886577025 34309883262786430414932769)
    ·
      refine ⟨25732412447089822811199577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34309883262786430414932769 25732412447089822811199577)
      ·
        refine ⟨19299309335317367108399683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25732412447089822811199577 19299309335317367108399683)
        ·
          refine ⟨28948964002976050662599525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19299309335317367108399683 28948964002976050662599525)
          ·
            refine ⟨5427930750558009499237411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28948964002976050662599525 5427930750558009499237411)
            ·
              refine ⟨8141896125837014248856117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5427930750558009499237411 8141896125837014248856117)
              ·
                refine ⟨763302761797220085830261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8141896125837014248856117 763302761797220085830261)
                ·
                  refine ⟨71559633918489383046587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 763302761797220085830261 71559633918489383046587)
                  ·
                    rfl

theorem cell23_1254257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 5].length) (baseStart_1254257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254257 prefixEnd_1254257 := by exact prefixLift 1254257
  have htrace : WordTrace (prefixWord ++ tailWord_1254257) baseStart_1254257 baseEnd_1254257 := by
    simpa [prefixWord, tailWord_1254257, baseEnd_1254257] using wordTrace_append hprefix tailTrace_1254257
  have hstable : (prefixWord ++ tailWord_1254257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254257).length < 2 ^ (prefixWord ++ tailWord_1254257).sum := by decide
  have hdescent : baseEnd_1254257 < baseStart_1254257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254307 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 1, 6, 2]
def baseStart_1254307 : Nat := 118140960795 + 1254307 * 2 ^ 59
def prefixEnd_1254307 : Nat := 4983230072969 + 3 ^ 40 * 1254307 * 2
def baseEnd_1254307 : Nat := 644062379299129251794053

theorem tailTrace_1254307 : CollatzResearch.WordTrace tailWord_1254307 prefixEnd_1254307 644062379299129251794053 := by
  unfold tailWord_1254307
  simp only [CollatzResearch.WordTrace]
  refine ⟨45748334666867432425897175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30498889777911621617264783 45748334666867432425897175)
  ·
    refine ⟨68622502000301148638845763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45748334666867432425897175 68622502000301148638845763)
    ·
      refine ⟨102933753000451722958268645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68622502000301148638845763 102933753000451722958268645)
      ·
        refine ⟨19300078687584698054675371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102933753000451722958268645 19300078687584698054675371)
        ·
          refine ⟨28950118031377047082013057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19300078687584698054675371 28950118031377047082013057)
          ·
            refine ⟨21712588523532785311509793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28950118031377047082013057 21712588523532785311509793)
            ·
              refine ⟨16284441392649588983632345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21712588523532785311509793 16284441392649588983632345)
              ·
                refine ⟨12213331044487191737724259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16284441392649588983632345 12213331044487191737724259)
                ·
                  refine ⟨18319996566730787606586389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12213331044487191737724259 18319996566730787606586389)
                  ·
                    refine ⟨858749839065505669058737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18319996566730787606586389 858749839065505669058737)
                    ·
                      refine ⟨644062379299129251794053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858749839065505669058737 644062379299129251794053)
                      ·
                        rfl

theorem cell23_1254307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_1254307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254307 prefixEnd_1254307 := by exact prefixLift 1254307
  have htrace : WordTrace (prefixWord ++ tailWord_1254307) baseStart_1254307 baseEnd_1254307 := by
    simpa [prefixWord, tailWord_1254307, baseEnd_1254307] using wordTrace_append hprefix tailTrace_1254307
  have hstable : (prefixWord ++ tailWord_1254307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254307).length < 2 ^ (prefixWord ++ tailWord_1254307).sum := by decide
  have hdescent : baseEnd_1254307 < baseStart_1254307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254327 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_1254327 : Nat := 118140960795 + 1254327 * 2 ^ 59
def prefixEnd_1254327 : Nat := 4983230072969 + 3 ^ 40 * 1254327 * 2
def baseEnd_1254327 : Nat := 644072648912219173543961

theorem tailTrace_1254327 : CollatzResearch.WordTrace tailWord_1254327 prefixEnd_1254327 644072648912219173543961 := by
  unfold tailWord_1254327
  simp only [CollatzResearch.WordTrace]
  refine ⟨45749064126794975841625235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30499376084529983894416823 45749064126794975841625235)
  ·
    refine ⟨68623596190192463762437853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45749064126794975841625235 68623596190192463762437853)
    ·
      refine ⟨25733848571322173910914195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68623596190192463762437853 25733848571322173910914195)
      ·
        refine ⟨38600772856983260866371293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25733848571322173910914195 38600772856983260866371293)
        ·
          refine ⟨14475289821368722824889235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38600772856983260866371293 14475289821368722824889235)
          ·
            refine ⟨21712934732053084237333853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14475289821368722824889235 21712934732053084237333853)
            ·
              refine ⟨8142350524519906589000195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21712934732053084237333853 8142350524519906589000195)
              ·
                refine ⟨12213525786779859883500293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8142350524519906589000195 12213525786779859883500293)
                ·
                  refine ⟨2290036085021223728156305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12213525786779859883500293 2290036085021223728156305)
                  ·
                    refine ⟨1717527063765917796117229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2290036085021223728156305 1717527063765917796117229)
                    ·
                      refine ⟨644072648912219173543961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1717527063765917796117229 644072648912219173543961)
                      ·
                        rfl

theorem cell23_1254327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_1254327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254327 prefixEnd_1254327 := by exact prefixLift 1254327
  have htrace : WordTrace (prefixWord ++ tailWord_1254327) baseStart_1254327 baseEnd_1254327 := by
    simpa [prefixWord, tailWord_1254327, baseEnd_1254327] using wordTrace_append hprefix tailTrace_1254327
  have hstable : (prefixWord ++ tailWord_1254327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254327).length < 2 ^ (prefixWord ++ tailWord_1254327).sum := by decide
  have hdescent : baseEnd_1254327 < baseStart_1254327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254330 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 8]
def baseStart_1254330 : Nat := 118140960795 + 1254330 * 2 ^ 59
def prefixEnd_1254330 : Nat := 4983230072969 + 3 ^ 40 * 1254330 * 2
def baseEnd_1254330 : Nat := 71563798817131406867383

theorem tailTrace_1254330 : CollatzResearch.WordTrace tailWord_1254330 prefixEnd_1254330 71563798817131406867383 := by
  unfold tailWord_1254330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11437293386446026838496111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30499449030522738235989629 11437293386446026838496111)
  ·
    refine ⟨17155940079669040257744167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11437293386446026838496111 17155940079669040257744167)
    ·
      refine ⟨25733910119503560386616251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17155940079669040257744167 25733910119503560386616251)
      ·
        refine ⟨38600865179255340579924377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25733910119503560386616251 38600865179255340579924377)
        ·
          refine ⟨28950648884441505434943283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38600865179255340579924377 28950648884441505434943283)
          ·
            refine ⟨43425973326662258152414925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28950648884441505434943283 43425973326662258152414925)
            ·
              refine ⟨16284739997498346807155597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43425973326662258152414925 16284739997498346807155597)
              ·
                refine ⟨6106777499061880052683349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16284739997498346807155597 6106777499061880052683349)
                ·
                  refine ⟨71563798817131406867383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6106777499061880052683349 71563798817131406867383)
                  ·
                    rfl

theorem cell23_1254330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_1254330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254330 prefixEnd_1254330 := by exact prefixLift 1254330
  have htrace : WordTrace (prefixWord ++ tailWord_1254330) baseStart_1254330 baseEnd_1254330 := by
    simpa [prefixWord, tailWord_1254330, baseEnd_1254330] using wordTrace_append hprefix tailTrace_1254330
  have hstable : (prefixWord ++ tailWord_1254330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254330).length < 2 ^ (prefixWord ++ tailWord_1254330).sum := by decide
  have hdescent : baseEnd_1254330 < baseStart_1254330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254347 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 6]
def baseStart_1254347 : Nat := 118140960795 + 1254347 * 2 ^ 59
def prefixEnd_1254347 : Nat := 4983230072969 + 3 ^ 40 * 1254347 * 2
def baseEnd_1254347 : Nat := 71564768725034343921541

theorem tailTrace_1254347 : CollatzResearch.WordTrace tailWord_1254347 prefixEnd_1254347 71564768725034343921541 := by
  unfold tailWord_1254347
  simp only [CollatzResearch.WordTrace]
  refine ⟨45749793586722519257353295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30499862391148346171568863 45749793586722519257353295)
  ·
    refine ⟨68624690380083778886029943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45749793586722519257353295 68624690380083778886029943)
    ·
      refine ⟨102937035570125668329044915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68624690380083778886029943 102937035570125668329044915)
      ·
        refine ⟨154405553355188502493567373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102937035570125668329044915 154405553355188502493567373)
        ·
          refine ⟨57902082508195688435087765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154405553355188502493567373 57902082508195688435087765)
          ·
            refine ⟨2714160117571672895394739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57902082508195688435087765 2714160117571672895394739)
            ·
              refine ⟨4071240176357509343092109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714160117571672895394739 4071240176357509343092109)
              ·
                refine ⟨1526715066134066003659541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4071240176357509343092109 1526715066134066003659541)
                ·
                  refine ⟨71564768725034343921541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1526715066134066003659541 71564768725034343921541)
                  ·
                    rfl

theorem cell23_1254347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 6].length) (baseStart_1254347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254347 prefixEnd_1254347 := by exact prefixLift 1254347
  have htrace : WordTrace (prefixWord ++ tailWord_1254347) baseStart_1254347 baseEnd_1254347 := by
    simpa [prefixWord, tailWord_1254347, baseEnd_1254347] using wordTrace_append hprefix tailTrace_1254347
  have hstable : (prefixWord ++ tailWord_1254347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254347).length < 2 ^ (prefixWord ++ tailWord_1254347).sum := by decide
  have hdescent : baseEnd_1254347 < baseStart_1254347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254414 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1254414 : Nat := 118140960795 + 1254414 * 2 ^ 59
def prefixEnd_1254414 : Nat := 4983230072969 + 3 ^ 40 * 1254414 * 2
def baseEnd_1254414 : Nat := 644117321729160333156061

theorem tailTrace_1254414 : CollatzResearch.WordTrace tailWord_1254414 prefixEnd_1254414 644117321729160333156061 := by
  unfold tailWord_1254414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5719029659684973712505287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30501491518319859800028197 5719029659684973712505287)
  ·
    refine ⟨8578544489527460568757931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5719029659684973712505287 8578544489527460568757931)
    ·
      refine ⟨12867816734291190853136897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8578544489527460568757931 12867816734291190853136897)
      ·
        refine ⟨9650862550718393139852673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12867816734291190853136897 9650862550718393139852673)
        ·
          refine ⟨7238146913038794854889505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9650862550718393139852673 7238146913038794854889505)
          ·
            refine ⟨5428610184779096141167129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7238146913038794854889505 5428610184779096141167129)
            ·
              refine ⟨4071457638584322105875347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5428610184779096141167129 4071457638584322105875347)
              ·
                refine ⟨6107186457876483158813021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4071457638584322105875347 6107186457876483158813021)
                ·
                  refine ⟨2290194921703681184554883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6107186457876483158813021 2290194921703681184554883)
                  ·
                    refine ⟨3435292382555521776832325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2290194921703681184554883 3435292382555521776832325)
                    ·
                      refine ⟨644117321729160333156061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3435292382555521776832325 644117321729160333156061)
                      ·
                        rfl

theorem cell23_1254414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1254414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254414 prefixEnd_1254414 := by exact prefixLift 1254414
  have htrace : WordTrace (prefixWord ++ tailWord_1254414) baseStart_1254414 baseEnd_1254414 := by
    simpa [prefixWord, tailWord_1254414, baseEnd_1254414] using wordTrace_append hprefix tailTrace_1254414
  have hstable : (prefixWord ++ tailWord_1254414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254414).length < 2 ^ (prefixWord ++ tailWord_1254414).sum := by decide
  have hdescent : baseEnd_1254414 < baseStart_1254414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254428 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1254428 : Nat := 118140960795 + 1254428 * 2 ^ 59
def prefixEnd_1254428 : Nat := 4983230072969 + 3 ^ 40 * 1254428 * 2
def baseEnd_1254428 : Nat := 214708170152774426126999

theorem tailTrace_1254428 : CollatzResearch.WordTrace tailWord_1254428 prefixEnd_1254428 214708170152774426126999 := by
  unfold tailWord_1254428
  simp only [CollatzResearch.WordTrace]
  refine ⟨22876373949714535045525969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30501831932952713394034625 22876373949714535045525969)
  ·
    refine ⟨17157280462285901284144477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22876373949714535045525969 17157280462285901284144477)
    ·
      refine ⟨6433980173357212981554179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17157280462285901284144477 6433980173357212981554179)
      ·
        refine ⟨9650970260035819472331269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6433980173357212981554179 9650970260035819472331269)
        ·
          refine ⟨1809556923756716151062113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9650970260035819472331269 1809556923756716151062113)
          ·
            refine ⟨1357167692817537113296585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1809556923756716151062113 1357167692817537113296585)
            ·
              refine ⟨1017875769613152834972439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357167692817537113296585 1017875769613152834972439)
              ·
                refine ⟨1526813654419729252458659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017875769613152834972439 1526813654419729252458659)
                ·
                  refine ⟨2290220481629593878687989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526813654419729252458659 2290220481629593878687989)
                  ·
                    refine ⟨214708170152774426126999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2290220481629593878687989 214708170152774426126999)
                    ·
                      rfl

theorem cell23_1254428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1254428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254428 prefixEnd_1254428 := by exact prefixLift 1254428
  have htrace : WordTrace (prefixWord ++ tailWord_1254428) baseStart_1254428 baseEnd_1254428 := by
    simpa [prefixWord, tailWord_1254428, baseEnd_1254428] using wordTrace_append hprefix tailTrace_1254428
  have hstable : (prefixWord ++ tailWord_1254428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254428).length < 2 ^ (prefixWord ++ tailWord_1254428).sum := by decide
  have hdescent : baseEnd_1254428 < baseStart_1254428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254431 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 1, 1, 4]
def baseStart_1254431 : Nat := 118140960795 + 1254431 * 2 ^ 59
def prefixEnd_1254431 : Nat := 4983230072969 + 3 ^ 40 * 1254431 * 2
def baseEnd_1254431 : Nat := 644126050900286766643483

theorem tailTrace_1254431 : CollatzResearch.WordTrace tailWord_1254431 prefixEnd_1254431 644126050900286766643483 := by
  unfold tailWord_1254431
  simp only [CollatzResearch.WordTrace]
  refine ⟨45752857318418201603411147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30501904878945467735607431 45752857318418201603411147)
  ·
    refine ⟨68629285977627302405116721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45752857318418201603411147 68629285977627302405116721)
    ·
      refine ⟨51471964483220476803837541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68629285977627302405116721 51471964483220476803837541)
      ·
        refine ⟨9650993340603839400719539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51471964483220476803837541 9650993340603839400719539)
        ·
          refine ⟨14476490010905759101079309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9650993340603839400719539 14476490010905759101079309)
          ·
            refine ⟨5428683754089659662904741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14476490010905759101079309 5428683754089659662904741)
            ·
              refine ⟨1017878203891811186794639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5428683754089659662904741 1017878203891811186794639)
              ·
                refine ⟨1526817305837716780191959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017878203891811186794639 1526817305837716780191959)
                ·
                  refine ⟨2290225958756575170287939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526817305837716780191959 2290225958756575170287939)
                  ·
                    refine ⟨3435338938134862755431909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2290225958756575170287939 3435338938134862755431909)
                    ·
                      refine ⟨644126050900286766643483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3435338938134862755431909 644126050900286766643483)
                      ·
                        rfl

theorem cell23_1254431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_1254431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254431 prefixEnd_1254431 := by exact prefixLift 1254431
  have htrace : WordTrace (prefixWord ++ tailWord_1254431) baseStart_1254431 baseEnd_1254431 := by
    simpa [prefixWord, tailWord_1254431, baseEnd_1254431] using wordTrace_append hprefix tailTrace_1254431
  have hstable : (prefixWord ++ tailWord_1254431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254431).length < 2 ^ (prefixWord ++ tailWord_1254431).sum := by decide
  have hdescent : baseEnd_1254431 < baseStart_1254431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254448 : List Nat := [2, 1, 1, 1, 2, 4, 1, 6, 1, 2, 2]
def baseStart_1254448 : Nat := 118140960795 + 1254448 * 2 ^ 59
def prefixEnd_1254448 : Nat := 4983230072969 + 3 ^ 40 * 1254448 * 2
def baseEnd_1254448 : Nat := 644134780071413200130905

theorem tailTrace_1254448 : CollatzResearch.WordTrace tailWord_1254448 prefixEnd_1254448 644134780071413200130905 := by
  unfold tailWord_1254448
  simp only [CollatzResearch.WordTrace]
  refine ⟨22876738679678306753389999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30502318239571075671186665 22876738679678306753389999)
  ·
    refine ⟨34315108019517460130084999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22876738679678306753389999 34315108019517460130084999)
    ·
      refine ⟨51472662029276190195127499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34315108019517460130084999 51472662029276190195127499)
      ·
        refine ⟨77208993043914285292691249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51472662029276190195127499 77208993043914285292691249)
        ·
          refine ⟨57906744782935713969518437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77208993043914285292691249 57906744782935713969518437)
          ·
            refine ⟨10857514646800446369284707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57906744782935713969518437 10857514646800446369284707)
            ·
              refine ⟨16286271970200669553927061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10857514646800446369284707 16286271970200669553927061)
              ·
                refine ⟨763418998603156385340331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16286271970200669553927061 763418998603156385340331)
                ·
                  refine ⟨1145128497904734578010497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763418998603156385340331 1145128497904734578010497)
                  ·
                    refine ⟨858846373428550933507873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1145128497904734578010497 858846373428550933507873)
                    ·
                      refine ⟨644134780071413200130905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858846373428550933507873 644134780071413200130905)
                      ·
                        rfl

theorem cell23_1254448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 2, 2].length) (baseStart_1254448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254448 prefixEnd_1254448 := by exact prefixLift 1254448
  have htrace : WordTrace (prefixWord ++ tailWord_1254448) baseStart_1254448 baseEnd_1254448 := by
    simpa [prefixWord, tailWord_1254448, baseEnd_1254448] using wordTrace_append hprefix tailTrace_1254448
  have hstable : (prefixWord ++ tailWord_1254448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254448).length < 2 ^ (prefixWord ++ tailWord_1254448).sum := by decide
  have hdescent : baseEnd_1254448 < baseStart_1254448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254461 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_1254461 : Nat := 118140960795 + 1254461 * 2 ^ 59
def prefixEnd_1254461 : Nat := 4983230072969 + 3 ^ 40 * 1254461 * 2
def baseEnd_1254461 : Nat := 644141455319921649268345

theorem tailTrace_1254461 : CollatzResearch.WordTrace tailWord_1254461 prefixEnd_1254461 644141455319921649268345 := by
  unfold tailWord_1254461
  simp only [CollatzResearch.WordTrace]
  refine ⟨45753951508309516727003237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30502634338873011151335491 45753951508309516727003237)
  ·
    refine ⟨8578865907808034386313107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45753951508309516727003237 8578865907808034386313107)
    ·
      refine ⟨12868298861712051579469661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8578865907808034386313107 12868298861712051579469661)
      ·
        refine ⟨4825612073142019342301123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12868298861712051579469661 4825612073142019342301123)
        ·
          refine ⟨7238418109713029013451685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4825612073142019342301123 7238418109713029013451685)
          ·
            refine ⟨1357203395571192940022191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7238418109713029013451685 1357203395571192940022191)
            ·
              refine ⟨2035805093356789410033287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357203395571192940022191 2035805093356789410033287)
              ·
                refine ⟨3053707640035184115049931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035805093356789410033287 3053707640035184115049931)
                ·
                  refine ⟨4580561460052776172574897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053707640035184115049931 4580561460052776172574897)
                  ·
                    refine ⟨3435421095039582129431173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4580561460052776172574897 3435421095039582129431173)
                    ·
                      refine ⟨644141455319921649268345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3435421095039582129431173 644141455319921649268345)
                      ·
                        rfl

theorem cell23_1254461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_1254461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254461 prefixEnd_1254461 := by exact prefixLift 1254461
  have htrace : WordTrace (prefixWord ++ tailWord_1254461) baseStart_1254461 baseEnd_1254461 := by
    simpa [prefixWord, tailWord_1254461, baseEnd_1254461] using wordTrace_append hprefix tailTrace_1254461
  have hstable : (prefixWord ++ tailWord_1254461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254461).length < 2 ^ (prefixWord ++ tailWord_1254461).sum := by decide
  have hdescent : baseEnd_1254461 < baseStart_1254461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254482 : List Nat := [3, 2, 2, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_1254482 : Nat := 118140960795 + 1254482 * 2 ^ 59
def prefixEnd_1254482 : Nat := 4983230072969 + 3 ^ 40 * 1254482 * 2
def baseEnd_1254482 : Nat := 644152238413666067105749

theorem tailTrace_1254482 : CollatzResearch.WordTrace tailWord_1254482 prefixEnd_1254482 644152238413666067105749 := by
  unfold tailWord_1254482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11438679360308359328379425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30503144960822291542345133 11438679360308359328379425)
  ·
    refine ⟨8579009520231269496284569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11438679360308359328379425 8579009520231269496284569)
    ·
      refine ⟨6434257140173452122213427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8579009520231269496284569 6434257140173452122213427)
      ·
        refine ⟨9651385710260178183320141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6434257140173452122213427 9651385710260178183320141)
        ·
          refine ⟨3619269641347566818745053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9651385710260178183320141 3619269641347566818745053)
          ·
            refine ⟨1357226115505337557029395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3619269641347566818745053 1357226115505337557029395)
            ·
              refine ⟨2035839173258006335544093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357226115505337557029395 2035839173258006335544093)
              ·
                refine ⟨763439689971752375829035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2035839173258006335544093 763439689971752375829035)
                ·
                  refine ⟨1145159534957628563743553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763439689971752375829035 1145159534957628563743553)
                  ·
                    refine ⟨858869651218221422807665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1145159534957628563743553 858869651218221422807665)
                    ·
                      refine ⟨644152238413666067105749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858869651218221422807665 644152238413666067105749)
                      ·
                        rfl

theorem cell23_1254482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_1254482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254482 prefixEnd_1254482 := by exact prefixLift 1254482
  have htrace : WordTrace (prefixWord ++ tailWord_1254482) baseStart_1254482 baseEnd_1254482 := by
    simpa [prefixWord, tailWord_1254482, baseEnd_1254482] using wordTrace_append hprefix tailTrace_1254482
  have hstable : (prefixWord ++ tailWord_1254482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254482).length < 2 ^ (prefixWord ++ tailWord_1254482).sum := by decide
  have hdescent : baseEnd_1254482 < baseStart_1254482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254487 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1254487 : Nat := 118140960795 + 1254487 * 2 ^ 59
def prefixEnd_1254487 : Nat := 4983230072969 + 3 ^ 40 * 1254487 * 2
def baseEnd_1254487 : Nat := 644154805816938547543225

theorem tailTrace_1254487 : CollatzResearch.WordTrace tailWord_1254487 prefixEnd_1254487 644154805816938547543225 := by
  unfold tailWord_1254487
  simp only [CollatzResearch.WordTrace]
  refine ⟨45754899806215323167449715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30503266537476882111633143 45754899806215323167449715)
  ·
    refine ⟨68632349709322984751174573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45754899806215323167449715 68632349709322984751174573)
    ·
      refine ⟨25737131140996119281690465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68632349709322984751174573 25737131140996119281690465)
      ·
        refine ⟨19302848355747089461267849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25737131140996119281690465 19302848355747089461267849)
        ·
          refine ⟨14477136266810317095950887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19302848355747089461267849 14477136266810317095950887)
          ·
            refine ⟨21715704400215475643926331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14477136266810317095950887 21715704400215475643926331)
            ·
              refine ⟨32573556600323213465889497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21715704400215475643926331 32573556600323213465889497)
              ·
                refine ⟨24430167450242410099417123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32573556600323213465889497 24430167450242410099417123)
                ·
                  refine ⟨36645251175363615149125685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24430167450242410099417123 36645251175363615149125685)
                  ·
                    refine ⟨3435492297690338920230533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36645251175363615149125685 3435492297690338920230533)
                    ·
                      refine ⟨644154805816938547543225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3435492297690338920230533 644154805816938547543225)
                      ·
                        rfl

theorem cell23_1254487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1254487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254487 prefixEnd_1254487 := by exact prefixLift 1254487
  have htrace : WordTrace (prefixWord ++ tailWord_1254487) baseStart_1254487 baseEnd_1254487 := by
    simpa [prefixWord, tailWord_1254487, baseEnd_1254487] using wordTrace_append hprefix tailTrace_1254487
  have hstable : (prefixWord ++ tailWord_1254487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254487).length < 2 ^ (prefixWord ++ tailWord_1254487).sum := by decide
  have hdescent : baseEnd_1254487 < baseStart_1254487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254497 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 4, 6]
def baseStart_1254497 : Nat := 118140960795 + 1254497 * 2 ^ 59
def prefixEnd_1254497 : Nat := 4983230072969 + 3 ^ 40 * 1254497 * 2
def baseEnd_1254497 : Nat := 214719980207827836139393

theorem tailTrace_1254497 : CollatzResearch.WordTrace tailWord_1254497 prefixEnd_1254497 214719980207827836139393 := by
  unfold tailWord_1254497
  simp only [CollatzResearch.WordTrace]
  refine ⟨45755264536179094875313745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30503509690786063250209163 45755264536179094875313745)
  ·
    refine ⟨34316448402134321156485309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45755264536179094875313745 34316448402134321156485309)
    ·
      refine ⟨12868668150800370433681991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34316448402134321156485309 12868668150800370433681991)
      ·
        refine ⟨19303002226200555650522987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12868668150800370433681991 19303002226200555650522987)
        ·
          refine ⟨28954503339300833475784481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19303002226200555650522987 28954503339300833475784481)
          ·
            refine ⟨21715877504475625106838361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28954503339300833475784481 21715877504475625106838361)
            ·
              refine ⟨16286908128356718830128771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21715877504475625106838361 16286908128356718830128771)
              ·
                refine ⟨24430362192535078245193157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16286908128356718830128771 24430362192535078245193157)
                ·
                  refine ⟨4580692911100327170973717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24430362192535078245193157 4580692911100327170973717)
                  ·
                    refine ⟨214719980207827836139393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4580692911100327170973717 214719980207827836139393)
                    ·
                      rfl

theorem cell23_1254497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_1254497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254497 prefixEnd_1254497 := by exact prefixLift 1254497
  have htrace : WordTrace (prefixWord ++ tailWord_1254497) baseStart_1254497 baseEnd_1254497 := by
    simpa [prefixWord, tailWord_1254497, baseEnd_1254497] using wordTrace_append hprefix tailTrace_1254497
  have hstable : (prefixWord ++ tailWord_1254497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254497).length < 2 ^ (prefixWord ++ tailWord_1254497).sum := by decide
  have hdescent : baseEnd_1254497 < baseStart_1254497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254498 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1254498 : Nat := 118140960795 + 1254498 * 2 ^ 59
def prefixEnd_1254498 : Nat := 4983230072969 + 3 ^ 40 * 1254498 * 2
def baseEnd_1254498 : Nat := 644160454104138004505675

theorem tailTrace_1254498 : CollatzResearch.WordTrace tailWord_1254498 prefixEnd_1254498 644160454104138004505675 := by
  unfold tailWord_1254498
  simp only [CollatzResearch.WordTrace]
  refine ⟨11438825252293868011525037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30503534006116981364066765 11438825252293868011525037)
  ·
    refine ⟨4289559469610200504321889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11438825252293868011525037 4289559469610200504321889)
    ·
      refine ⟨3217169602207650378241417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4289559469610200504321889 3217169602207650378241417)
      ·
        refine ⟨2412877201655737783681063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3217169602207650378241417 2412877201655737783681063)
        ·
          refine ⟨3619315802483606675521595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412877201655737783681063 3619315802483606675521595)
          ·
            refine ⟨5428973703725410013282393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619315802483606675521595 5428973703725410013282393)
            ·
              refine ⟨4071730277794057509961795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5428973703725410013282393 4071730277794057509961795)
              ·
                refine ⟨6107595416691086264942693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4071730277794057509961795 6107595416691086264942693)
                ·
                  refine ⟨1145174140629578674676755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6107595416691086264942693 1145174140629578674676755)
                  ·
                    refine ⟨1717761210944368012015133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1145174140629578674676755 1717761210944368012015133)
                    ·
                      refine ⟨644160454104138004505675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1717761210944368012015133 644160454104138004505675)
                      ·
                        rfl

theorem cell23_1254498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1254498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254498 prefixEnd_1254498 := by exact prefixLift 1254498
  have htrace : WordTrace (prefixWord ++ tailWord_1254498) baseStart_1254498 baseEnd_1254498 := by
    simpa [prefixWord, tailWord_1254498, baseEnd_1254498] using wordTrace_append hprefix tailTrace_1254498
  have hstable : (prefixWord ++ tailWord_1254498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254498).length < 2 ^ (prefixWord ++ tailWord_1254498).sum := by decide
  have hdescent : baseEnd_1254498 < baseStart_1254498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254561 : List Nat := [1, 2, 3, 3, 1, 1, 3, 4, 5]
def baseStart_1254561 : Nat := 118140960795 + 1254561 * 2 ^ 59
def prefixEnd_1254561 : Nat := 4983230072969 + 3 ^ 40 * 1254561 * 2
def baseEnd_1254561 : Nat := 71576978153930139779765

theorem tailTrace_1254561 : CollatzResearch.WordTrace tailWord_1254561 prefixEnd_1254561 71576978153930139779765 := by
  unfold tailWord_1254561
  simp only [CollatzResearch.WordTrace]
  refine ⟨45757598807947233805643537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30505065871964822537095691 45757598807947233805643537)
  ·
    refine ⟨34318199105960425354232653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45757598807947233805643537 34318199105960425354232653)
    ·
      refine ⟨12869324664735159507837245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34318199105960425354232653 12869324664735159507837245)
      ·
        refine ⟨4825996749275684815438967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12869324664735159507837245 4825996749275684815438967)
        ·
          refine ⟨7238995123913527223158451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4825996749275684815438967 7238995123913527223158451)
          ·
            refine ⟨10858492685870290834737677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7238995123913527223158451 10858492685870290834737677)
            ·
              refine ⟨4071934757201359063026629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10858492685870290834737677 4071934757201359063026629)
              ·
                refine ⟨763487766975254824317493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4071934757201359063026629 763487766975254824317493)
                ·
                  refine ⟨71576978153930139779765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 763487766975254824317493 71576978153930139779765)
                  ·
                    rfl

theorem cell23_1254561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 5].length) (baseStart_1254561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254561 prefixEnd_1254561 := by exact prefixLift 1254561
  have htrace : WordTrace (prefixWord ++ tailWord_1254561) baseStart_1254561 baseEnd_1254561 := by
    simpa [prefixWord, tailWord_1254561, baseEnd_1254561] using wordTrace_append hprefix tailTrace_1254561
  have hstable : (prefixWord ++ tailWord_1254561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254561).length < 2 ^ (prefixWord ++ tailWord_1254561).sum := by decide
  have hdescent : baseEnd_1254561 < baseStart_1254561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254587 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 1, 10]
def baseStart_1254587 : Nat := 118140960795 + 1254587 * 2 ^ 59
def prefixEnd_1254587 : Nat := 4983230072969 + 3 ^ 40 * 1254587 * 2
def baseEnd_1254587 : Nat := 214735384627462718764255

theorem tailTrace_1254587 : CollatzResearch.WordTrace tailWord_1254587 prefixEnd_1254587 214735384627462718764255 := by
  unfold tailWord_1254587
  simp only [CollatzResearch.WordTrace]
  refine ⟨45758547105853040246090015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30505698070568693497393343 45758547105853040246090015)
  ·
    refine ⟨68637820658779560369135023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45758547105853040246090015 68637820658779560369135023)
    ·
      refine ⟨102956730988169340553702535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68637820658779560369135023 102956730988169340553702535)
      ·
        refine ⟨154435096482254010830553803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102956730988169340553702535 154435096482254010830553803)
        ·
          refine ⟨231652644723381016245830705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154435096482254010830553803 231652644723381016245830705)
          ·
            refine ⟨173739483542535762184373029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231652644723381016245830705 173739483542535762184373029)
            ·
              refine ⟨32576153164225455409569943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173739483542535762184373029 32576153164225455409569943)
              ·
                refine ⟨48864229746338183114354915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32576153164225455409569943 48864229746338183114354915)
                ·
                  refine ⟨73296344619507274671532373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48864229746338183114354915 73296344619507274671532373)
                  ·
                    refine ⟨214735384627462718764255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 73296344619507274671532373 214735384627462718764255)
                    ·
                      rfl

theorem cell23_1254587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 10].length) (baseStart_1254587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254587 prefixEnd_1254587 := by exact prefixLift 1254587
  have htrace : WordTrace (prefixWord ++ tailWord_1254587) baseStart_1254587 baseEnd_1254587 := by
    simpa [prefixWord, tailWord_1254587, baseEnd_1254587] using wordTrace_append hprefix tailTrace_1254587
  have hstable : (prefixWord ++ tailWord_1254587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254587).length < 2 ^ (prefixWord ++ tailWord_1254587).sum := by decide
  have hdescent : baseEnd_1254587 < baseStart_1254587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254655 : List Nat := [1, 1, 2, 2, 1, 7, 1, 3, 1, 4]
def baseStart_1254655 : Nat := 118140960795 + 1254655 * 2 ^ 59
def prefixEnd_1254655 : Nat := 4983230072969 + 3 ^ 40 * 1254655 * 2
def baseEnd_1254655 : Nat := 214747023522297963414151

theorem tailTrace_1254655 : CollatzResearch.WordTrace tailWord_1254655 prefixEnd_1254655 214747023522297963414151 := by
  unfold tailWord_1254655
  simp only [CollatzResearch.WordTrace]
  refine ⟨45761027269606687859565419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30507351513071125239710279 45761027269606687859565419)
  ·
    refine ⟨68641540904410031789348129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45761027269606687859565419 68641540904410031789348129)
    ·
      refine ⟨51481155678307523842011097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68641540904410031789348129 51481155678307523842011097)
      ·
        refine ⟨38610866758730642881508323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51481155678307523842011097 38610866758730642881508323)
        ·
          refine ⟨57916300138095964322262485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38610866758730642881508323 57916300138095964322262485)
          ·
            refine ⟨1357413284486624163803027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 57916300138095964322262485 1357413284486624163803027)
            ·
              refine ⟨2036119926729936245704541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357413284486624163803027 2036119926729936245704541)
              ·
                refine ⟨763544972523726092139203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036119926729936245704541 763544972523726092139203)
                ·
                  refine ⟨1145317458785589138208805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763544972523726092139203 1145317458785589138208805)
                  ·
                    refine ⟨214747023522297963414151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1145317458785589138208805 214747023522297963414151)
                    ·
                      rfl

theorem cell23_1254655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 4].length) (baseStart_1254655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254655 prefixEnd_1254655 := by exact prefixLift 1254655
  have htrace : WordTrace (prefixWord ++ tailWord_1254655) baseStart_1254655 baseEnd_1254655 := by
    simpa [prefixWord, tailWord_1254655, baseEnd_1254655] using wordTrace_append hprefix tailTrace_1254655
  have hstable : (prefixWord ++ tailWord_1254655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254655).length < 2 ^ (prefixWord ++ tailWord_1254655).sum := by decide
  have hdescent : baseEnd_1254655 < baseStart_1254655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254685 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 6]
def baseStart_1254685 : Nat := 118140960795 + 1254685 * 2 ^ 59
def prefixEnd_1254685 : Nat := 4983230072969 + 3 ^ 40 * 1254685 * 2
def baseEnd_1254685 : Nat := 71584052776280974763035

theorem tailTrace_1254685 : CollatzResearch.WordTrace tailWord_1254685 prefixEnd_1254685 71584052776280974763035 := by
  unfold tailWord_1254685
  simp only [CollatzResearch.WordTrace]
  refine ⟨45762121459498002983157509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30508080972998668655438339 45762121459498002983157509)
  ·
    refine ⟨8580397773655875559342033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45762121459498002983157509 8580397773655875559342033)
    ·
      refine ⟨6435298330241906669506525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8580397773655875559342033 6435298330241906669506525)
      ·
        refine ⟨2413236873840715001064947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6435298330241906669506525 2413236873840715001064947)
        ·
          refine ⟨3619855310761072501597421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413236873840715001064947 3619855310761072501597421)
          ·
            refine ⟨1357445741535402188099033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3619855310761072501597421 1357445741535402188099033)
            ·
              refine ⟨1018084306151551641074275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357445741535402188099033 1018084306151551641074275)
              ·
                refine ⟨1527126459227327461611413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018084306151551641074275 1527126459227327461611413)
                ·
                  refine ⟨71584052776280974763035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1527126459227327461611413 71584052776280974763035)
                  ·
                    rfl

theorem cell23_1254685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_1254685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254685 prefixEnd_1254685 := by exact prefixLift 1254685
  have htrace : WordTrace (prefixWord ++ tailWord_1254685) baseStart_1254685 baseEnd_1254685 := by
    simpa [prefixWord, tailWord_1254685, baseEnd_1254685] using wordTrace_append hprefix tailTrace_1254685
  have hstable : (prefixWord ++ tailWord_1254685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254685).length < 2 ^ (prefixWord ++ tailWord_1254685).sum := by decide
  have hdescent : baseEnd_1254685 < baseStart_1254685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254698 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1254698 : Nat := 118140960795 + 1254698 * 2 ^ 59
def prefixEnd_1254698 : Nat := 4983230072969 + 3 ^ 40 * 1254698 * 2
def baseEnd_1254698 : Nat := 214754383411679074001585

theorem tailTrace_1254698 : CollatzResearch.WordTrace tailWord_1254698 prefixEnd_1254698 214754383411679074001585 := by
  unfold tailWord_1254698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11440648902112726550845187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30508397072300604135587165 11440648902112726550845187)
  ·
    refine ⟨17160973353169089826267781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11440648902112726550845187 17160973353169089826267781)
    ·
      refine ⟨3217682503719204342425209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17160973353169089826267781 3217682503719204342425209)
      ·
        refine ⟨2413261877789403256818907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3217682503719204342425209 2413261877789403256818907)
        ·
          refine ⟨3619892816684104885228361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413261877789403256818907 3619892816684104885228361)
          ·
            refine ⟨2714919612513078663921271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3619892816684104885228361 2714919612513078663921271)
            ·
              refine ⟨4072379418769617995881907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714919612513078663921271 4072379418769617995881907)
              ·
                refine ⟨6108569128154426993822861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4072379418769617995881907 6108569128154426993822861)
                ·
                  refine ⟨2290713423057910122683573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6108569128154426993822861 2290713423057910122683573)
                  ·
                    refine ⟨214754383411679074001585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2290713423057910122683573 214754383411679074001585)
                    ·
                      rfl

theorem cell23_1254698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1254698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254698 prefixEnd_1254698 := by exact prefixLift 1254698
  have htrace : WordTrace (prefixWord ++ tailWord_1254698) baseStart_1254698 baseEnd_1254698 := by
    simpa [prefixWord, tailWord_1254698, baseEnd_1254698] using wordTrace_append hprefix tailTrace_1254698
  have hstable : (prefixWord ++ tailWord_1254698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254698).length < 2 ^ (prefixWord ++ tailWord_1254698).sum := by decide
  have hdescent : baseEnd_1254698 < baseStart_1254698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254705 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 2, 3, 2]
def baseStart_1254705 : Nat := 118140960795 + 1254705 * 2 ^ 59
def prefixEnd_1254705 : Nat := 4983230072969 + 3 ^ 40 * 1254705 * 2
def baseEnd_1254705 : Nat := 644266744599618694617223

theorem tailTrace_1254705 : CollatzResearch.WordTrace tailWord_1254705 prefixEnd_1254705 644266744599618694617223 := by
  unfold tailWord_1254705
  simp only [CollatzResearch.WordTrace]
  refine ⟨45762850919425546398885569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30508567279617030932590379 45762850919425546398885569)
  ·
    refine ⟨34322138189569159799164177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45762850919425546398885569 34322138189569159799164177)
    ·
      refine ⟨25741603642176869849373133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34322138189569159799164177 25741603642176869849373133)
      ·
        refine ⟨9653101365816326193514925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25741603642176869849373133 9653101365816326193514925)
        ·
          refine ⟨3619913012181122322568097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9653101365816326193514925 3619913012181122322568097)
          ·
            refine ⟨2714934759135841741926073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3619913012181122322568097 2714934759135841741926073)
            ·
              refine ⟨2036201069351881306444555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2714934759135841741926073 2036201069351881306444555)
              ·
                refine ⟨3054301604027821959666833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036201069351881306444555 3054301604027821959666833)
                ·
                  refine ⟨2290726203020866469750125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3054301604027821959666833 2290726203020866469750125)
                  ·
                    refine ⟨859022326132824926156297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2290726203020866469750125 859022326132824926156297)
                    ·
                      refine ⟨644266744599618694617223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859022326132824926156297 644266744599618694617223)
                      ·
                        rfl

theorem cell23_1254705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_1254705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254705 prefixEnd_1254705 := by exact prefixLift 1254705
  have htrace : WordTrace (prefixWord ++ tailWord_1254705) baseStart_1254705 baseEnd_1254705 := by
    simpa [prefixWord, tailWord_1254705, baseEnd_1254705] using wordTrace_append hprefix tailTrace_1254705
  have hstable : (prefixWord ++ tailWord_1254705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254705).length < 2 ^ (prefixWord ++ tailWord_1254705).sum := by decide
  have hdescent : baseEnd_1254705 < baseStart_1254705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254741 : List Nat := [1, 3, 2, 2, 3, 1, 3, 8]
def baseStart_1254741 : Nat := 118140960795 + 1254741 * 2 ^ 59
def prefixEnd_1254741 : Nat := 4983230072969 + 3 ^ 40 * 1254741 * 2
def baseEnd_1254741 : Nat := 23862415922340020509891

theorem tailTrace_1254741 : CollatzResearch.WordTrace tailWord_1254741 prefixEnd_1254741 23862415922340020509891 := by
  unfold tailWord_1254741
  simp only [CollatzResearch.WordTrace]
  refine ⟨45764163947295124547196077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30509442631530083031464051 45764163947295124547196077)
  ·
    refine ⟨17161561480235671705198529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45764163947295124547196077 17161561480235671705198529)
    ·
      refine ⟨12871171110176753778898897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17161561480235671705198529 12871171110176753778898897)
      ·
        refine ⟨9653378332632565334174173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12871171110176753778898897 9653378332632565334174173)
        ·
          refine ⟨3620016874737212000315315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9653378332632565334174173 3620016874737212000315315)
          ·
            refine ⟨5430025312105818000472973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620016874737212000315315 5430025312105818000472973)
            ·
              refine ⟨2036259492039681750177365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5430025312105818000472973 2036259492039681750177365)
              ·
                refine ⟨23862415922340020509891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2036259492039681750177365 23862415922340020509891)
                ·
                  rfl

theorem cell23_1254741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 8].length) (baseStart_1254741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254741 prefixEnd_1254741 := by exact prefixLift 1254741
  have htrace : WordTrace (prefixWord ++ tailWord_1254741) baseStart_1254741 baseEnd_1254741 := by
    simpa [prefixWord, tailWord_1254741, baseEnd_1254741] using wordTrace_append hprefix tailTrace_1254741
  have hstable : (prefixWord ++ tailWord_1254741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254741).length < 2 ^ (prefixWord ++ tailWord_1254741).sum := by decide
  have hdescent : baseEnd_1254741 < baseStart_1254741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254768 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 4, 1, 3]
def baseStart_1254768 : Nat := 118140960795 + 1254768 * 2 ^ 59
def prefixEnd_1254768 : Nat := 4983230072969 + 3 ^ 40 * 1254768 * 2
def baseEnd_1254768 : Nat := 644299093880851948129433

theorem tailTrace_1254768 : CollatzResearch.WordTrace tailWord_1254768 prefixEnd_1254768 644299093880851948129433 := by
  unfold tailWord_1254768
  simp only [CollatzResearch.WordTrace]
  refine ⟨22882574359098654079214479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30510099145464872105619305 22882574359098654079214479)
  ·
    refine ⟨34323861538647981118821719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22882574359098654079214479 34323861538647981118821719)
    ·
      refine ⟨51485792307971971678232579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34323861538647981118821719 51485792307971971678232579)
      ·
        refine ⟨77228688461957957517348869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51485792307971971678232579 77228688461957957517348869)
        ·
          refine ⟨14480379086617117034502913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77228688461957957517348869 14480379086617117034502913)
          ·
            refine ⟨10860284314962837775877185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14480379086617117034502913 10860284314962837775877185)
            ·
              refine ⟨8145213236222128331907889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10860284314962837775877185 8145213236222128331907889)
              ·
                refine ⟨6108909927166596248930917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8145213236222128331907889 6108909927166596248930917)
                ·
                  refine ⟨1145420611343736796674547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6108909927166596248930917 1145420611343736796674547)
                  ·
                    refine ⟨1718130917015605195011821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1145420611343736796674547 1718130917015605195011821)
                    ·
                      refine ⟨644299093880851948129433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1718130917015605195011821 644299093880851948129433)
                      ·
                        rfl

theorem cell23_1254768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 1, 3].length) (baseStart_1254768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254768 prefixEnd_1254768 := by exact prefixLift 1254768
  have htrace : WordTrace (prefixWord ++ tailWord_1254768) baseStart_1254768 baseEnd_1254768 := by
    simpa [prefixWord, tailWord_1254768, baseEnd_1254768] using wordTrace_append hprefix tailTrace_1254768
  have hstable : (prefixWord ++ tailWord_1254768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254768).length < 2 ^ (prefixWord ++ tailWord_1254768).sum := by decide
  have hdescent : baseEnd_1254768 < baseStart_1254768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254786 : List Nat := [3, 4, 2, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_1254786 : Nat := 118140960795 + 1254786 * 2 ^ 59
def prefixEnd_1254786 : Nat := 4983230072969 + 3 ^ 40 * 1254786 * 2
def baseEnd_1254786 : Nat := 644308336532632877704351

theorem tailTrace_1254786 : CollatzResearch.WordTrace tailWord_1254786 prefixEnd_1254786 644308336532632877704351 := by
  unfold tailWord_1254786
  simp only [CollatzResearch.WordTrace]
  refine ⟨11441451308033024308146053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30510536821421398155056141 11441451308033024308146053)
  ·
    refine ⟨2145272120256192057777385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11441451308033024308146053 2145272120256192057777385)
    ·
      refine ⟨1608954090192144043333039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2145272120256192057777385 1608954090192144043333039)
      ·
        refine ⟨2413431135288216064999559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1608954090192144043333039 2413431135288216064999559)
        ·
          refine ⟨3620146702932324097499339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413431135288216064999559 3620146702932324097499339)
          ·
            refine ⟨5430220054398486146249009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620146702932324097499339 5430220054398486146249009)
            ·
              refine ⟨4072665040798864609686757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5430220054398486146249009 4072665040798864609686757)
              ·
                refine ⟨763624695149787114316267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4072665040798864609686757 763624695149787114316267)
                ·
                  refine ⟨1145437042724680671474401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763624695149787114316267 1145437042724680671474401)
                  ·
                    refine ⟨859077782043510503605801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1145437042724680671474401 859077782043510503605801)
                    ·
                      refine ⟨644308336532632877704351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859077782043510503605801 644308336532632877704351)
                      ·
                        rfl

theorem cell23_1254786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_1254786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254786 prefixEnd_1254786 := by exact prefixLift 1254786
  have htrace : WordTrace (prefixWord ++ tailWord_1254786) baseStart_1254786 baseEnd_1254786 := by
    simpa [prefixWord, tailWord_1254786, baseEnd_1254786] using wordTrace_append hprefix tailTrace_1254786
  have hstable : (prefixWord ++ tailWord_1254786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254786).length < 2 ^ (prefixWord ++ tailWord_1254786).sum := by decide
  have hdescent : baseEnd_1254786 < baseStart_1254786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254821 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_1254821 : Nat := 118140960795 + 1254821 * 2 ^ 59
def prefixEnd_1254821 : Nat := 4983230072969 + 3 ^ 40 * 1254821 * 2
def baseEnd_1254821 : Nat := 644326308355540240766689

theorem tailTrace_1254821 : CollatzResearch.WordTrace tailWord_1254821 prefixEnd_1254821 644326308355540240766689 := by
  unfold tailWord_1254821
  simp only [CollatzResearch.WordTrace]
  refine ⟨45767081787005298210108317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30511387858003532140072211 45767081787005298210108317)
  ·
    refine ⟨17162655670126986828790619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45767081787005298210108317 17162655670126986828790619)
    ·
      refine ⟨25743983505190480243185929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17162655670126986828790619 25743983505190480243185929)
      ·
        refine ⟨19307987628892860182389447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25743983505190480243185929 19307987628892860182389447)
        ·
          refine ⟨28961981443339290273584171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19307987628892860182389447 28961981443339290273584171)
          ·
            refine ⟨43442972165008935410376257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28961981443339290273584171 43442972165008935410376257)
            ·
              refine ⟨32582229123756701557782193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43442972165008935410376257 32582229123756701557782193)
              ·
                refine ⟨24436671842817526168336645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32582229123756701557782193 24436671842817526168336645)
                ·
                  refine ⟨4581875970528286156563121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24436671842817526168336645 4581875970528286156563121)
                  ·
                    refine ⟨3436406977896214617422341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4581875970528286156563121 3436406977896214617422341)
                    ·
                      refine ⟨644326308355540240766689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3436406977896214617422341 644326308355540240766689)
                      ·
                        rfl

theorem cell23_1254821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_1254821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254821 prefixEnd_1254821 := by exact prefixLift 1254821
  have htrace : WordTrace (prefixWord ++ tailWord_1254821) baseStart_1254821 baseEnd_1254821 := by
    simpa [prefixWord, tailWord_1254821, baseEnd_1254821] using wordTrace_append hprefix tailTrace_1254821
  have hstable : (prefixWord ++ tailWord_1254821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254821).length < 2 ^ (prefixWord ++ tailWord_1254821).sum := by decide
  have hdescent : baseEnd_1254821 < baseStart_1254821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254848 : List Nat := [2, 1, 1, 2, 3, 1, 2, 6, 5]
def baseStart_1254848 : Nat := 118140960795 + 1254848 * 2 ^ 59
def prefixEnd_1254848 : Nat := 4983230072969 + 3 ^ 40 * 1254848 * 2
def baseEnd_1254848 : Nat := 71593352481467959458785

theorem tailTrace_1254848 : CollatzResearch.WordTrace tailWord_1254848 prefixEnd_1254848 71593352481467959458785 := by
  unfold tailWord_1254848
  simp only [CollatzResearch.WordTrace]
  refine ⟨22884033278953740910670599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30512044371938321214227465 22884033278953740910670599)
  ·
    refine ⟨34326049918430611366005899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22884033278953740910670599 34326049918430611366005899)
    ·
      refine ⟨51489074877645917049008849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34326049918430611366005899 51489074877645917049008849)
      ·
        refine ⟨38616806158234437786756637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51489074877645917049008849 38616806158234437786756637)
        ·
          refine ⟨14481302309337914170033739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38616806158234437786756637 14481302309337914170033739)
          ·
            refine ⟨21721953464006871255050609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14481302309337914170033739 21721953464006871255050609)
            ·
              refine ⟨16291465098005153441287957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21721953464006871255050609 16291465098005153441287957)
              ·
                refine ⟨763662426468991567560373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16291465098005153441287957 763662426468991567560373)
                ·
                  refine ⟨71593352481467959458785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 763662426468991567560373 71593352481467959458785)
                  ·
                    rfl

theorem cell23_1254848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 5].length) (baseStart_1254848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254848 prefixEnd_1254848 := by exact prefixLift 1254848
  have htrace : WordTrace (prefixWord ++ tailWord_1254848) baseStart_1254848 baseEnd_1254848 := by
    simpa [prefixWord, tailWord_1254848, baseEnd_1254848] using wordTrace_append hprefix tailTrace_1254848
  have hstable : (prefixWord ++ tailWord_1254848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254848).length < 2 ^ (prefixWord ++ tailWord_1254848).sum := by decide
  have hdescent : baseEnd_1254848 < baseStart_1254848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254911 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_1254911 : Nat := 118140960795 + 1254911 * 2 ^ 59
def prefixEnd_1254911 : Nat := 4983230072969 + 3 ^ 40 * 1254911 * 2
def baseEnd_1254911 : Nat := 644372521614444888641275

theorem tailTrace_1254911 : CollatzResearch.WordTrace tailWord_1254911 prefixEnd_1254911 644372521614444888641275 := by
  unfold tailWord_1254911
  simp only [CollatzResearch.WordTrace]
  refine ⟨45770364356679243580884587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30513576237786162387256391 45770364356679243580884587)
  ·
    refine ⟨68655546535018865371326881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45770364356679243580884587 68655546535018865371326881)
    ·
      refine ⟨51491659901264149028495161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68655546535018865371326881 51491659901264149028495161)
      ·
        refine ⟨38618744925948111771371371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51491659901264149028495161 38618744925948111771371371)
        ·
          refine ⟨57928117388922167657057057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38618744925948111771371371 57928117388922167657057057)
          ·
            refine ⟨43446088041691625742792793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57928117388922167657057057 43446088041691625742792793)
            ·
              refine ⟨32584566031268719307094595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43446088041691625742792793 32584566031268719307094595)
              ·
                refine ⟨48876849046903078960641893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32584566031268719307094595 48876849046903078960641893)
                ·
                  refine ⟨9164409196294327305120355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48876849046903078960641893 9164409196294327305120355)
                  ·
                    refine ⟨13746613794441490957680533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9164409196294327305120355 13746613794441490957680533)
                    ·
                      refine ⟨644372521614444888641275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13746613794441490957680533 644372521614444888641275)
                      ·
                        rfl

theorem cell23_1254911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_1254911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254911 prefixEnd_1254911 := by exact prefixLift 1254911
  have htrace : WordTrace (prefixWord ++ tailWord_1254911) baseStart_1254911 baseEnd_1254911 := by
    simpa [prefixWord, tailWord_1254911, baseEnd_1254911] using wordTrace_append hprefix tailTrace_1254911
  have hstable : (prefixWord ++ tailWord_1254911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254911).length < 2 ^ (prefixWord ++ tailWord_1254911).sum := by decide
  have hdescent : baseEnd_1254911 < baseStart_1254911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254932 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1254932 : Nat := 118140960795 + 1254932 * 2 ^ 59
def prefixEnd_1254932 : Nat := 4983230072969 + 3 ^ 40 * 1254932 * 2
def baseEnd_1254932 : Nat := 644383304708189306478679

theorem tailTrace_1254932 : CollatzResearch.WordTrace tailWord_1254932 prefixEnd_1254932 644383304708189306478679 := by
  unfold tailWord_1254932
  simp only [CollatzResearch.WordTrace]
  refine ⟨22885565144801582083699525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30514086859735442778266033 22885565144801582083699525)
  ·
    refine ⟨4291043464650296640693661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22885565144801582083699525 4291043464650296640693661)
    ·
      refine ⟨1609141299243861240260123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4291043464650296640693661 1609141299243861240260123)
      ·
        refine ⟨2413711948865791860390185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609141299243861240260123 2413711948865791860390185)
        ·
          refine ⟨1810283961649343895292639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2413711948865791860390185 1810283961649343895292639)
          ·
            refine ⟨2715425942474015842938959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810283961649343895292639 2715425942474015842938959)
            ·
              refine ⟨4073138913711023764408439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715425942474015842938959 4073138913711023764408439)
              ·
                refine ⟨6109708370566535646612659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073138913711023764408439 6109708370566535646612659)
                ·
                  refine ⟨9164562555849803469918989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6109708370566535646612659 9164562555849803469918989)
                  ·
                    refine ⟨3436710958443676301219621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9164562555849803469918989 3436710958443676301219621)
                    ·
                      refine ⟨644383304708189306478679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3436710958443676301219621 644383304708189306478679)
                      ·
                        rfl

theorem cell23_1254932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1254932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254932 prefixEnd_1254932 := by exact prefixLift 1254932
  have htrace : WordTrace (prefixWord ++ tailWord_1254932) baseStart_1254932 baseEnd_1254932 := by
    simpa [prefixWord, tailWord_1254932, baseEnd_1254932] using wordTrace_append hprefix tailTrace_1254932
  have hstable : (prefixWord ++ tailWord_1254932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254932).length < 2 ^ (prefixWord ++ tailWord_1254932).sum := by decide
  have hdescent : baseEnd_1254932 < baseStart_1254932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254972 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 6]
def baseStart_1254972 : Nat := 118140960795 + 1254972 * 2 ^ 59
def prefixEnd_1254972 : Nat := 4983230072969 + 3 ^ 40 * 1254972 * 2
def baseEnd_1254972 : Nat := 71600427103818794442055

theorem tailTrace_1254972 : CollatzResearch.WordTrace tailWord_1254972 prefixEnd_1254972 71600427103818794442055 := by
  unfold tailWord_1254972
  simp only [CollatzResearch.WordTrace]
  refine ⟨22886294604729125499427585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30515059472972167332570113 22886294604729125499427585)
  ·
    refine ⟨17164720953546844124570689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22886294604729125499427585 17164720953546844124570689)
    ·
      refine ⟨12873540715160133093428017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17164720953546844124570689 12873540715160133093428017)
      ·
        refine ⟨9655155536370099820071013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12873540715160133093428017 9655155536370099820071013)
        ·
          refine ⟨1810341663069393716263315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9655155536370099820071013 1810341663069393716263315)
          ·
            refine ⟨2715512494604090574394973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810341663069393716263315 2715512494604090574394973)
            ·
              refine ⟨1018317185476533965398115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2715512494604090574394973 1018317185476533965398115)
              ·
                refine ⟨1527475778214800948097173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018317185476533965398115 1527475778214800948097173)
                ·
                  refine ⟨71600427103818794442055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1527475778214800948097173 71600427103818794442055)
                  ·
                    rfl

theorem cell23_1254972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_1254972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254972 prefixEnd_1254972 := by exact prefixLift 1254972
  have htrace : WordTrace (prefixWord ++ tailWord_1254972) baseStart_1254972 baseEnd_1254972 := by
    simpa [prefixWord, tailWord_1254972, baseEnd_1254972] using wordTrace_append hprefix tailTrace_1254972
  have hstable : (prefixWord ++ tailWord_1254972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254972).length < 2 ^ (prefixWord ++ tailWord_1254972).sum := by decide
  have hdescent : baseEnd_1254972 < baseStart_1254972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254975 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 1, 5, 2]
def baseStart_1254975 : Nat := 118140960795 + 1254975 * 2 ^ 59
def prefixEnd_1254975 : Nat := 4983230072969 + 3 ^ 40 * 1254975 * 2
def baseEnd_1254975 : Nat := 644405384376332638240981

theorem tailTrace_1254975 : CollatzResearch.WordTrace tailWord_1254975 prefixEnd_1254975 644405384376332638240981 := by
  unfold tailWord_1254975
  simp only [CollatzResearch.WordTrace]
  refine ⟨45772698628447382511214379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30515132418964921674142919 45772698628447382511214379)
  ·
    refine ⟨68659047942671073766821569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45772698628447382511214379 68659047942671073766821569)
    ·
      refine ⟨51494285957003305325116177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68659047942671073766821569 51494285957003305325116177)
      ·
        refine ⟨38620714467752478993837133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51494285957003305325116177 38620714467752478993837133)
        ·
          refine ⟨14482767925407179622688925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38620714467752478993837133 14482767925407179622688925)
          ·
            refine ⟨5431037972027692358508347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14482767925407179622688925 5431037972027692358508347)
            ·
              refine ⟨8146556958041538537762521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431037972027692358508347 8146556958041538537762521)
              ·
                refine ⟨6109917718531153903321891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8146556958041538537762521 6109917718531153903321891)
                ·
                  refine ⟨9164876577796730854982837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6109917718531153903321891 9164876577796730854982837)
                  ·
                    refine ⟨859207179168443517654641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9164876577796730854982837 859207179168443517654641)
                    ·
                      refine ⟨644405384376332638240981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859207179168443517654641 644405384376332638240981)
                      ·
                        rfl

theorem cell23_1254975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_1254975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254975 prefixEnd_1254975 := by exact prefixLift 1254975
  have htrace : WordTrace (prefixWord ++ tailWord_1254975) baseStart_1254975 baseEnd_1254975 := by
    simpa [prefixWord, tailWord_1254975, baseEnd_1254975] using wordTrace_append hprefix tailTrace_1254975
  have hstable : (prefixWord ++ tailWord_1254975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254975).length < 2 ^ (prefixWord ++ tailWord_1254975).sum := by decide
  have hdescent : baseEnd_1254975 < baseStart_1254975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254999 : List Nat := [1, 1, 3, 2, 2, 3, 3, 3, 1, 1, 3]
def baseStart_1254999 : Nat := 118140960795 + 1254999 * 2 ^ 59
def prefixEnd_1254999 : Nat := 4983230072969 + 3 ^ 40 * 1254999 * 2
def baseEnd_1254999 : Nat := 644417707912040544340871

theorem tailTrace_1254999 : CollatzResearch.WordTrace tailWord_1254999 prefixEnd_1254999 644417707912040544340871 := by
  unfold tailWord_1254999
  simp only [CollatzResearch.WordTrace]
  refine ⟨45773573980360434610088051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30515715986906956406725367 45773573980360434610088051)
  ·
    refine ⟨68660360970540651915132077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45773573980360434610088051 68660360970540651915132077)
    ·
      refine ⟨25747635363952744468174529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68660360970540651915132077 25747635363952744468174529)
      ·
        refine ⟨19310726522964558351130897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25747635363952744468174529 19310726522964558351130897)
        ·
          refine ⟨14483044892223418763348173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19310726522964558351130897 14483044892223418763348173)
          ·
            refine ⟨5431141834583782036255565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14483044892223418763348173 5431141834583782036255565)
            ·
              refine ⟨2036678187968918263595837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5431141834583782036255565 2036678187968918263595837)
              ·
                refine ⟨763754320488344348848439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036678187968918263595837 763754320488344348848439)
                ·
                  refine ⟨1145631480732516523272659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763754320488344348848439 1145631480732516523272659)
                  ·
                    refine ⟨1718447221098774784908989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1145631480732516523272659 1718447221098774784908989)
                    ·
                      refine ⟨644417707912040544340871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1718447221098774784908989 644417707912040544340871)
                      ·
                        rfl

theorem cell23_1254999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_1254999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254999 prefixEnd_1254999 := by exact prefixLift 1254999
  have htrace : WordTrace (prefixWord ++ tailWord_1254999) baseStart_1254999 baseEnd_1254999 := by
    simpa [prefixWord, tailWord_1254999, baseEnd_1254999] using wordTrace_append hprefix tailTrace_1254999
  have hstable : (prefixWord ++ tailWord_1254999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254999).length < 2 ^ (prefixWord ++ tailWord_1254999).sum := by decide
  have hdescent : baseEnd_1254999 < baseStart_1254999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255015 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 4, 4]
def baseStart_1255015 : Nat := 118140960795 + 1255015 * 2 ^ 59
def prefixEnd_1255015 : Nat := 4983230072969 + 3 ^ 40 * 1255015 * 2
def baseEnd_1255015 : Nat := 214808641200837493913599

theorem tailTrace_1255015 : CollatzResearch.WordTrace tailWord_1255015 prefixEnd_1255015 214808641200837493913599 := by
  unfold tailWord_1255015
  simp only [CollatzResearch.WordTrace]
  refine ⟨45774157548302469342670499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30516105032201646228446999 45774157548302469342670499)
  ·
    refine ⟨68661236322453704014005749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45774157548302469342670499 68661236322453704014005749)
    ·
      refine ⟨6436990905230034751313039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68661236322453704014005749 6436990905230034751313039)
      ·
        refine ⟨9655486357845052126969559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6436990905230034751313039 9655486357845052126969559)
        ·
          refine ⟨14483229536767578190454339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9655486357845052126969559 14483229536767578190454339)
          ·
            refine ⟨21724844305151367285681509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14483229536767578190454339 21724844305151367285681509)
            ·
              refine ⟨4073408307215881366065283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21724844305151367285681509 4073408307215881366065283)
              ·
                refine ⟨6110112460823822049097925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073408307215881366065283 6110112460823822049097925)
                ·
                  refine ⟨1145646086404466634205861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6110112460823822049097925 1145646086404466634205861)
                  ·
                    refine ⟨214808641200837493913599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1145646086404466634205861 214808641200837493913599)
                    ·
                      rfl

theorem cell23_1255015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_1255015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255015 prefixEnd_1255015 := by exact prefixLift 1255015
  have htrace : WordTrace (prefixWord ++ tailWord_1255015) baseStart_1255015 baseEnd_1255015 := by
    simpa [prefixWord, tailWord_1255015, baseEnd_1255015] using wordTrace_append hprefix tailTrace_1255015
  have hstable : (prefixWord ++ tailWord_1255015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255015).length < 2 ^ (prefixWord ++ tailWord_1255015).sum := by decide
  have hdescent : baseEnd_1255015 < baseStart_1255015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255073 : List Nat := [1, 2, 3, 3, 2, 1, 4, 2, 1, 2, 2]
def baseStart_1255073 : Nat := 118140960795 + 1255073 * 2 ^ 59
def prefixEnd_1255073 : Nat := 4983230072969 + 3 ^ 40 * 1255073 * 2
def baseEnd_1255073 : Nat := 644455705480473254815531

theorem tailTrace_1255073 : CollatzResearch.WordTrace tailWord_1255073 prefixEnd_1255073 644455705480473254815531 := by
  unfold tailWord_1255073
  simp only [CollatzResearch.WordTrace]
  refine ⟨45776272982092345248281873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30517515321394896832187915 45776272982092345248281873)
  ·
    refine ⟨34332204736569258936211405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45776272982092345248281873 34332204736569258936211405)
    ·
      refine ⟨12874576776213472101079277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34332204736569258936211405 12874576776213472101079277)
      ·
        refine ⟨4827966291080052037904729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12874576776213472101079277 4827966291080052037904729)
        ·
          refine ⟨3620974718310039028428547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4827966291080052037904729 3620974718310039028428547)
          ·
            refine ⟨5431462077465058542642821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620974718310039028428547 5431462077465058542642821)
            ·
              refine ⟨1018399139524698476745529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5431462077465058542642821 1018399139524698476745529)
              ·
                refine ⟨763799354643523857559147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018399139524698476745529 763799354643523857559147)
                ·
                  refine ⟨1145699031965285786338721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763799354643523857559147 1145699031965285786338721)
                  ·
                    refine ⟨859274273973964339754041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1145699031965285786338721 859274273973964339754041)
                    ·
                      refine ⟨644455705480473254815531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859274273973964339754041 644455705480473254815531)
                      ·
                        rfl

theorem cell23_1255073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_1255073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255073 prefixEnd_1255073 := by exact prefixLift 1255073
  have htrace : WordTrace (prefixWord ++ tailWord_1255073) baseStart_1255073 baseEnd_1255073 := by
    simpa [prefixWord, tailWord_1255073, baseEnd_1255073] using wordTrace_append hprefix tailTrace_1255073
  have hstable : (prefixWord ++ tailWord_1255073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255073).length < 2 ^ (prefixWord ++ tailWord_1255073).sum := by decide
  have hdescent : baseEnd_1255073 < baseStart_1255073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255088 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 1, 8]
def baseStart_1255088 : Nat := 118140960795 + 1255088 * 2 ^ 59
def prefixEnd_1255088 : Nat := 4983230072969 + 3 ^ 40 * 1255088 * 2
def baseEnd_1255088 : Nat := 214821135896763565375987

theorem tailTrace_1255088 : CollatzResearch.WordTrace tailWord_1255088 prefixEnd_1255088 214821135896763565375987 := by
  unfold tailWord_1255088
  simp only [CollatzResearch.WordTrace]
  refine ⟨22888410038519001405038959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30517880051358668540051945 22888410038519001405038959)
  ·
    refine ⟨34332615057778502107558439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22888410038519001405038959 34332615057778502107558439)
    ·
      refine ⟨51498922586667753161337659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34332615057778502107558439 51498922586667753161337659)
      ·
        refine ⟨77248383880001629742006489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51498922586667753161337659 77248383880001629742006489)
        ·
          refine ⟨57936287910001222306504867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77248383880001629742006489 57936287910001222306504867)
          ·
            refine ⟨86904431865001833459757301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57936287910001222306504867 86904431865001833459757301)
            ·
              refine ⟨8147290487343921886852247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86904431865001833459757301 8147290487343921886852247)
              ·
                refine ⟨12220935731015882830278371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8147290487343921886852247 12220935731015882830278371)
                ·
                  refine ⟨18331403596523824245417557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12220935731015882830278371 18331403596523824245417557)
                  ·
                    refine ⟨214821135896763565375987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18331403596523824245417557 214821135896763565375987)
                    ·
                      rfl

theorem cell23_1255088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_1255088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255088 prefixEnd_1255088 := by exact prefixLift 1255088
  have htrace : WordTrace (prefixWord ++ tailWord_1255088) baseStart_1255088 baseEnd_1255088 := by
    simpa [prefixWord, tailWord_1255088, baseEnd_1255088] using wordTrace_append hprefix tailTrace_1255088
  have hstable : (prefixWord ++ tailWord_1255088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255088).length < 2 ^ (prefixWord ++ tailWord_1255088).sum := by decide
  have hdescent : baseEnd_1255088 < baseStart_1255088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255110 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1255110 : Nat := 118140960795 + 1255110 * 2 ^ 59
def prefixEnd_1255110 : Nat := 4983230072969 + 3 ^ 40 * 1255110 * 2
def baseEnd_1255110 : Nat := 644474704264689610052861

theorem tailTrace_1255110 : CollatzResearch.WordTrace tailWord_1255110 prefixEnd_1255110 644474704264689610052861 := by
  unfold tailWord_1255110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430550702592446892730587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30518414988638867044919189 1430550702592446892730587)
  ·
    refine ⟨2145826053888670339095881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430550702592446892730587 2145826053888670339095881)
    ·
      refine ⟨1609369540416502754321911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2145826053888670339095881 1609369540416502754321911)
      ·
        refine ⟨2414054310624754131482867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609369540416502754321911 2414054310624754131482867)
        ·
          refine ⟨3621081465937131197224301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414054310624754131482867 3621081465937131197224301)
          ·
            refine ⟨1357905549726424198959113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3621081465937131197224301 1357905549726424198959113)
            ·
              refine ⟨1018429162294818149219335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357905549726424198959113 1018429162294818149219335)
              ·
                refine ⟨1527643743442227223829003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018429162294818149219335 1527643743442227223829003)
                ·
                  refine ⟨2291465615163340835743505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527643743442227223829003 2291465615163340835743505)
                  ·
                    refine ⟨1718599211372505626807629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2291465615163340835743505 1718599211372505626807629)
                    ·
                      refine ⟨644474704264689610052861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1718599211372505626807629 644474704264689610052861)
                      ·
                        rfl

theorem cell23_1255110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1255110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255110 prefixEnd_1255110 := by exact prefixLift 1255110
  have htrace : WordTrace (prefixWord ++ tailWord_1255110) baseStart_1255110 baseEnd_1255110 := by
    simpa [prefixWord, tailWord_1255110, baseEnd_1255110] using wordTrace_append hprefix tailTrace_1255110
  have hstable : (prefixWord ++ tailWord_1255110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255110).length < 2 ^ (prefixWord ++ tailWord_1255110).sum := by decide
  have hdescent : baseEnd_1255110 < baseStart_1255110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255112 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_1255112 : Nat := 118140960795 + 1255112 * 2 ^ 59
def prefixEnd_1255112 : Nat := 4983230072969 + 3 ^ 40 * 1255112 * 2
def baseEnd_1255112 : Nat := 644475731225998602227851

theorem tailTrace_1255112 : CollatzResearch.WordTrace tailWord_1255112 prefixEnd_1255112 644475731225998602227851 := by
  unfold tailWord_1255112
  simp only [CollatzResearch.WordTrace]
  refine ⟨22888847714475527454475795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30518463619300703272634393 22888847714475527454475795)
  ·
    refine ⟨34333271571713291181713693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22888847714475527454475795 34333271571713291181713693)
    ·
      refine ⟨12874976839392484193142635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34333271571713291181713693 12874976839392484193142635)
      ·
        refine ⟨19312465259088726289713953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12874976839392484193142635 19312465259088726289713953)
        ·
          refine ⟨14484348944316544717285465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19312465259088726289713953 14484348944316544717285465)
          ·
            refine ⟨10863261708237408537964099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14484348944316544717285465 10863261708237408537964099)
            ·
              refine ⟨16294892562356112806946149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10863261708237408537964099 16294892562356112806946149)
              ·
                refine ⟨3055292355441771151302403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16294892562356112806946149 3055292355441771151302403)
                ·
                  refine ⟨4582938533162656726953605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055292355441771151302403 4582938533162656726953605)
                  ·
                    refine ⟨859300974967998136303801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4582938533162656726953605 859300974967998136303801)
                    ·
                      refine ⟨644475731225998602227851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859300974967998136303801 644475731225998602227851)
                      ·
                        rfl

theorem cell23_1255112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_1255112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255112 prefixEnd_1255112 := by exact prefixLift 1255112
  have htrace : WordTrace (prefixWord ++ tailWord_1255112) baseStart_1255112 baseEnd_1255112 := by
    simpa [prefixWord, tailWord_1255112, baseEnd_1255112] using wordTrace_append hprefix tailTrace_1255112
  have hstable : (prefixWord ++ tailWord_1255112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255112).length < 2 ^ (prefixWord ++ tailWord_1255112).sum := by decide
  have hdescent : baseEnd_1255112 < baseStart_1255112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255116 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1255116 : Nat := 118140960795 + 1255116 * 2 ^ 59
def prefixEnd_1255116 : Nat := 4983230072969 + 3 ^ 40 * 1255116 * 2
def baseEnd_1255116 : Nat := 644477785148616586577833

theorem tailTrace_1255116 : CollatzResearch.WordTrace tailWord_1255116 prefixEnd_1255116 644477785148616586577833 := by
  unfold tailWord_1255116
  simp only [CollatzResearch.WordTrace]
  refine ⟨22888920660468281796048601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30518560880624375728064801 22888920660468281796048601)
  ·
    refine ⟨17166690495351211347036451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22888920660468281796048601 17166690495351211347036451)
    ·
      refine ⟨25750035743026817020554677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17166690495351211347036451 25750035743026817020554677)
      ·
        refine ⟨2414065850908764095677001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25750035743026817020554677 2414065850908764095677001)
        ·
          refine ⟨1810549388181573071757751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2414065850908764095677001 1810549388181573071757751)
          ·
            refine ⟨2715824082272359607636627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810549388181573071757751 2715824082272359607636627)
            ·
              refine ⟨4073736123408539411454941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715824082272359607636627 4073736123408539411454941)
              ·
                refine ⟨1527651046278202279295603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4073736123408539411454941 1527651046278202279295603)
                ·
                  refine ⟨2291476569417303418943405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527651046278202279295603 2291476569417303418943405)
                  ·
                    refine ⟨859303713531488782103777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291476569417303418943405 859303713531488782103777)
                    ·
                      refine ⟨644477785148616586577833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859303713531488782103777 644477785148616586577833)
                      ·
                        rfl

theorem cell23_1255116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1255116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255116 prefixEnd_1255116 := by exact prefixLift 1255116
  have htrace : WordTrace (prefixWord ++ tailWord_1255116) baseStart_1255116 baseEnd_1255116 := by
    simpa [prefixWord, tailWord_1255116, baseEnd_1255116] using wordTrace_append hprefix tailTrace_1255116
  have hstable : (prefixWord ++ tailWord_1255116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255116).length < 2 ^ (prefixWord ++ tailWord_1255116).sum := by decide
  have hdescent : baseEnd_1255116 < baseStart_1255116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255129 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 4, 2, 2]
def baseStart_1255129 : Nat := 118140960795 + 1255129 * 2 ^ 59
def prefixEnd_1255129 : Nat := 4983230072969 + 3 ^ 40 * 1255129 * 2
def baseEnd_1255129 : Nat := 644484460397125035715273

theorem tailTrace_1255129 : CollatzResearch.WordTrace tailWord_1255129 prefixEnd_1255129 644484460397125035715273 := by
  unfold tailWord_1255129
  simp only [CollatzResearch.WordTrace]
  refine ⟨45778315469889466812320441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30518876979926311208213627 45778315469889466812320441)
  ·
    refine ⟨34333736602417100109240331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45778315469889466812320441 34333736602417100109240331)
    ·
      refine ⟨51500604903625650163860497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34333736602417100109240331 51500604903625650163860497)
      ·
        refine ⟨38625453677719237622895373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51500604903625650163860497 38625453677719237622895373)
        ·
          refine ⟨14484545129144714108585765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38625453677719237622895373 14484545129144714108585765)
          ·
            refine ⟨2715852211714633895359831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14484545129144714108585765 2715852211714633895359831)
            ·
              refine ⟨4073778317571950843039747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715852211714633895359831 4073778317571950843039747)
              ·
                refine ⟨6110667476357926264559621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073778317571950843039747 6110667476357926264559621)
                ·
                  refine ⟨1145750151817111174604929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6110667476357926264559621 1145750151817111174604929)
                  ·
                    refine ⟨859312613862833380953697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1145750151817111174604929 859312613862833380953697)
                    ·
                      refine ⟨644484460397125035715273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859312613862833380953697 644484460397125035715273)
                      ·
                        rfl

theorem cell23_1255129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_1255129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255129 prefixEnd_1255129 := by exact prefixLift 1255129
  have htrace : WordTrace (prefixWord ++ tailWord_1255129) baseStart_1255129 baseEnd_1255129 := by
    simpa [prefixWord, tailWord_1255129, baseEnd_1255129] using wordTrace_append hprefix tailTrace_1255129
  have hstable : (prefixWord ++ tailWord_1255129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255129).length < 2 ^ (prefixWord ++ tailWord_1255129).sum := by decide
  have hdescent : baseEnd_1255129 < baseStart_1255129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255135 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 7]
def baseStart_1255135 : Nat := 118140960795 + 1255135 * 2 ^ 59
def prefixEnd_1255135 : Nat := 4983230072969 + 3 ^ 40 * 1255135 * 2
def baseEnd_1255135 : Nat := 71609726809005779137805

theorem tailTrace_1255135 : CollatzResearch.WordTrace tailWord_1255135 prefixEnd_1255135 71609726809005779137805 := by
  unfold tailWord_1255135
  simp only [CollatzResearch.WordTrace]
  refine ⟨45778534307867729837038859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30519022871911819891359239 45778534307867729837038859)
  ·
    refine ⟨68667801461801594755558289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45778534307867729837038859 68667801461801594755558289)
    ·
      refine ⟨51500851096351196066668717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68667801461801594755558289 51500851096351196066668717)
      ·
        refine ⟨19312819161131698525000769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51500851096351196066668717 19312819161131698525000769)
        ·
          refine ⟨14484614370848773893750577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19312819161131698525000769 14484614370848773893750577)
          ·
            refine ⟨10863460778136580420312933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14484614370848773893750577 10863460778136580420312933)
            ·
              refine ⟨2036898895900608828808675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10863460778136580420312933 2036898895900608828808675)
              ·
                refine ⟨3055348343850913243213013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036898895900608828808675 3055348343850913243213013)
                ·
                  refine ⟨71609726809005779137805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3055348343850913243213013 71609726809005779137805)
                  ·
                    rfl

theorem cell23_1255135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 7].length) (baseStart_1255135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255135 prefixEnd_1255135 := by exact prefixLift 1255135
  have htrace : WordTrace (prefixWord ++ tailWord_1255135) baseStart_1255135 baseEnd_1255135 := by
    simpa [prefixWord, tailWord_1255135, baseEnd_1255135] using wordTrace_append hprefix tailTrace_1255135
  have hstable : (prefixWord ++ tailWord_1255135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255135).length < 2 ^ (prefixWord ++ tailWord_1255135).sum := by decide
  have hdescent : baseEnd_1255135 < baseStart_1255135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255202 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1255202 : Nat := 118140960795 + 1255202 * 2 ^ 59
def prefixEnd_1255202 : Nat := 4983230072969 + 3 ^ 40 * 1255202 * 2
def baseEnd_1255202 : Nat := 644521944484903250102437

theorem tailTrace_1255202 : CollatzResearch.WordTrace tailWord_1255202 prefixEnd_1255202 644521944484903250102437 := by
  unfold tailWord_1255202
  simp only [CollatzResearch.WordTrace]
  refine ⟨11445244499656250069931965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30520651999083333519818573 11445244499656250069931965)
  ·
    refine ⟨4291966687371093776224487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11445244499656250069931965 4291966687371093776224487)
    ·
      refine ⟨6437950031056640664336731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4291966687371093776224487 6437950031056640664336731)
      ·
        refine ⟨9656925046584960996505097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6437950031056640664336731 9656925046584960996505097)
        ·
          refine ⟨7242693784938720747378823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9656925046584960996505097 7242693784938720747378823)
          ·
            refine ⟨10864040677408081121068235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7242693784938720747378823 10864040677408081121068235)
            ·
              refine ⟨16296061016112121681602353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10864040677408081121068235 16296061016112121681602353)
              ·
                refine ⟨12222045762084091261201765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16296061016112121681602353 12222045762084091261201765)
                ·
                  refine ⟨2291633580390767111475331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12222045762084091261201765 2291633580390767111475331)
                  ·
                    refine ⟨3437450370586150667212997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2291633580390767111475331 3437450370586150667212997)
                    ·
                      refine ⟨644521944484903250102437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3437450370586150667212997 644521944484903250102437)
                      ·
                        rfl

theorem cell23_1255202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1255202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255202 prefixEnd_1255202 := by exact prefixLift 1255202
  have htrace : WordTrace (prefixWord ++ tailWord_1255202) baseStart_1255202 baseEnd_1255202 := by
    simpa [prefixWord, tailWord_1255202, baseEnd_1255202] using wordTrace_append hprefix tailTrace_1255202
  have hstable : (prefixWord ++ tailWord_1255202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255202).length < 2 ^ (prefixWord ++ tailWord_1255202).sum := by decide
  have hdescent : baseEnd_1255202 < baseStart_1255202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255219 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 4]
def baseStart_1255219 : Nat := 118140960795 + 1255219 * 2 ^ 59
def prefixEnd_1255219 : Nat := 4983230072969 + 3 ^ 40 * 1255219 * 2
def baseEnd_1255219 : Nat := 644530673656029683589859

theorem tailTrace_1255219 : CollatzResearch.WordTrace tailWord_1255219 prefixEnd_1255219 644530673656029683589859 := by
  unfold tailWord_1255219
  simp only [CollatzResearch.WordTrace]
  refine ⟨45781598039563412183096711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30521065359708941455397807 45781598039563412183096711)
  ·
    refine ⟨68672397059345118274645067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45781598039563412183096711 68672397059345118274645067)
    ·
      refine ⟨103008595589017677411967601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68672397059345118274645067 103008595589017677411967601)
      ·
        refine ⟨77256446691763258058975701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103008595589017677411967601 77256446691763258058975701)
        ·
          refine ⟨1810697969338201360757243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 77256446691763258058975701 1810697969338201360757243)
          ·
            refine ⟨2716046954007302041135865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810697969338201360757243 2716046954007302041135865)
            ·
              refine ⟨2037035215505476530851899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2716046954007302041135865 2037035215505476530851899)
              ·
                refine ⟨3055552823258214796277849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037035215505476530851899 3055552823258214796277849)
                ·
                  refine ⟨2291664617443661097208387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3055552823258214796277849 2291664617443661097208387)
                  ·
                    refine ⟨3437496926165491645812581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2291664617443661097208387 3437496926165491645812581)
                    ·
                      refine ⟨644530673656029683589859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3437496926165491645812581 644530673656029683589859)
                      ·
                        rfl

theorem cell23_1255219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_1255219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255219 prefixEnd_1255219 := by exact prefixLift 1255219
  have htrace : WordTrace (prefixWord ++ tailWord_1255219) baseStart_1255219 baseEnd_1255219 := by
    simpa [prefixWord, tailWord_1255219, baseEnd_1255219] using wordTrace_append hprefix tailTrace_1255219
  have hstable : (prefixWord ++ tailWord_1255219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255219).length < 2 ^ (prefixWord ++ tailWord_1255219).sum := by decide
  have hdescent : baseEnd_1255219 < baseStart_1255219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255242 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 6]
def baseStart_1255242 : Nat := 118140960795 + 1255242 * 2 ^ 59
def prefixEnd_1255242 : Nat := 4983230072969 + 3 ^ 40 * 1255242 * 2
def baseEnd_1255242 : Nat := 71615831523453677066917

theorem tailTrace_1255242 : CollatzResearch.WordTrace tailWord_1255242 prefixEnd_1255242 71615831523453677066917 := by
  unfold tailWord_1255242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11445609229620021777795995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30521624612320058074122653 11445609229620021777795995)
  ·
    refine ⟨17168413844430032666693993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11445609229620021777795995 17168413844430032666693993)
    ·
      refine ⟨12876310383322524500020495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17168413844430032666693993 12876310383322524500020495)
      ·
        refine ⟨19314465574983786750030743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12876310383322524500020495 19314465574983786750030743)
        ·
          refine ⟨28971698362475680125046115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19314465574983786750030743 28971698362475680125046115)
          ·
            refine ⟨43457547543713520187569173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28971698362475680125046115 43457547543713520187569173)
            ·
              refine ⟨2037072541111571258792305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43457547543713520187569173 2037072541111571258792305)
              ·
                refine ⟨1527804405833678444094229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037072541111571258792305 1527804405833678444094229)
                ·
                  refine ⟨71615831523453677066917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1527804405833678444094229 71615831523453677066917)
                  ·
                    rfl

theorem cell23_1255242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_1255242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255242 prefixEnd_1255242 := by exact prefixLift 1255242
  have htrace : WordTrace (prefixWord ++ tailWord_1255242) baseStart_1255242 baseEnd_1255242 := by
    simpa [prefixWord, tailWord_1255242, baseEnd_1255242] using wordTrace_append hprefix tailTrace_1255242
  have hstable : (prefixWord ++ tailWord_1255242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255242).length < 2 ^ (prefixWord ++ tailWord_1255242).sum := by decide
  have hdescent : baseEnd_1255242 < baseStart_1255242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255265 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_1255265 : Nat := 118140960795 + 1255265 * 2 ^ 59
def prefixEnd_1255265 : Nat := 4983230072969 + 3 ^ 40 * 1255265 * 2
def baseEnd_1255265 : Nat := 644554293766136503614647

theorem tailTrace_1255265 : CollatzResearch.WordTrace tailWord_1255265 prefixEnd_1255265 644554293766136503614647 := by
  unfold tailWord_1255265
  simp only [CollatzResearch.WordTrace]
  refine ⟨45783275797396762039271249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30522183864931174692847499 45783275797396762039271249)
  ·
    refine ⟨34337456848047571529453437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45783275797396762039271249 34337456848047571529453437)
    ·
      refine ⟨12876546318017839323545039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34337456848047571529453437 12876546318017839323545039)
      ·
        refine ⟨19314819477026758985317559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12876546318017839323545039 19314819477026758985317559)
        ·
          refine ⟨28972229215540138477976339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19314819477026758985317559 28972229215540138477976339)
          ·
            refine ⟨43458343823310207716964509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28972229215540138477976339 43458343823310207716964509)
            ·
              refine ⟨16296878933741327893861691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43458343823310207716964509 16296878933741327893861691)
              ·
                refine ⟨24445318400611991840792537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16296878933741327893861691 24445318400611991840792537)
                ·
                  refine ⟨18333988800458993880594403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24445318400611991840792537 18333988800458993880594403)
                  ·
                    refine ⟨27500983200688490820891605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18333988800458993880594403 27500983200688490820891605)
                    ·
                      refine ⟨644554293766136503614647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27500983200688490820891605 644554293766136503614647)
                      ·
                        rfl

theorem cell23_1255265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_1255265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255265 prefixEnd_1255265 := by exact prefixLift 1255265
  have htrace : WordTrace (prefixWord ++ tailWord_1255265) baseStart_1255265 baseEnd_1255265 := by
    simpa [prefixWord, tailWord_1255265, baseEnd_1255265] using wordTrace_append hprefix tailTrace_1255265
  have hstable : (prefixWord ++ tailWord_1255265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255265).length < 2 ^ (prefixWord ++ tailWord_1255265).sum := by decide
  have hdescent : baseEnd_1255265 < baseStart_1255265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255272 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1255272 : Nat := 118140960795 + 1255272 * 2 ^ 59
def prefixEnd_1255272 : Nat := 4983230072969 + 3 ^ 40 * 1255272 * 2
def baseEnd_1255272 : Nat := 214852629376905992075705

theorem tailTrace_1255272 : CollatzResearch.WordTrace tailWord_1255272 prefixEnd_1255272 214852629376905992075705 := by
  unfold tailWord_1255272
  simp only [CollatzResearch.WordTrace]
  refine ⟨22891765554185701117388035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30522354072247601489850713 22891765554185701117388035)
  ·
    refine ⟨34337648331278551676082053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22891765554185701117388035 34337648331278551676082053)
    ·
      refine ⟨6438309062114728439265385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34337648331278551676082053 6438309062114728439265385)
      ·
        refine ⟨4828731796586046329449039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6438309062114728439265385 4828731796586046329449039)
        ·
          refine ⟨7243097694879069494173559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4828731796586046329449039 7243097694879069494173559)
          ·
            refine ⟨10864646542318604241260339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7243097694879069494173559 10864646542318604241260339)
            ·
              refine ⟨16296969813477906361890509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10864646542318604241260339 16296969813477906361890509)
              ·
                refine ⟨6111363680054214885708941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16296969813477906361890509 6111363680054214885708941)
                ·
                  refine ⟨2291761380020330582140853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6111363680054214885708941 2291761380020330582140853)
                  ·
                    refine ⟨214852629376905992075705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2291761380020330582140853 214852629376905992075705)
                    ·
                      rfl

theorem cell23_1255272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1255272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255272 prefixEnd_1255272 := by exact prefixLift 1255272
  have htrace : WordTrace (prefixWord ++ tailWord_1255272) baseStart_1255272 baseEnd_1255272 := by
    simpa [prefixWord, tailWord_1255272, baseEnd_1255272] using wordTrace_append hprefix tailTrace_1255272
  have hstable : (prefixWord ++ tailWord_1255272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255272).length < 2 ^ (prefixWord ++ tailWord_1255272).sum := by decide
  have hdescent : baseEnd_1255272 < baseStart_1255272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255319 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 1, 6]
def baseStart_1255319 : Nat := 118140960795 + 1255319 * 2 ^ 59
def prefixEnd_1255319 : Nat := 4983230072969 + 3 ^ 40 * 1255319 * 2
def baseEnd_1255319 : Nat := 214860673907159764113133

theorem tailTrace_1255319 : CollatzResearch.WordTrace tailWord_1255319 prefixEnd_1255319 214860673907159764113133 := by
  unfold tailWord_1255319
  simp only [CollatzResearch.WordTrace]
  refine ⟨45785245339201129261737011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30523496892800752841158007 45785245339201129261737011)
  ·
    refine ⟨68677868008801693892605517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45785245339201129261737011 68677868008801693892605517)
    ·
      refine ⟨25754200503300635209727069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68677868008801693892605517 25754200503300635209727069)
      ·
        refine ⟨9657825188737738203647651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25754200503300635209727069 9657825188737738203647651)
        ·
          refine ⟨14486737783106607305471477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9657825188737738203647651 14486737783106607305471477)
          ·
            refine ⟨1358131667166244434887951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14486737783106607305471477 1358131667166244434887951)
            ·
              refine ⟨2037197500749366652331927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358131667166244434887951 2037197500749366652331927)
              ·
                refine ⟨3055796251124049978497891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037197500749366652331927 3055796251124049978497891)
                ·
                  refine ⟨4583694376686074967746837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055796251124049978497891 4583694376686074967746837)
                  ·
                    refine ⟨214860673907159764113133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4583694376686074967746837 214860673907159764113133)
                    ·
                      rfl

theorem cell23_1255319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_1255319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255319 prefixEnd_1255319 := by exact prefixLift 1255319
  have htrace : WordTrace (prefixWord ++ tailWord_1255319) baseStart_1255319 baseEnd_1255319 := by
    simpa [prefixWord, tailWord_1255319, baseEnd_1255319] using wordTrace_append hprefix tailTrace_1255319
  have hstable : (prefixWord ++ tailWord_1255319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255319).length < 2 ^ (prefixWord ++ tailWord_1255319).sum := by decide
  have hdescent : baseEnd_1255319 < baseStart_1255319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255332 : List Nat := [2, 3, 1, 2, 1, 4, 1, 9]
def baseStart_1255332 : Nat := 118140960795 + 1255332 * 2 ^ 59
def prefixEnd_1255332 : Nat := 4983230072969 + 3 ^ 40 * 1255332 * 2
def baseEnd_1255332 : Nat := 23873655443332879313957

theorem tailTrace_1255332 : CollatzResearch.WordTrace tailWord_1255332 prefixEnd_1255332 23873655443332879313957 := by
  unfold tailWord_1255332
  simp only [CollatzResearch.WordTrace]
  refine ⟨22892859744077016240980125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30523812992102688321306833 22892859744077016240980125)
  ·
    refine ⟨8584822404028881090367547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22892859744077016240980125 8584822404028881090367547)
    ·
      refine ⟨12877233606043321635551321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8584822404028881090367547 12877233606043321635551321)
      ·
        refine ⟨9657925204532491226663491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12877233606043321635551321 9657925204532491226663491)
        ·
          refine ⟨14486887806798736839995237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9657925204532491226663491 14486887806798736839995237)
          ·
            refine ⟨2716291463774763157499107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14486887806798736839995237 2716291463774763157499107)
            ·
              refine ⟨4074437195662144736248661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716291463774763157499107 4074437195662144736248661)
              ·
                refine ⟨23873655443332879313957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4074437195662144736248661 23873655443332879313957)
                ·
                  rfl

theorem cell23_1255332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 9].length) (baseStart_1255332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255332 prefixEnd_1255332 := by exact prefixLift 1255332
  have htrace : WordTrace (prefixWord ++ tailWord_1255332) baseStart_1255332 baseEnd_1255332 := by
    simpa [prefixWord, tailWord_1255332, baseEnd_1255332] using wordTrace_append hprefix tailTrace_1255332
  have hstable : (prefixWord ++ tailWord_1255332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255332).length < 2 ^ (prefixWord ++ tailWord_1255332).sum := by decide
  have hdescent : baseEnd_1255332 < baseStart_1255332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255359 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 3]
def baseStart_1255359 : Nat := 118140960795 + 1255359 * 2 ^ 59
def prefixEnd_1255359 : Nat := 4983230072969 + 3 ^ 40 * 1255359 * 2
def baseEnd_1255359 : Nat := 644602560947659135839215

theorem tailTrace_1255359 : CollatzResearch.WordTrace tailWord_1255359 prefixEnd_1255359 644602560947659135839215 := by
  unfold tailWord_1255359
  simp only [CollatzResearch.WordTrace]
  refine ⟨45786704259056216093193131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30524469506037477395462087 45786704259056216093193131)
  ·
    refine ⟨68680056388584324139789697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45786704259056216093193131 68680056388584324139789697)
    ·
      refine ⟨51510042291438243104842273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68680056388584324139789697 51510042291438243104842273)
      ·
        refine ⟨38632531718578682328631705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51510042291438243104842273 38632531718578682328631705)
        ·
          refine ⟨28974398788934011746473779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38632531718578682328631705 28974398788934011746473779)
          ·
            refine ⟨43461598183401017619710669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28974398788934011746473779 43461598183401017619710669)
            ·
              refine ⟨16298099318775381607391501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43461598183401017619710669 16298099318775381607391501)
              ·
                refine ⟨6111787244540768102771813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16298099318775381607391501 6111787244540768102771813)
                ·
                  refine ⟨1145960108351394019269715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6111787244540768102771813 1145960108351394019269715)
                  ·
                    refine ⟨1718940162527091028904573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1145960108351394019269715 1718940162527091028904573)
                    ·
                      refine ⟨644602560947659135839215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1718940162527091028904573 644602560947659135839215)
                      ·
                        rfl

theorem cell23_1255359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_1255359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255359 prefixEnd_1255359 := by exact prefixLift 1255359
  have htrace : WordTrace (prefixWord ++ tailWord_1255359) baseStart_1255359 baseEnd_1255359 := by
    simpa [prefixWord, tailWord_1255359, baseEnd_1255359] using wordTrace_append hprefix tailTrace_1255359
  have hstable : (prefixWord ++ tailWord_1255359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255359).length < 2 ^ (prefixWord ++ tailWord_1255359).sum := by decide
  have hdescent : baseEnd_1255359 < baseStart_1255359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255360 : List Nat := [2, 1, 1, 2, 3, 2, 5, 2, 1, 2, 2]
def baseStart_1255360 : Nat := 118140960795 + 1255360 * 2 ^ 59
def prefixEnd_1255360 : Nat := 4983230072969 + 3 ^ 40 * 1255360 * 2
def baseEnd_1255360 : Nat := 644603074428313631926711

theorem tailTrace_1255360 : CollatzResearch.WordTrace tailWord_1255360 prefixEnd_1255360 644603074428313631926711 := by
  unfold tailWord_1255360
  simp only [CollatzResearch.WordTrace]
  refine ⟨22893370366026296631989767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30524493821368395509319689 22893370366026296631989767)
  ·
    refine ⟨34340055549039444947984651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22893370366026296631989767 34340055549039444947984651)
    ·
      refine ⟨51510083323559167421976977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34340055549039444947984651 51510083323559167421976977)
      ·
        refine ⟨38632562492669375566482733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51510083323559167421976977 38632562492669375566482733)
        ·
          refine ⟨14487210934751015837431025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38632562492669375566482733 14487210934751015837431025)
          ·
            refine ⟨10865408201063261878073269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14487210934751015837431025 10865408201063261878073269)
            ·
              refine ⟨1018632018849680801069369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10865408201063261878073269 1018632018849680801069369)
              ·
                refine ⟨763974014137260600802027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018632018849680801069369 763974014137260600802027)
                ·
                  refine ⟨1145961021205890901203041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763974014137260600802027 1145961021205890901203041)
                  ·
                    refine ⟨859470765904418175902281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1145961021205890901203041 859470765904418175902281)
                    ·
                      refine ⟨644603074428313631926711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859470765904418175902281 644603074428313631926711)
                      ·
                        rfl

theorem cell23_1255360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 2, 2].length) (baseStart_1255360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255360 prefixEnd_1255360 := by exact prefixLift 1255360
  have htrace : WordTrace (prefixWord ++ tailWord_1255360) baseStart_1255360 baseEnd_1255360 := by
    simpa [prefixWord, tailWord_1255360, baseEnd_1255360] using wordTrace_append hprefix tailTrace_1255360
  have hstable : (prefixWord ++ tailWord_1255360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255360).length < 2 ^ (prefixWord ++ tailWord_1255360).sum := by decide
  have hdescent : baseEnd_1255360 < baseStart_1255360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255369 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 5, 3, 2]
def baseStart_1255369 : Nat := 118140960795 + 1255369 * 2 ^ 59
def prefixEnd_1255369 : Nat := 4983230072969 + 3 ^ 40 * 1255369 * 2
def baseEnd_1255369 : Nat := 644607695754204096714169

theorem tailTrace_1255369 : CollatzResearch.WordTrace tailWord_1255369 prefixEnd_1255369 644607695754204096714169 := by
  unfold tailWord_1255369
  simp only [CollatzResearch.WordTrace]
  refine ⟨45787068989019987801057161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30524712659346658534038107 45787068989019987801057161)
  ·
    refine ⟨34340301741764990850792871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45787068989019987801057161 34340301741764990850792871)
    ·
      refine ⟨51510452612647486276189307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34340301741764990850792871 51510452612647486276189307)
      ·
        refine ⟨77265678918971229414283961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51510452612647486276189307 77265678918971229414283961)
        ·
          refine ⟨57949259189228422060712971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77265678918971229414283961 57949259189228422060712971)
          ·
            refine ⟨86923888783842633091069457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57949259189228422060712971 86923888783842633091069457)
            ·
              refine ⟨65192916587881974818302093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86923888783842633091069457 65192916587881974818302093)
              ·
                refine ⟨24447343720455740556863285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65192916587881974818302093 24447343720455740556863285)
                ·
                  refine ⟨2291938473792725677205933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24447343720455740556863285 2291938473792725677205933)
                  ·
                    refine ⟨859476927672272128952225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291938473792725677205933 859476927672272128952225)
                    ·
                      refine ⟨644607695754204096714169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859476927672272128952225 644607695754204096714169)
                      ·
                        rfl

theorem cell23_1255369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 3, 2].length) (baseStart_1255369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255369 prefixEnd_1255369 := by exact prefixLift 1255369
  have htrace : WordTrace (prefixWord ++ tailWord_1255369) baseStart_1255369 baseEnd_1255369 := by
    simpa [prefixWord, tailWord_1255369, baseEnd_1255369] using wordTrace_append hprefix tailTrace_1255369
  have hstable : (prefixWord ++ tailWord_1255369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255369).length < 2 ^ (prefixWord ++ tailWord_1255369).sum := by decide
  have hdescent : baseEnd_1255369 < baseStart_1255369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255416 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 4, 2, 2]
def baseStart_1255416 : Nat := 118140960795 + 1255416 * 2 ^ 59
def prefixEnd_1255416 : Nat := 4983230072969 + 3 ^ 40 * 1255416 * 2
def baseEnd_1255416 : Nat := 644631829344965412826453

theorem tailTrace_1255416 : CollatzResearch.WordTrace tailWord_1255416 prefixEnd_1255416 644631829344965412826453 := by
  unfold tailWord_1255416
  simp only [CollatzResearch.WordTrace]
  refine ⟨22894391609924857414009051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30525855479899809885345401 22894391609924857414009051)
  ·
    refine ⟨34341587414887286121013577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22894391609924857414009051 34341587414887286121013577)
    ·
      refine ⟨25756190561165464590760183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34341587414887286121013577 25756190561165464590760183)
      ·
        refine ⟨38634285841748196886140275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25756190561165464590760183 38634285841748196886140275)
        ·
          refine ⟨57951428762622295329210413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38634285841748196886140275 57951428762622295329210413)
          ·
            refine ⟨21731785785983360748453905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57951428762622295329210413 21731785785983360748453905)
            ·
              refine ⟨16298839339487520561340429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21731785785983360748453905 16298839339487520561340429)
              ·
                refine ⟨6112064752307820210502661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16298839339487520561340429 6112064752307820210502661)
                ·
                  refine ⟨1146012141057716289469249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6112064752307820210502661 1146012141057716289469249)
                  ·
                    refine ⟨859509105793287217101937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1146012141057716289469249 859509105793287217101937)
                    ·
                      refine ⟨644631829344965412826453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859509105793287217101937 644631829344965412826453)
                      ·
                        rfl

theorem cell23_1255416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_1255416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255416 prefixEnd_1255416 := by exact prefixLift 1255416
  have htrace : WordTrace (prefixWord ++ tailWord_1255416) baseStart_1255416 baseEnd_1255416 := by
    simpa [prefixWord, tailWord_1255416, baseEnd_1255416] using wordTrace_append hprefix tailTrace_1255416
  have hstable : (prefixWord ++ tailWord_1255416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255416).length < 2 ^ (prefixWord ++ tailWord_1255416).sum := by decide
  have hdescent : baseEnd_1255416 < baseStart_1255416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255429 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_1255429 : Nat := 118140960795 + 1255429 * 2 ^ 59
def prefixEnd_1255429 : Nat := 4983230072969 + 3 ^ 40 * 1255429 * 2
def baseEnd_1255429 : Nat := 644638504593473861963893

theorem tailTrace_1255429 : CollatzResearch.WordTrace tailWord_1255429 prefixEnd_1255429 644638504593473861963893 := by
  unfold tailWord_1255429
  simp only [CollatzResearch.WordTrace]
  refine ⟨45789257368802618048241341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30526171579201745365494227 45789257368802618048241341)
  ·
    refine ⟨17170971513300981768090503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45789257368802618048241341 17170971513300981768090503)
    ·
      refine ⟨25756457269951472652135755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17170971513300981768090503 25756457269951472652135755)
      ·
        refine ⟨38634685904927208978203633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25756457269951472652135755 38634685904927208978203633)
        ·
          refine ⟨28976014428695406733652725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38634685904927208978203633 28976014428695406733652725)
          ·
            refine ⟨2716501352690194381279943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28976014428695406733652725 2716501352690194381279943)
            ·
              refine ⟨4074752029035291571919915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716501352690194381279943 4074752029035291571919915)
              ·
                refine ⟨6112128043552937357879873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074752029035291571919915 6112128043552937357879873)
                ·
                  refine ⟨4584096032664703018409905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6112128043552937357879873 4584096032664703018409905)
                  ·
                    refine ⟨3438072024498527263807429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4584096032664703018409905 3438072024498527263807429)
                    ·
                      refine ⟨644638504593473861963893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3438072024498527263807429 644638504593473861963893)
                      ·
                        rfl

theorem cell23_1255429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_1255429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255429 prefixEnd_1255429 := by exact prefixLift 1255429
  have htrace : WordTrace (prefixWord ++ tailWord_1255429) baseStart_1255429 baseEnd_1255429 := by
    simpa [prefixWord, tailWord_1255429, baseEnd_1255429] using wordTrace_append hprefix tailTrace_1255429
  have hstable : (prefixWord ++ tailWord_1255429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255429).length < 2 ^ (prefixWord ++ tailWord_1255429).sum := by decide
  have hdescent : baseEnd_1255429 < baseStart_1255429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255466 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1255466 : Nat := 118140960795 + 1255466 * 2 ^ 59
def prefixEnd_1255466 : Nat := 4983230072969 + 3 ^ 40 * 1255466 * 2
def baseEnd_1255466 : Nat := 644657503377690217201223

theorem tailTrace_1255466 : CollatzResearch.WordTrace tailWord_1255466 prefixEnd_1255466 644657503377690217201223 := by
  unfold tailWord_1255466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11447651717417143341834563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30527071246445715578225501 11447651717417143341834563)
  ·
    refine ⟨17171477576125715012751845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11447651717417143341834563 17171477576125715012751845)
    ·
      refine ⟨3219652045523571564890971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17171477576125715012751845 3219652045523571564890971)
      ·
        refine ⟨4829478068285357347336457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219652045523571564890971 4829478068285357347336457)
        ·
          refine ⟨3622108551214018010502343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4829478068285357347336457 3622108551214018010502343)
          ·
            refine ⟨5433162826821027015753515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622108551214018010502343 5433162826821027015753515)
            ·
              refine ⟨8149744240231540523630273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433162826821027015753515 8149744240231540523630273)
              ·
                refine ⟨6112308180173655392722705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8149744240231540523630273 6112308180173655392722705)
                ·
                  refine ⟨4584231135130241544542029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6112308180173655392722705 4584231135130241544542029)
                  ·
                    refine ⟨1719086675673840579203261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4584231135130241544542029 1719086675673840579203261)
                    ·
                      refine ⟨644657503377690217201223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1719086675673840579203261 644657503377690217201223)
                      ·
                        rfl

theorem cell23_1255466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1255466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255466 prefixEnd_1255466 := by exact prefixLift 1255466
  have htrace : WordTrace (prefixWord ++ tailWord_1255466) baseStart_1255466 baseEnd_1255466 := by
    simpa [prefixWord, tailWord_1255466, baseEnd_1255466] using wordTrace_append hprefix tailTrace_1255466
  have hstable : (prefixWord ++ tailWord_1255466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255466).length < 2 ^ (prefixWord ++ tailWord_1255466).sum := by decide
  have hdescent : baseEnd_1255466 < baseStart_1255466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255529 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 6]
def baseStart_1255529 : Nat := 118140960795 + 1255529 * 2 ^ 59
def prefixEnd_1255529 : Nat := 4983230072969 + 3 ^ 40 * 1255529 * 2
def baseEnd_1255529 : Nat := 71632205850991496745937

theorem tailTrace_1255529 : CollatzResearch.WordTrace tailWord_1255529 prefixEnd_1255529 71632205850991496745937 := by
  unfold tailWord_1255529
  simp only [CollatzResearch.WordTrace]
  refine ⟨45792904668440335126881641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30528603112293556751254427 45792904668440335126881641)
  ·
    refine ⟨34344678501330251345161231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45792904668440335126881641 34344678501330251345161231)
    ·
      refine ⟨51517017751995377017741847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34344678501330251345161231 51517017751995377017741847)
      ·
        refine ⟨77275526627993065526612771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51517017751995377017741847 77275526627993065526612771)
        ·
          refine ⟨115913289941989598289919157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77275526627993065526612771 115913289941989598289919157)
          ·
            refine ⟨10866870932061524839679921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115913289941989598289919157 10866870932061524839679921)
            ·
              refine ⟨8150153199046143629759941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10866870932061524839679921 8150153199046143629759941)
              ·
                refine ⟨1528153724821151930579989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8150153199046143629759941 1528153724821151930579989)
                ·
                  refine ⟨71632205850991496745937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1528153724821151930579989 71632205850991496745937)
                  ·
                    rfl

theorem cell23_1255529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 6].length) (baseStart_1255529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255529 prefixEnd_1255529 := by exact prefixLift 1255529
  have htrace : WordTrace (prefixWord ++ tailWord_1255529) baseStart_1255529 baseEnd_1255529 := by
    simpa [prefixWord, tailWord_1255529, baseEnd_1255529] using wordTrace_append hprefix tailTrace_1255529
  have hstable : (prefixWord ++ tailWord_1255529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255529).length < 2 ^ (prefixWord ++ tailWord_1255529).sum := by decide
  have hdescent : baseEnd_1255529 < baseStart_1255529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255589 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_1255589 : Nat := 118140960795 + 1255589 * 2 ^ 59
def prefixEnd_1255589 : Nat := 4983230072969 + 3 ^ 40 * 1255589 * 2
def baseEnd_1255589 : Nat := 214906887166064411987719

theorem tailTrace_1255589 : CollatzResearch.WordTrace tailWord_1255589 prefixEnd_1255589 214906887166064411987719 := by
  unfold tailWord_1255589
  simp only [CollatzResearch.WordTrace]
  refine ⟨45795093048222965374065821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30530062032148643582710547 45795093048222965374065821)
  ·
    refine ⟨17173159893083612015274683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45795093048222965374065821 17173159893083612015274683)
    ·
      refine ⟨25759739839625418022912025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17173159893083612015274683 25759739839625418022912025)
      ·
        refine ⟨19319804879719063517184019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25759739839625418022912025 19319804879719063517184019)
        ·
          refine ⟨28979707319578595275776029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19319804879719063517184019 28979707319578595275776029)
          ·
            refine ⟨10867390244841973228416011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28979707319578595275776029 10867390244841973228416011)
            ·
              refine ⟨16301085367262959842624017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10867390244841973228416011 16301085367262959842624017)
              ·
                refine ⟨12225814025447219881968013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16301085367262959842624017 12225814025447219881968013)
                ·
                  refine ⟨4584680259542707455738005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12225814025447219881968013 4584680259542707455738005)
                  ·
                    refine ⟨214906887166064411987719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4584680259542707455738005 214906887166064411987719)
                    ·
                      rfl

theorem cell23_1255589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_1255589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255589 prefixEnd_1255589 := by exact prefixLift 1255589
  have htrace : WordTrace (prefixWord ++ tailWord_1255589) baseStart_1255589 baseEnd_1255589 := by
    simpa [prefixWord, tailWord_1255589, baseEnd_1255589] using wordTrace_append hprefix tailTrace_1255589
  have hstable : (prefixWord ++ tailWord_1255589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255589).length < 2 ^ (prefixWord ++ tailWord_1255589).sum := by decide
  have hdescent : baseEnd_1255589 < baseStart_1255589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255599 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_1255599 : Nat := 118140960795 + 1255599 * 2 ^ 59
def prefixEnd_1255599 : Nat := 4983230072969 + 3 ^ 40 * 1255599 * 2
def baseEnd_1255599 : Nat := 644725796304738196838111

theorem tailTrace_1255599 : CollatzResearch.WordTrace tailWord_1255599 prefixEnd_1255599 644725796304738196838111 := by
  unfold tailWord_1255599
  simp only [CollatzResearch.WordTrace]
  refine ⟨45795457778186737081929851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30530305185457824721286567 45795457778186737081929851)
  ·
    refine ⟨68693186667280105622894777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45795457778186737081929851 68693186667280105622894777)
    ·
      refine ⟨51519890000460079217171083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68693186667280105622894777 51519890000460079217171083)
      ·
        refine ⟨77279835000690118825756625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51519890000460079217171083 77279835000690118825756625)
        ·
          refine ⟨57959876250517589119317469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77279835000690118825756625 57959876250517589119317469)
          ·
            refine ⟨21734953593944095919744051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57959876250517589119317469 21734953593944095919744051)
            ·
              refine ⟨32602430390916143879616077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21734953593944095919744051 32602430390916143879616077)
              ·
                refine ⟨12225911396593553954856029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32602430390916143879616077 12225911396593553954856029)
                ·
                  refine ⟨4584716773722582733071011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12225911396593553954856029 4584716773722582733071011)
                  ·
                    refine ⟨6877075160583874099606517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4584716773722582733071011 6877075160583874099606517)
                    ·
                      refine ⟨644725796304738196838111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6877075160583874099606517 644725796304738196838111)
                      ·
                        rfl

theorem cell23_1255599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_1255599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255599 prefixEnd_1255599 := by exact prefixLift 1255599
  have htrace : WordTrace (prefixWord ++ tailWord_1255599) baseStart_1255599 baseEnd_1255599 := by
    simpa [prefixWord, tailWord_1255599, baseEnd_1255599] using wordTrace_append hprefix tailTrace_1255599
  have hstable : (prefixWord ++ tailWord_1255599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255599).length < 2 ^ (prefixWord ++ tailWord_1255599).sum := by decide
  have hdescent : baseEnd_1255599 < baseStart_1255599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255626 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1255626 : Nat := 118140960795 + 1255626 * 2 ^ 59
def prefixEnd_1255626 : Nat := 4983230072969 + 3 ^ 40 * 1255626 * 2
def baseEnd_1255626 : Nat := 644739660282409591200487

theorem tailTrace_1255626 : CollatzResearch.WordTrace tailWord_1255626 prefixEnd_1255626 644739660282409591200487 := by
  unfold tailWord_1255626
  simp only [CollatzResearch.WordTrace]
  refine ⟨11449110637272230173290683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30530961699392613795441821 11449110637272230173290683)
  ·
    refine ⟨17173665955908345259936025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11449110637272230173290683 17173665955908345259936025)
    ·
      refine ⟨12880249466931258944952019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17173665955908345259936025 12880249466931258944952019)
      ·
        refine ⟨19320374200396888417428029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12880249466931258944952019 19320374200396888417428029)
        ·
          refine ⟨7245140325148833156535511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19320374200396888417428029 7245140325148833156535511)
          ·
            refine ⟨10867710487723249734803267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7245140325148833156535511 10867710487723249734803267)
            ·
              refine ⟨16301565731584874602204901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10867710487723249734803267 16301565731584874602204901)
              ·
                refine ⟨3056543574672163987913419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16301565731584874602204901 3056543574672163987913419)
                ·
                  refine ⟨4584815362008245981870129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056543574672163987913419 4584815362008245981870129)
                  ·
                    refine ⟨3438611521506184486402597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4584815362008245981870129 3438611521506184486402597)
                    ·
                      refine ⟨644739660282409591200487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3438611521506184486402597 644739660282409591200487)
                      ·
                        rfl

theorem cell23_1255626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1255626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255626 prefixEnd_1255626 := by exact prefixLift 1255626
  have htrace : WordTrace (prefixWord ++ tailWord_1255626) baseStart_1255626 baseEnd_1255626 := by
    simpa [prefixWord, tailWord_1255626, baseEnd_1255626] using wordTrace_append hprefix tailTrace_1255626
  have hstable : (prefixWord ++ tailWord_1255626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255626).length < 2 ^ (prefixWord ++ tailWord_1255626).sum := by decide
  have hdescent : baseEnd_1255626 < baseStart_1255626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255630 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_1255630 : Nat := 118140960795 + 1255630 * 2 ^ 59
def prefixEnd_1255630 : Nat := 4983230072969 + 3 ^ 40 * 1255630 * 2
def baseEnd_1255630 : Nat := 644741714205027575550469

theorem tailTrace_1255630 : CollatzResearch.WordTrace tailWord_1255630 prefixEnd_1255630 644741714205027575550469 := by
  unfold tailWord_1255630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724573555134303672038543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30531058960716286250872229 5724573555134303672038543)
  ·
    refine ⟨8586860332701455508057815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5724573555134303672038543 8586860332701455508057815)
    ·
      refine ⟨12880290499052183262086723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8586860332701455508057815 12880290499052183262086723)
      ·
        refine ⟨19320435748578274893130085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12880290499052183262086723 19320435748578274893130085)
        ·
          refine ⟨3622581702858426542461891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19320435748578274893130085 3622581702858426542461891)
          ·
            refine ⟨5433872554287639813692837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622581702858426542461891 5433872554287639813692837)
            ·
              refine ⟨1018851103928932465067407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5433872554287639813692837 1018851103928932465067407)
              ·
                refine ⟨1528276655893398697601111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018851103928932465067407 1528276655893398697601111)
                ·
                  refine ⟨2292414983840098046401667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528276655893398697601111 2292414983840098046401667)
                  ·
                    refine ⟨3438622475760147069602501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2292414983840098046401667 3438622475760147069602501)
                    ·
                      refine ⟨644741714205027575550469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3438622475760147069602501 644741714205027575550469)
                      ·
                        rfl

theorem cell23_1255630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_1255630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255630 prefixEnd_1255630 := by exact prefixLift 1255630
  have htrace : WordTrace (prefixWord ++ tailWord_1255630) baseStart_1255630 baseEnd_1255630 := by
    simpa [prefixWord, tailWord_1255630, baseEnd_1255630] using wordTrace_append hprefix tailTrace_1255630
  have hstable : (prefixWord ++ tailWord_1255630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255630).length < 2 ^ (prefixWord ++ tailWord_1255630).sum := by decide
  have hdescent : baseEnd_1255630 < baseStart_1255630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255639 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1255639 : Nat := 118140960795 + 1255639 * 2 ^ 59
def prefixEnd_1255639 : Nat := 4983230072969 + 3 ^ 40 * 1255639 * 2
def baseEnd_1255639 : Nat := 644746335530918040337927

theorem tailTrace_1255639 : CollatzResearch.WordTrace tailWord_1255639 prefixEnd_1255639 644746335530918040337927 := by
  unfold tailWord_1255639
  simp only [CollatzResearch.WordTrace]
  refine ⟨45796916698041823913385971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30531277798694549275590647 45796916698041823913385971)
  ·
    refine ⟨68695375047062735870078957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45796916698041823913385971 68695375047062735870078957)
    ·
      refine ⟨25760765642648525951279609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68695375047062735870078957 25760765642648525951279609)
      ·
        refine ⟨19320574231986394463459707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25760765642648525951279609 19320574231986394463459707)
        ·
          refine ⟨28980861347979591695189561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19320574231986394463459707 28980861347979591695189561)
          ·
            refine ⟨21735646010984693771392171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28980861347979591695189561 21735646010984693771392171)
            ·
              refine ⟨32603469016477040657088257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21735646010984693771392171 32603469016477040657088257)
              ·
                refine ⟨24452601762357780492816193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32603469016477040657088257 24452601762357780492816193)
                ·
                  refine ⟨18339451321768335369612145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24452601762357780492816193 18339451321768335369612145)
                  ·
                    refine ⟨13754588491326251527209109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18339451321768335369612145 13754588491326251527209109)
                    ·
                      refine ⟨644746335530918040337927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13754588491326251527209109 644746335530918040337927)
                      ·
                        rfl

theorem cell23_1255639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1255639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255639 prefixEnd_1255639 := by exact prefixLift 1255639
  have htrace : WordTrace (prefixWord ++ tailWord_1255639) baseStart_1255639 baseEnd_1255639 := by
    simpa [prefixWord, tailWord_1255639, baseEnd_1255639] using wordTrace_append hprefix tailTrace_1255639
  have hstable : (prefixWord ++ tailWord_1255639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255639).length < 2 ^ (prefixWord ++ tailWord_1255639).sum := by decide
  have hdescent : baseEnd_1255639 < baseStart_1255639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255640 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 2, 4]
def baseStart_1255640 : Nat := 118140960795 + 1255640 * 2 ^ 59
def prefixEnd_1255640 : Nat := 4983230072969 + 3 ^ 40 * 1255640 * 2
def baseEnd_1255640 : Nat := 214915616337190845475141

theorem tailTrace_1255640 : CollatzResearch.WordTrace tailWord_1255640 prefixEnd_1255640 214915616337190845475141 := by
  unfold tailWord_1255640
  simp only [CollatzResearch.WordTrace]
  refine ⟨22898476585519100542086187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30531302114025467389448249 22898476585519100542086187)
  ·
    refine ⟨34347714878278650813129281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22898476585519100542086187 34347714878278650813129281)
    ·
      refine ⟨25760786158708988109846961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34347714878278650813129281 25760786158708988109846961)
      ·
        refine ⟨19320589619031741082385221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25760786158708988109846961 19320589619031741082385221)
        ·
          refine ⟨3622610553568451452947229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19320589619031741082385221 3622610553568451452947229)
          ·
            refine ⟨1358478957588169294855211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3622610553568451452947229 1358478957588169294855211)
            ·
              refine ⟨2037718436382253942282817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358478957588169294855211 2037718436382253942282817)
              ·
                refine ⟨1528288827286690456712113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037718436382253942282817 1528288827286690456712113)
                ·
                  refine ⟨1146216620465017842534085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1528288827286690456712113 1146216620465017842534085)
                  ·
                    refine ⟨214915616337190845475141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1146216620465017842534085 214915616337190845475141)
                    ·
                      rfl

theorem cell23_1255640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_1255640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255640 prefixEnd_1255640 := by exact prefixLift 1255640
  have htrace : WordTrace (prefixWord ++ tailWord_1255640) baseStart_1255640 baseEnd_1255640 := by
    simpa [prefixWord, tailWord_1255640, baseEnd_1255640] using wordTrace_append hprefix tailTrace_1255640
  have hstable : (prefixWord ++ tailWord_1255640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255640).length < 2 ^ (prefixWord ++ tailWord_1255640).sum := by decide
  have hdescent : baseEnd_1255640 < baseStart_1255640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255663 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 3]
def baseStart_1255663 : Nat := 118140960795 + 1255663 * 2 ^ 59
def prefixEnd_1255663 : Nat := 4983230072969 + 3 ^ 40 * 1255663 * 2
def baseEnd_1255663 : Nat := 644758659066625946437817

theorem tailTrace_1255663 : CollatzResearch.WordTrace tailWord_1255663 prefixEnd_1255663 644758659066625946437817 := by
  unfold tailWord_1255663
  simp only [CollatzResearch.WordTrace]
  refine ⟨45797792049954876012259643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30531861366636584008173095 45797792049954876012259643)
  ·
    refine ⟨68696688074932314018389465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45797792049954876012259643 68696688074932314018389465)
    ·
      refine ⟨51522516056199235513792099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68696688074932314018389465 51522516056199235513792099)
      ·
        refine ⟨77283774084298853270688149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51522516056199235513792099 77283774084298853270688149)
        ·
          refine ⟨3622676910201508747063507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77283774084298853270688149 3622676910201508747063507)
          ·
            refine ⟨5434015365302263120595261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622676910201508747063507 5434015365302263120595261)
            ·
              refine ⟨2037755761988348670223223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5434015365302263120595261 2037755761988348670223223)
              ·
                refine ⟨3056633642982523005334835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037755761988348670223223 3056633642982523005334835)
                ·
                  refine ⟨4584950464473784508002253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056633642982523005334835 4584950464473784508002253)
                  ·
                    refine ⟨1719356424177669190500845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4584950464473784508002253 1719356424177669190500845)
                    ·
                      refine ⟨644758659066625946437817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1719356424177669190500845 644758659066625946437817)
                      ·
                        rfl

theorem cell23_1255663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_1255663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255663 prefixEnd_1255663 := by exact prefixLift 1255663
  have htrace : WordTrace (prefixWord ++ tailWord_1255663) baseStart_1255663 baseEnd_1255663 := by
    simpa [prefixWord, tailWord_1255663, baseEnd_1255663] using wordTrace_append hprefix tailTrace_1255663
  have hstable : (prefixWord ++ tailWord_1255663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255663).length < 2 ^ (prefixWord ++ tailWord_1255663).sum := by decide
  have hdescent : baseEnd_1255663 < baseStart_1255663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255676 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_1255676 : Nat := 118140960795 + 1255676 * 2 ^ 59
def prefixEnd_1255676 : Nat := 4983230072969 + 3 ^ 40 * 1255676 * 2
def baseEnd_1255676 : Nat := 644765334315134395575257

theorem tailTrace_1255676 : CollatzResearch.WordTrace tailWord_1255676 prefixEnd_1255676 644765334315134395575257 := by
  unfold tailWord_1255676
  simp only [CollatzResearch.WordTrace]
  refine ⟨22899133099453889616241441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30532177465938519488321921 22899133099453889616241441)
  ·
    refine ⟨17174349824590417212181081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22899133099453889616241441 17174349824590417212181081)
    ·
      refine ⟨12880762368442812909135811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17174349824590417212181081 12880762368442812909135811)
      ·
        refine ⟨19321143552664219363703717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12880762368442812909135811 19321143552664219363703717)
        ·
          refine ⟨3622714416124541130694447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19321143552664219363703717 3622714416124541130694447)
          ·
            refine ⟨5434071624186811696041671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622714416124541130694447 5434071624186811696041671)
            ·
              refine ⟨8151107436280217544062507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5434071624186811696041671 8151107436280217544062507)
              ·
                refine ⟨12226661154420326316093761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8151107436280217544062507 12226661154420326316093761)
                ·
                  refine ⟨9169995865815244737070321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12226661154420326316093761 9169995865815244737070321)
                  ·
                    refine ⟨6877496899361433552802741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9169995865815244737070321 6877496899361433552802741)
                    ·
                      refine ⟨644765334315134395575257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6877496899361433552802741 644765334315134395575257)
                      ·
                        rfl

theorem cell23_1255676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_1255676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255676 prefixEnd_1255676 := by exact prefixLift 1255676
  have htrace : WordTrace (prefixWord ++ tailWord_1255676) baseStart_1255676 baseEnd_1255676 := by
    simpa [prefixWord, tailWord_1255676, baseEnd_1255676] using wordTrace_append hprefix tailTrace_1255676
  have hstable : (prefixWord ++ tailWord_1255676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255676).length < 2 ^ (prefixWord ++ tailWord_1255676).sum := by decide
  have hdescent : baseEnd_1255676 < baseStart_1255676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255690 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_1255690 : Nat := 118140960795 + 1255690 * 2 ^ 59
def prefixEnd_1255690 : Nat := 4983230072969 + 3 ^ 40 * 1255690 * 2
def baseEnd_1255690 : Nat := 644772523044297340800193

theorem tailTrace_1255690 : CollatzResearch.WordTrace tailWord_1255690 prefixEnd_1255690 644772523044297340800193 := by
  unfold tailWord_1255690
  simp only [CollatzResearch.WordTrace]
  refine ⟨11449694205214264905873131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30532517880571373082328349 11449694205214264905873131)
  ·
    refine ⟨17174541307821397358809697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11449694205214264905873131 17174541307821397358809697)
    ·
      refine ⟨12880905980866048019107273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17174541307821397358809697 12880905980866048019107273)
      ·
        refine ⟨9660679485649536014330455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12880905980866048019107273 9660679485649536014330455)
        ·
          refine ⟨14491019228474304021495683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9660679485649536014330455 14491019228474304021495683)
          ·
            refine ⟨21736528842711456032243525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14491019228474304021495683 21736528842711456032243525)
            ·
              refine ⟨4075599158008398006045661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21736528842711456032243525 4075599158008398006045661)
              ·
                refine ⟨1528349684253149252267123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4075599158008398006045661 1528349684253149252267123)
                ·
                  refine ⟨2292524526379723878400685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528349684253149252267123 2292524526379723878400685)
                  ·
                    refine ⟨859696697392396454400257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2292524526379723878400685 859696697392396454400257)
                    ·
                      refine ⟨644772523044297340800193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859696697392396454400257 644772523044297340800193)
                      ·
                        rfl

theorem cell23_1255690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_1255690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255690 prefixEnd_1255690 := by exact prefixLift 1255690
  have htrace : WordTrace (prefixWord ++ tailWord_1255690) baseStart_1255690 baseEnd_1255690 := by
    simpa [prefixWord, tailWord_1255690, baseEnd_1255690] using wordTrace_append hprefix tailTrace_1255690
  have hstable : (prefixWord ++ tailWord_1255690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255690).length < 2 ^ (prefixWord ++ tailWord_1255690).sum := by decide
  have hdescent : baseEnd_1255690 < baseStart_1255690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255714 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_1255714 : Nat := 118140960795 + 1255714 * 2 ^ 59
def prefixEnd_1255714 : Nat := 4983230072969 + 3 ^ 40 * 1255714 * 2
def baseEnd_1255714 : Nat := 644784846580005246900083

theorem tailTrace_1255714 : CollatzResearch.WordTrace tailWord_1255714 prefixEnd_1255714 644784846580005246900083 := by
  unfold tailWord_1255714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11449913043192527930591549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30533101448513407814910797 11449913043192527930591549)
  ·
    refine ⟨4293717391197197973971831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11449913043192527930591549 4293717391197197973971831)
    ·
      refine ⟨6440576086795796960957747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4293717391197197973971831 6440576086795796960957747)
      ·
        refine ⟨9660864130193695441436621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6440576086795796960957747 9660864130193695441436621)
        ·
          refine ⟨3622824048822635790538733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9660864130193695441436621 3622824048822635790538733)
          ·
            refine ⟨1358559018308488421452025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3622824048822635790538733 1358559018308488421452025)
            ·
              refine ⟨1018919263731366316089019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358559018308488421452025 1018919263731366316089019)
              ·
                refine ⟨1528378895597049474133529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018919263731366316089019 1528378895597049474133529)
                ·
                  refine ⟨1146284171697787105600147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1528378895597049474133529 1146284171697787105600147)
                  ·
                    refine ⟨1719426257546680658400221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1146284171697787105600147 1719426257546680658400221)
                    ·
                      refine ⟨644784846580005246900083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1719426257546680658400221 644784846580005246900083)
                      ·
                        rfl

theorem cell23_1255714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_1255714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255714 prefixEnd_1255714 := by exact prefixLift 1255714
  have htrace : WordTrace (prefixWord ++ tailWord_1255714) baseStart_1255714 baseEnd_1255714 := by
    simpa [prefixWord, tailWord_1255714, baseEnd_1255714] using wordTrace_append hprefix tailTrace_1255714
  have hstable : (prefixWord ++ tailWord_1255714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255714).length < 2 ^ (prefixWord ++ tailWord_1255714).sum := by decide
  have hdescent : baseEnd_1255714 < baseStart_1255714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255743 : List Nat := [1, 1, 2, 2, 4, 1, 2, 5, 5]
def baseStart_1255743 : Nat := 118140960795 + 1255743 * 2 ^ 59
def prefixEnd_1255743 : Nat := 4983230072969 + 3 ^ 40 * 1255743 * 2
def baseEnd_1255743 : Nat := 71644415279887292604161

theorem tailTrace_1255743 : CollatzResearch.WordTrace tailWord_1255743 prefixEnd_1255743 71644415279887292604161 := by
  unfold tailWord_1255743
  simp only [CollatzResearch.WordTrace]
  refine ⟨45800709889665049675171883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30533806593110033116781255 45800709889665049675171883)
  ·
    refine ⟨68701064834497574512757825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45800709889665049675171883 68701064834497574512757825)
    ·
      refine ⟨51525798625873180884568369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68701064834497574512757825 51525798625873180884568369)
      ·
        refine ⟨38644348969404885663426277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51525798625873180884568369 38644348969404885663426277)
        ·
          refine ⟨7245815431763416061892427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38644348969404885663426277 7245815431763416061892427)
          ·
            refine ⟨10868723147645124092838641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7245815431763416061892427 10868723147645124092838641)
            ·
              refine ⟨8151542360733843069628981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10868723147645124092838641 8151542360733843069628981)
              ·
                refine ⟨764207096318797787777717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8151542360733843069628981 764207096318797787777717)
                ·
                  refine ⟨71644415279887292604161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 764207096318797787777717 71644415279887292604161)
                  ·
                    rfl

theorem cell23_1255743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 5].length) (baseStart_1255743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255743 prefixEnd_1255743 := by exact prefixLift 1255743
  have htrace : WordTrace (prefixWord ++ tailWord_1255743) baseStart_1255743 baseEnd_1255743 := by
    simpa [prefixWord, tailWord_1255743, baseEnd_1255743] using wordTrace_append hprefix tailTrace_1255743
  have hstable : (prefixWord ++ tailWord_1255743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255743).length < 2 ^ (prefixWord ++ tailWord_1255743).sum := by decide
  have hdescent : baseEnd_1255743 < baseStart_1255743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255760 : List Nat := [2, 1, 1, 1, 1, 6, 4, 2, 5]
def baseStart_1255760 : Nat := 118140960795 + 1255760 * 2 ^ 59
def prefixEnd_1255760 : Nat := 4983230072969 + 3 ^ 40 * 1255760 * 2
def baseEnd_1255760 : Nat := 71645385187790229658319

theorem tailTrace_1255760 : CollatzResearch.WordTrace tailWord_1255760 prefixEnd_1255760 71645385187790229658319 := by
  unfold tailWord_1255760
  simp only [CollatzResearch.WordTrace]
  refine ⟨22900664965301730789270367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30534219953735641052360489 22900664965301730789270367)
  ·
    refine ⟨34350997447952596183905551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22900664965301730789270367 34350997447952596183905551)
    ·
      refine ⟨51526496171928894275858327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34350997447952596183905551 51526496171928894275858327)
      ·
        refine ⟨77289744257893341413787491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51526496171928894275858327 77289744257893341413787491)
        ·
          refine ⟨115934616386840012120681237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77289744257893341413787491 115934616386840012120681237)
          ·
            refine ⟨5434435143133125568156933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115934616386840012120681237 5434435143133125568156933)
            ·
              refine ⟨1018956589337461044029425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5434435143133125568156933 1018956589337461044029425)
              ·
                refine ⟨764217442003095783022069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018956589337461044029425 764217442003095783022069)
                ·
                  refine ⟨71645385187790229658319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 764217442003095783022069 71645385187790229658319)
                  ·
                    rfl

theorem cell23_1255760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 5].length) (baseStart_1255760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255760 prefixEnd_1255760 := by exact prefixLift 1255760
  have htrace : WordTrace (prefixWord ++ tailWord_1255760) baseStart_1255760 baseEnd_1255760 := by
    simpa [prefixWord, tailWord_1255760, baseEnd_1255760] using wordTrace_append hprefix tailTrace_1255760
  have hstable : (prefixWord ++ tailWord_1255760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255760).length < 2 ^ (prefixWord ++ tailWord_1255760).sum := by decide
  have hdescent : baseEnd_1255760 < baseStart_1255760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255793 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 3, 6, 2]
def baseStart_1255793 : Nat := 118140960795 + 1255793 * 2 ^ 59
def prefixEnd_1255793 : Nat := 4983230072969 + 3 ^ 40 * 1255793 * 2
def baseEnd_1255793 : Nat := 644825411551710437812219

theorem tailTrace_1255793 : CollatzResearch.WordTrace tailWord_1255793 prefixEnd_1255793 644825411551710437812219 := by
  unfold tailWord_1255793
  simp only [CollatzResearch.WordTrace]
  refine ⟨45802533539483908214492033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30535022359655938809661355 45802533539483908214492033)
  ·
    refine ⟨34351900154612931160869025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45802533539483908214492033 34351900154612931160869025)
    ·
      refine ⟨25763925115959698370651769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34351900154612931160869025 25763925115959698370651769)
      ·
        refine ⟨19322943836969773777988827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25763925115959698370651769 19322943836969773777988827)
        ·
          refine ⟨28984415755454660666983241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19322943836969773777988827 28984415755454660666983241)
          ·
            refine ⟨21738311816590995500237431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28984415755454660666983241 21738311816590995500237431)
            ·
              refine ⟨32607467724886493250356147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21738311816590995500237431 32607467724886493250356147)
              ·
                refine ⟨48911201587329739875534221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32607467724886493250356147 48911201587329739875534221)
                ·
                  refine ⟨18341700595248652453325333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48911201587329739875534221 18341700595248652453325333)
                  ·
                    refine ⟨859767215402280583749625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18341700595248652453325333 859767215402280583749625)
                    ·
                      refine ⟨644825411551710437812219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859767215402280583749625 644825411551710437812219)
                      ·
                        rfl

theorem cell23_1255793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_1255793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255793 prefixEnd_1255793 := by exact prefixLift 1255793
  have htrace : WordTrace (prefixWord ++ tailWord_1255793) baseStart_1255793 baseEnd_1255793 := by
    simpa [prefixWord, tailWord_1255793, baseEnd_1255793] using wordTrace_append hprefix tailTrace_1255793
  have hstable : (prefixWord ++ tailWord_1255793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255793).length < 2 ^ (prefixWord ++ tailWord_1255793).sum := by decide
  have hdescent : baseEnd_1255793 < baseStart_1255793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255813 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_1255813 : Nat := 118140960795 + 1255813 * 2 ^ 59
def prefixEnd_1255813 : Nat := 4983230072969 + 3 ^ 40 * 1255813 * 2
def baseEnd_1255813 : Nat := 644835681164800359562127

theorem tailTrace_1255813 : CollatzResearch.WordTrace tailWord_1255813 prefixEnd_1255813 644835681164800359562127 := by
  unfold tailWord_1255813
  simp only [CollatzResearch.WordTrace]
  refine ⟨45803262999411451630220093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30535508666274301086813395 45803262999411451630220093)
  ·
    refine ⟨17176223624779294361332535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45803262999411451630220093 17176223624779294361332535)
    ·
      refine ⟨25764335437168941541998803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17176223624779294361332535 25764335437168941541998803)
      ·
        refine ⟨38646503155753412312998205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25764335437168941541998803 38646503155753412312998205)
        ·
          refine ⟨14492438683407529617374327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38646503155753412312998205 14492438683407529617374327)
          ·
            refine ⟨21738658025111294426061491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14492438683407529617374327 21738658025111294426061491)
            ·
              refine ⟨32607987037666941639092237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21738658025111294426061491 32607987037666941639092237)
              ·
                refine ⟨12227995139125103114659589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32607987037666941639092237 12227995139125103114659589)
                ·
                  refine ⟨2292749088585956833998673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12227995139125103114659589 2292749088585956833998673)
                  ·
                    refine ⟨1719561816439467625499005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2292749088585956833998673 1719561816439467625499005)
                    ·
                      refine ⟨644835681164800359562127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1719561816439467625499005 644835681164800359562127)
                      ·
                        rfl

theorem cell23_1255813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_1255813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255813 prefixEnd_1255813 := by exact prefixLift 1255813
  have htrace : WordTrace (prefixWord ++ tailWord_1255813) baseStart_1255813 baseEnd_1255813 := by
    simpa [prefixWord, tailWord_1255813, baseEnd_1255813] using wordTrace_append hprefix tailTrace_1255813
  have hstable : (prefixWord ++ tailWord_1255813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255813).length < 2 ^ (prefixWord ++ tailWord_1255813).sum := by decide
  have hdescent : baseEnd_1255813 < baseStart_1255813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255820 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_1255820 : Nat := 118140960795 + 1255820 * 2 ^ 59
def prefixEnd_1255820 : Nat := 4983230072969 + 3 ^ 40 * 1255820 * 2
def baseEnd_1255820 : Nat := 214946425176460610724865

theorem tailTrace_1255820 : CollatzResearch.WordTrace tailWord_1255820 prefixEnd_1255820 214946425176460610724865 := by
  unfold tailWord_1255820
  simp only [CollatzResearch.WordTrace]
  refine ⟨22901759155193045912862457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30535678873590727883816609 22901759155193045912862457)
  ·
    refine ⟨17176319366394784434646843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22901759155193045912862457 17176319366394784434646843)
    ·
      refine ⟨25764479049592176651970265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17176319366394784434646843 25764479049592176651970265)
      ·
        refine ⟨19323359287194132488977699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25764479049592176651970265 19323359287194132488977699)
        ·
          refine ⟨28985038930791198733466549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19323359287194132488977699 28985038930791198733466549)
          ·
            refine ⟨2717347399761674881262489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28985038930791198733466549 2717347399761674881262489)
            ·
              refine ⟨2038010549821256160946867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717347399761674881262489 2038010549821256160946867)
              ·
                refine ⟨3057015824731884241420301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038010549821256160946867 3057015824731884241420301)
                ·
                  refine ⟨1146380934274456590532613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3057015824731884241420301 1146380934274456590532613)
                  ·
                    refine ⟨214946425176460610724865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1146380934274456590532613 214946425176460610724865)
                    ·
                      rfl

theorem cell23_1255820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_1255820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255820 prefixEnd_1255820 := by exact prefixLift 1255820
  have htrace : WordTrace (prefixWord ++ tailWord_1255820) baseStart_1255820 baseEnd_1255820 := by
    simpa [prefixWord, tailWord_1255820, baseEnd_1255820] using wordTrace_append hprefix tailTrace_1255820
  have hstable : (prefixWord ++ tailWord_1255820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255820).length < 2 ^ (prefixWord ++ tailWord_1255820).sum := by decide
  have hdescent : baseEnd_1255820 < baseStart_1255820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255856 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_1255856 : Nat := 118140960795 + 1255856 * 2 ^ 59
def prefixEnd_1255856 : Nat := 4983230072969 + 3 ^ 40 * 1255856 * 2
def baseEnd_1255856 : Nat := 644857760832943691324429

theorem tailTrace_1255856 : CollatzResearch.WordTrace tailWord_1255856 prefixEnd_1255856 644857760832943691324429 := by
  unfold tailWord_1255856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22902415669127834987017711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30536554225503779982690281 22902415669127834987017711)
  ·
    refine ⟨34353623503691752480526567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22902415669127834987017711 34353623503691752480526567)
    ·
      refine ⟨51530435255537628720789851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34353623503691752480526567 51530435255537628720789851)
      ·
        refine ⟨77295652883306443081184777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51530435255537628720789851 77295652883306443081184777)
        ·
          refine ⟨57971739662479832310888583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77295652883306443081184777 57971739662479832310888583)
          ·
            refine ⟨86957609493719748466332875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57971739662479832310888583 86957609493719748466332875)
            ·
              refine ⟨130436414240579622699499313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86957609493719748466332875 130436414240579622699499313)
              ·
                refine ⟨97827310680434717024624485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130436414240579622699499313 97827310680434717024624485)
                ·
                  refine ⟨18342620752581509442117091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97827310680434717024624485 18342620752581509442117091)
                  ·
                    refine ⟨27513931128872264163175637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18342620752581509442117091 27513931128872264163175637)
                    ·
                      refine ⟨644857760832943691324429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27513931128872264163175637 644857760832943691324429)
                      ·
                        rfl

theorem cell23_1255856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_1255856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255856 prefixEnd_1255856 := by exact prefixLift 1255856
  have htrace : WordTrace (prefixWord ++ tailWord_1255856) baseStart_1255856 baseEnd_1255856 := by
    simpa [prefixWord, tailWord_1255856, baseEnd_1255856] using wordTrace_append hprefix tailTrace_1255856
  have hstable : (prefixWord ++ tailWord_1255856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255856).length < 2 ^ (prefixWord ++ tailWord_1255856).sum := by decide
  have hdescent : baseEnd_1255856 < baseStart_1255856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255883 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 4]
def baseStart_1255883 : Nat := 118140960795 + 1255883 * 2 ^ 59
def prefixEnd_1255883 : Nat := 4983230072969 + 3 ^ 40 * 1255883 * 2
def baseEnd_1255883 : Nat := 644871624810615085686805

theorem tailTrace_1255883 : CollatzResearch.WordTrace tailWord_1255883 prefixEnd_1255883 644871624810615085686805 := by
  unfold tailWord_1255883
  simp only [CollatzResearch.WordTrace]
  refine ⟨45805816109157853585268303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30537210739438569056845535 45805816109157853585268303)
  ·
    refine ⟨68708724163736780377902455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45805816109157853585268303 68708724163736780377902455)
    ·
      refine ⟨103063086245605170566853683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68708724163736780377902455 103063086245605170566853683)
      ·
        refine ⟨154594629368407755850280525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103063086245605170566853683 154594629368407755850280525)
        ·
          refine ⟨57972986013152908443855197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154594629368407755850280525 57972986013152908443855197)
          ·
            refine ⟨21739869754932340666445699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57972986013152908443855197 21739869754932340666445699)
            ·
              refine ⟨32609804632398510999668549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21739869754932340666445699 32609804632398510999668549)
              ·
                refine ⟨6114338368574720812437853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32609804632398510999668549 6114338368574720812437853)
                ·
                  refine ⟨2292876888215520304664195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6114338368574720812437853 2292876888215520304664195)
                  ·
                    refine ⟨3439315332323280456996293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2292876888215520304664195 3439315332323280456996293)
                    ·
                      refine ⟨644871624810615085686805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3439315332323280456996293 644871624810615085686805)
                      ·
                        rfl

theorem cell23_1255883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 4].length) (baseStart_1255883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255883 prefixEnd_1255883 := by exact prefixLift 1255883
  have htrace : WordTrace (prefixWord ++ tailWord_1255883) baseStart_1255883 baseEnd_1255883 := by
    simpa [prefixWord, tailWord_1255883, baseEnd_1255883] using wordTrace_append hprefix tailTrace_1255883
  have hstable : (prefixWord ++ tailWord_1255883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255883).length < 2 ^ (prefixWord ++ tailWord_1255883).sum := by decide
  have hdescent : baseEnd_1255883 < baseStart_1255883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255884 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 6]
def baseStart_1255884 : Nat := 118140960795 + 1255884 * 2 ^ 59
def prefixEnd_1255884 : Nat := 4983230072969 + 3 ^ 40 * 1255884 * 2
def baseEnd_1255884 : Nat := 71652459810141064641589

theorem tailTrace_1255884 : CollatzResearch.WordTrace tailWord_1255884 prefixEnd_1255884 71652459810141064641589 := by
  unfold tailWord_1255884
  simp only [CollatzResearch.WordTrace]
  refine ⟨22902926291077115378027353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30537235054769487170703137 22902926291077115378027353)
  ·
    refine ⟨17177194718307836533520515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22902926291077115378027353 17177194718307836533520515)
    ·
      refine ⟨25765792077461754800280773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17177194718307836533520515 25765792077461754800280773)
      ·
        refine ⟨4831086014524079025052645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25765792077461754800280773 4831086014524079025052645)
        ·
          refine ⟨905828627723264817197371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4831086014524079025052645 905828627723264817197371)
          ·
            refine ⟨1358742941584897225796057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905828627723264817197371 1358742941584897225796057)
            ·
              refine ⟨1019057206188672919347043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358742941584897225796057 1019057206188672919347043)
              ·
                refine ⟨1528585809283009379020565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019057206188672919347043 1528585809283009379020565)
                ·
                  refine ⟨71652459810141064641589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1528585809283009379020565 71652459810141064641589)
                  ·
                    rfl

theorem cell23_1255884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_1255884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255884 prefixEnd_1255884 := by exact prefixLift 1255884
  have htrace : WordTrace (prefixWord ++ tailWord_1255884) baseStart_1255884 baseEnd_1255884 := by
    simpa [prefixWord, tailWord_1255884, baseEnd_1255884] using wordTrace_append hprefix tailTrace_1255884
  have hstable : (prefixWord ++ tailWord_1255884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255884).length < 2 ^ (prefixWord ++ tailWord_1255884).sum := by decide
  have hdescent : baseEnd_1255884 < baseStart_1255884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255940 : List Nat := [2, 3, 2, 3, 1, 1, 3, 8]
def baseStart_1255940 : Nat := 118140960795 + 1255940 * 2 ^ 59
def prefixEnd_1255940 : Nat := 4983230072969 + 3 ^ 40 * 1255940 * 2
def baseEnd_1255940 : Nat := 23885218266960050469409

theorem tailTrace_1255940 : CollatzResearch.WordTrace tailWord_1255940 prefixEnd_1255940 23885218266960050469409 := by
  unfold tailWord_1255940
  simp only [CollatzResearch.WordTrace]
  refine ⟨22903947534975676160046637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30538596713300901546728849 22903947534975676160046637)
  ·
    refine ⟨8588980325615878560017489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22903947534975676160046637 8588980325615878560017489)
    ·
      refine ⟨6441735244211908920013117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8588980325615878560017489 6441735244211908920013117)
      ·
        refine ⟨2415650716579465845004919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6441735244211908920013117 2415650716579465845004919)
        ·
          refine ⟨3623476074869198767507379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2415650716579465845004919 3623476074869198767507379)
          ·
            refine ⟨5435214112303798151261069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623476074869198767507379 5435214112303798151261069)
            ·
              refine ⟨2038205292113924306722901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5435214112303798151261069 2038205292113924306722901)
              ·
                refine ⟨23885218266960050469409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2038205292113924306722901 23885218266960050469409)
                ·
                  rfl

theorem cell23_1255940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 8].length) (baseStart_1255940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255940 prefixEnd_1255940 := by exact prefixLift 1255940
  have htrace : WordTrace (prefixWord ++ tailWord_1255940) baseStart_1255940 baseEnd_1255940 := by
    simpa [prefixWord, tailWord_1255940, baseEnd_1255940] using wordTrace_append hprefix tailTrace_1255940
  have hstable : (prefixWord ++ tailWord_1255940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255940).length < 2 ^ (prefixWord ++ tailWord_1255940).sum := by decide
  have hdescent : baseEnd_1255940 < baseStart_1255940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255968 : List Nat := [2, 1, 1, 6, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1255968 : Nat := 118140960795 + 1255968 * 2 ^ 59
def prefixEnd_1255968 : Nat := 4983230072969 + 3 ^ 40 * 1255968 * 2
def baseEnd_1255968 : Nat := 644915270666247253123915

theorem tailTrace_1255968 : CollatzResearch.WordTrace tailWord_1255968 prefixEnd_1255968 644915270666247253123915 := by
  unfold tailWord_1255968
  simp only [CollatzResearch.WordTrace]
  refine ⟨22904458156924956551056279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30539277542566608734741705 22904458156924956551056279)
  ·
    refine ⟨34356687235387434826584419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22904458156924956551056279 34356687235387434826584419)
    ·
      refine ⟨51535030853081152239876629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34356687235387434826584419 51535030853081152239876629)
      ·
        refine ⟨2415704571238179011244217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51535030853081152239876629 2415704571238179011244217)
        ·
          refine ⟨1811778428428634258433163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2415704571238179011244217 1811778428428634258433163)
          ·
            refine ⟨2717667642642951387649745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811778428428634258433163 2717667642642951387649745)
            ·
              refine ⟨2038250731982213540737309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717667642642951387649745 2038250731982213540737309)
              ·
                refine ⟨764344024493330077776491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2038250731982213540737309 764344024493330077776491)
                ·
                  refine ⟨1146516036739995116664737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764344024493330077776491 1146516036739995116664737)
                  ·
                    refine ⟨859887027554996337498553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1146516036739995116664737 859887027554996337498553)
                    ·
                      refine ⟨644915270666247253123915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 859887027554996337498553 644915270666247253123915)
                      ·
                        rfl

theorem cell23_1255968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1255968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1255968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1255968 prefixEnd_1255968 := by exact prefixLift 1255968
  have htrace : WordTrace (prefixWord ++ tailWord_1255968) baseStart_1255968 baseEnd_1255968 := by
    simpa [prefixWord, tailWord_1255968, baseEnd_1255968] using wordTrace_append hprefix tailTrace_1255968
  have hstable : (prefixWord ++ tailWord_1255968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255968).length < 2 ^ (prefixWord ++ tailWord_1255968).sum := by decide
  have hdescent : baseEnd_1255968 < baseStart_1255968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256001 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_1256001 : Nat := 118140960795 + 1256001 * 2 ^ 59
def prefixEnd_1256001 : Nat := 4983230072969 + 3 ^ 40 * 1256001 * 2
def baseEnd_1256001 : Nat := 644932215527845624011263

theorem tailTrace_1256001 : CollatzResearch.WordTrace tailWord_1256001 prefixEnd_1256001 644932215527845624011263 := by
  unfold tailWord_1256001
  simp only [CollatzResearch.WordTrace]
  refine ⟨45810119922730359738063857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30540079948486906492042571 45810119922730359738063857)
  ·
    refine ⟨34357589942047769803547893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45810119922730359738063857 34357589942047769803547893)
    ·
      refine ⟨3221024057066978419082615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34357589942047769803547893 3221024057066978419082615)
      ·
        refine ⟨4831536085600467628623923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3221024057066978419082615 4831536085600467628623923)
        ·
          refine ⟨7247304128400701442935885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4831536085600467628623923 7247304128400701442935885)
          ·
            refine ⟨2717739048150263041100957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7247304128400701442935885 2717739048150263041100957)
            ·
              refine ⟨1019152143056348640412859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2717739048150263041100957 1019152143056348640412859)
              ·
                refine ⟨1528728214584522960619289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019152143056348640412859 1528728214584522960619289)
                ·
                  refine ⟨1146546160938392220464467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1528728214584522960619289 1146546160938392220464467)
                  ·
                    refine ⟨1719819241407588330696701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1146546160938392220464467 1719819241407588330696701)
                    ·
                      refine ⟨644932215527845624011263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1719819241407588330696701 644932215527845624011263)
                      ·
                        rfl

theorem cell23_1256001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_1256001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256001 prefixEnd_1256001 := by exact prefixLift 1256001
  have htrace : WordTrace (prefixWord ++ tailWord_1256001) baseStart_1256001 baseEnd_1256001 := by
    simpa [prefixWord, tailWord_1256001, baseEnd_1256001] using wordTrace_append hprefix tailTrace_1256001
  have hstable : (prefixWord ++ tailWord_1256001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256001).length < 2 ^ (prefixWord ++ tailWord_1256001).sum := by decide
  have hdescent : baseEnd_1256001 < baseStart_1256001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256043 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 3, 7]
def baseStart_1256043 : Nat := 118140960795 + 1256043 * 2 ^ 59
def prefixEnd_1256043 : Nat := 4983230072969 + 3 ^ 40 * 1256043 * 2
def baseEnd_1256043 : Nat := 214984593905111486562023

theorem tailTrace_1256043 : CollatzResearch.WordTrace tailWord_1256043 prefixEnd_1256043 214984593905111486562023 := by
  unfold tailWord_1256043
  simp only [CollatzResearch.WordTrace]
  refine ⟨45811651788578200911092783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30541101192385467274061855 45811651788578200911092783)
  ·
    refine ⟨68717477682867301366639175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45811651788578200911092783 68717477682867301366639175)
    ·
      refine ⟨103076216524300952049958763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68717477682867301366639175 103076216524300952049958763)
      ·
        refine ⟨154614324786451428074938145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103076216524300952049958763 154614324786451428074938145)
        ·
          refine ⟨115960743589838571056203609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154614324786451428074938145 115960743589838571056203609)
          ·
            refine ⟨86970557692378928292152707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115960743589838571056203609 86970557692378928292152707)
            ·
              refine ⟨130455836538568392438229061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86970557692378928292152707 130455836538568392438229061)
              ·
                refine ⟨24460469350981573582167949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130455836538568392438229061 24460469350981573582167949)
                ·
                  refine ⟨9172676006618090093312981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24460469350981573582167949 9172676006618090093312981)
                  ·
                    refine ⟨214984593905111486562023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9172676006618090093312981 214984593905111486562023)
                    ·
                      rfl

theorem cell23_1256043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 7].length) (baseStart_1256043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256043 prefixEnd_1256043 := by exact prefixLift 1256043
  have htrace : WordTrace (prefixWord ++ tailWord_1256043) baseStart_1256043 baseEnd_1256043 := by
    simpa [prefixWord, tailWord_1256043, baseEnd_1256043] using wordTrace_append hprefix tailTrace_1256043
  have hstable : (prefixWord ++ tailWord_1256043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256043).length < 2 ^ (prefixWord ++ tailWord_1256043).sum := by decide
  have hdescent : baseEnd_1256043 < baseStart_1256043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256100 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1256100 : Nat := 118140960795 + 1256100 * 2 ^ 59
def prefixEnd_1256100 : Nat := 4983230072969 + 3 ^ 40 * 1256100 * 2
def baseEnd_1256100 : Nat := 644983050112640736673307

theorem tailTrace_1256100 : CollatzResearch.WordTrace tailWord_1256100 prefixEnd_1256100 644983050112640736673307 := by
  unfold tailWord_1256100
  simp only [CollatzResearch.WordTrace]
  refine ⟨22906865374685849822958877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30542487166247799763945169 22906865374685849822958877)
  ·
    refine ⟨8590074515507193683609579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22906865374685849822958877 8590074515507193683609579)
    ·
      refine ⟨12885111773260790525414369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8590074515507193683609579 12885111773260790525414369)
      ·
        refine ⟨9663833829945592894060777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12885111773260790525414369 9663833829945592894060777)
        ·
          refine ⟨7247875372459194670545583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9663833829945592894060777 7247875372459194670545583)
          ·
            refine ⟨10871813058688792005818375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7247875372459194670545583 10871813058688792005818375)
            ·
              refine ⟨16307719588033188008727563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10871813058688792005818375 16307719588033188008727563)
              ·
                refine ⟨24461579382049782013091345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16307719588033188008727563 24461579382049782013091345)
                ·
                  refine ⟨18346184536537336509818509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24461579382049782013091345 18346184536537336509818509)
                  ·
                    refine ⟨6879819201201501191181941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18346184536537336509818509 6879819201201501191181941)
                    ·
                      refine ⟨644983050112640736673307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6879819201201501191181941 644983050112640736673307)
                      ·
                        rfl

theorem cell23_1256100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1256100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256100 prefixEnd_1256100 := by exact prefixLift 1256100
  have htrace : WordTrace (prefixWord ++ tailWord_1256100) baseStart_1256100 baseEnd_1256100 := by
    simpa [prefixWord, tailWord_1256100, baseEnd_1256100] using wordTrace_append hprefix tailTrace_1256100
  have hstable : (prefixWord ++ tailWord_1256100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256100).length < 2 ^ (prefixWord ++ tailWord_1256100).sum := by decide
  have hdescent : baseEnd_1256100 < baseStart_1256100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256164 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_1256164 : Nat := 118140960795 + 1256164 * 2 ^ 59
def prefixEnd_1256164 : Nat := 4983230072969 + 3 ^ 40 * 1256164 * 2
def baseEnd_1256164 : Nat := 645015912874528486273013

theorem tailTrace_1256164 : CollatzResearch.WordTrace tailWord_1256164 prefixEnd_1256164 645015912874528486273013 := by
  unfold tailWord_1256164
  simp only [CollatzResearch.WordTrace]
  refine ⟨22908032510569919288123773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30544043347426559050831697 22908032510569919288123773)
  ·
    refine ⟨8590512191463719733046415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22908032510569919288123773 8590512191463719733046415)
    ·
      refine ⟨12885768287195579599569623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8590512191463719733046415 12885768287195579599569623)
      ·
        refine ⟨19328652430793369399354435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12885768287195579599569623 19328652430793369399354435)
        ·
          refine ⟨28992978646190054099031653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19328652430793369399354435 28992978646190054099031653)
          ·
            refine ⟨5436183496160635143568435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28992978646190054099031653 5436183496160635143568435)
            ·
              refine ⟨8154275244240952715352653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5436183496160635143568435 8154275244240952715352653)
              ·
                refine ⟨3057853216590357268257245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8154275244240952715352653 3057853216590357268257245)
                ·
                  refine ⟨1146694956221383975596467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3057853216590357268257245 1146694956221383975596467)
                  ·
                    refine ⟨1720042434332075963394701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1146694956221383975596467 1720042434332075963394701)
                    ·
                      refine ⟨645015912874528486273013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1720042434332075963394701 645015912874528486273013)
                      ·
                        rfl

theorem cell23_1256164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_1256164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256164 prefixEnd_1256164 := by exact prefixLift 1256164
  have htrace : WordTrace (prefixWord ++ tailWord_1256164) baseStart_1256164 baseEnd_1256164 := by
    simpa [prefixWord, tailWord_1256164, baseEnd_1256164] using wordTrace_append hprefix tailTrace_1256164
  have hstable : (prefixWord ++ tailWord_1256164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256164).length < 2 ^ (prefixWord ++ tailWord_1256164).sum := by decide
  have hdescent : baseEnd_1256164 < baseStart_1256164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256174 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_1256174 : Nat := 118140960795 + 1256174 * 2 ^ 59
def prefixEnd_1256174 : Nat := 4983230072969 + 3 ^ 40 * 1256174 * 2
def baseEnd_1256174 : Nat := 645021047681073447147967

theorem tailTrace_1256174 : CollatzResearch.WordTrace tailWord_1256174 prefixEnd_1256174 645021047681073447147967 := by
  unfold tailWord_1256174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727053718887951285513947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30544286500735740189407717 5727053718887951285513947)
  ·
    refine ⟨8590580578331926928270921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5727053718887951285513947 8590580578331926928270921)
    ·
      refine ⟨6442935433748945196203191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8590580578331926928270921 6442935433748945196203191)
      ·
        refine ⟨9664403150623417794304787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6442935433748945196203191 9664403150623417794304787)
        ·
          refine ⟨14496604725935126691457181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9664403150623417794304787 14496604725935126691457181)
          ·
            refine ⟨5436226772225672509296443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14496604725935126691457181 5436226772225672509296443)
            ·
              refine ⟨8154340158338508763944665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5436226772225672509296443 8154340158338508763944665)
              ·
                refine ⟨6115755118753881572958499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8154340158338508763944665 6115755118753881572958499)
                ·
                  refine ⟨9173632678130822359437749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6115755118753881572958499 9173632678130822359437749)
                  ·
                    refine ⟨860028063574764596197289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9173632678130822359437749 860028063574764596197289)
                    ·
                      refine ⟨645021047681073447147967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860028063574764596197289 645021047681073447147967)
                      ·
                        rfl

theorem cell23_1256174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_1256174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256174 prefixEnd_1256174 := by exact prefixLift 1256174
  have htrace : WordTrace (prefixWord ++ tailWord_1256174) baseStart_1256174 baseEnd_1256174 := by
    simpa [prefixWord, tailWord_1256174, baseEnd_1256174] using wordTrace_append hprefix tailTrace_1256174
  have hstable : (prefixWord ++ tailWord_1256174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256174).length < 2 ^ (prefixWord ++ tailWord_1256174).sum := by decide
  have hdescent : baseEnd_1256174 < baseStart_1256174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256207 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 5]
def baseStart_1256207 : Nat := 118140960795 + 1256207 * 2 ^ 59
def prefixEnd_1256207 : Nat := 4983230072969 + 3 ^ 40 * 1256207 * 2
def baseEnd_1256207 : Nat := 645037992542671818035315

theorem tailTrace_1256207 : CollatzResearch.WordTrace tailWord_1256207 prefixEnd_1256207 645037992542671818035315 := by
  unfold tailWord_1256207
  simp only [CollatzResearch.WordTrace]
  refine ⟨45817633359984056920062875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30545088906656037946708583 45817633359984056920062875)
  ·
    refine ⟨68726450039976085380094313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45817633359984056920062875 68726450039976085380094313)
    ·
      refine ⟨51544837529982064035070735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68726450039976085380094313 51544837529982064035070735)
      ·
        refine ⟨77317256294973096052606103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51544837529982064035070735 77317256294973096052606103)
        ·
          refine ⟨115975884442459644078909155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77317256294973096052606103 115975884442459644078909155)
          ·
            refine ⟨173963826663689466118363733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115975884442459644078909155 173963826663689466118363733)
            ·
              refine ⟨2038638593715110931074575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 173963826663689466118363733 2038638593715110931074575)
              ·
                refine ⟨3057957890572666396611863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038638593715110931074575 3057957890572666396611863)
                ·
                  refine ⟨4586936835858999594917795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057957890572666396611863 4586936835858999594917795)
                  ·
                    refine ⟨6880405253788499392376693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4586936835858999594917795 6880405253788499392376693)
                    ·
                      refine ⟨645037992542671818035315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6880405253788499392376693 645037992542671818035315)
                      ·
                        rfl

theorem cell23_1256207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_1256207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256207 prefixEnd_1256207 := by exact prefixLift 1256207
  have htrace : WordTrace (prefixWord ++ tailWord_1256207) baseStart_1256207 baseEnd_1256207 := by
    simpa [prefixWord, tailWord_1256207, baseEnd_1256207] using wordTrace_append hprefix tailTrace_1256207
  have hstable : (prefixWord ++ tailWord_1256207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256207).length < 2 ^ (prefixWord ++ tailWord_1256207).sum := by decide
  have hdescent : baseEnd_1256207 < baseStart_1256207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256215 : List Nat := [1, 1, 3, 4, 3, 1, 3, 2, 1, 1, 3]
def baseStart_1256215 : Nat := 118140960795 + 1256215 * 2 ^ 59
def prefixEnd_1256215 : Nat := 4983230072969 + 3 ^ 40 * 1256215 * 2
def baseEnd_1256215 : Nat := 645042100387907786735279

theorem tailTrace_1256215 : CollatzResearch.WordTrace tailWord_1256215 prefixEnd_1256215 645042100387907786735279 := by
  unfold tailWord_1256215
  simp only [CollatzResearch.WordTrace]
  refine ⟨45817925143955074286354099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30545283429303382857569399 45817925143955074286354099)
  ·
    refine ⟨68726887715932611429531149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45817925143955074286354099 68726887715932611429531149)
    ·
      refine ⟨25772582893474729286074181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68726887715932611429531149 25772582893474729286074181)
      ·
        refine ⟨4832359292526511741138909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25772582893474729286074181 4832359292526511741138909)
        ·
          refine ⟨1812134734697441902927091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4832359292526511741138909 1812134734697441902927091)
          ·
            refine ⟨2718202102046162854390637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812134734697441902927091 2718202102046162854390637)
            ·
              refine ⟨1019325788267311070396489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2718202102046162854390637 1019325788267311070396489)
              ·
                refine ⟨764494341200483302797367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019325788267311070396489 764494341200483302797367)
                ·
                  refine ⟨1146741511800724954196051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764494341200483302797367 1146741511800724954196051)
                  ·
                    refine ⟨1720112267701087431294077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1146741511800724954196051 1720112267701087431294077)
                    ·
                      refine ⟨645042100387907786735279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1720112267701087431294077 645042100387907786735279)
                      ·
                        rfl

theorem cell23_1256215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_1256215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256215 prefixEnd_1256215 := by exact prefixLift 1256215
  have htrace : WordTrace (prefixWord ++ tailWord_1256215) baseStart_1256215 baseEnd_1256215 := by
    simpa [prefixWord, tailWord_1256215, baseEnd_1256215] using wordTrace_append hprefix tailTrace_1256215
  have hstable : (prefixWord ++ tailWord_1256215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256215).length < 2 ^ (prefixWord ++ tailWord_1256215).sum := by decide
  have hdescent : baseEnd_1256215 < baseStart_1256215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256238 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1256238 : Nat := 118140960795 + 1256238 * 2 ^ 59
def prefixEnd_1256238 : Nat := 4983230072969 + 3 ^ 40 * 1256238 * 2
def baseEnd_1256238 : Nat := 645053910442961196747673

theorem tailTrace_1256238 : CollatzResearch.WordTrace tailWord_1256238 prefixEnd_1256238 645053910442961196747673 := by
  unfold tailWord_1256238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727345502858968651805171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30545842681914499476294245 5727345502858968651805171)
  ·
    refine ⟨8591018254288452977707757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5727345502858968651805171 8591018254288452977707757)
    ·
      refine ⟨3221631845358169866640409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8591018254288452977707757 3221631845358169866640409)
      ·
        refine ⟨2416223884018627399980307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3221631845358169866640409 2416223884018627399980307)
        ·
          refine ⟨3624335826027941099970461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416223884018627399980307 3624335826027941099970461)
          ·
            refine ⟨1359125934760477912488923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3624335826027941099970461 1359125934760477912488923)
            ·
              refine ⟨2038688902140716868733385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359125934760477912488923 2038688902140716868733385)
              ·
                refine ⟨1529016676605537651550039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2038688902140716868733385 1529016676605537651550039)
                ·
                  refine ⟨2293525014908306477325059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529016676605537651550039 2293525014908306477325059)
                  ·
                    refine ⟨3440287522362459715987589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2293525014908306477325059 3440287522362459715987589)
                    ·
                      refine ⟨645053910442961196747673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3440287522362459715987589 645053910442961196747673)
                      ·
                        rfl

theorem cell23_1256238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1256238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256238 prefixEnd_1256238 := by exact prefixLift 1256238
  have htrace : WordTrace (prefixWord ++ tailWord_1256238) baseStart_1256238 baseEnd_1256238 := by
    simpa [prefixWord, tailWord_1256238, baseEnd_1256238] using wordTrace_append hprefix tailTrace_1256238
  have hstable : (prefixWord ++ tailWord_1256238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256238).length < 2 ^ (prefixWord ++ tailWord_1256238).sum := by decide
  have hdescent : baseEnd_1256238 < baseStart_1256238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256277 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1256277 : Nat := 118140960795 + 1256277 * 2 ^ 59
def prefixEnd_1256277 : Nat := 4983230072969 + 3 ^ 40 * 1256277 * 2
def baseEnd_1256277 : Nat := 645073936188486544159993

theorem tailTrace_1256277 : CollatzResearch.WordTrace tailWord_1256277 prefixEnd_1256277 645073936188486544159993 := by
  unfold tailWord_1256277
  simp only [CollatzResearch.WordTrace]
  refine ⟨45820186469730458875111085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30546790979820305916740723 45820186469730458875111085)
  ·
    refine ⟨17182569926148922078166657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45820186469730458875111085 17182569926148922078166657)
    ·
      refine ⟨12886927444611691558624993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17182569926148922078166657 12886927444611691558624993)
      ·
        refine ⟨9665195583458768668968745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12886927444611691558624993 9665195583458768668968745)
        ·
          refine ⟨7248896687594076501726559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9665195583458768668968745 7248896687594076501726559)
          ·
            refine ⟨10873345031391114752589839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7248896687594076501726559 10873345031391114752589839)
            ·
              refine ⟨16310017547086672128884759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10873345031391114752589839 16310017547086672128884759)
              ·
                refine ⟨24465026320630008193327139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16310017547086672128884759 24465026320630008193327139)
                ·
                  refine ⟨36697539480945012289990709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24465026320630008193327139 36697539480945012289990709)
                  ·
                    refine ⟨3440394326338594902186629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36697539480945012289990709 3440394326338594902186629)
                    ·
                      refine ⟨645073936188486544159993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3440394326338594902186629 645073936188486544159993)
                      ·
                        rfl

theorem cell23_1256277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1256277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256277 prefixEnd_1256277 := by exact prefixLift 1256277
  have htrace : WordTrace (prefixWord ++ tailWord_1256277) baseStart_1256277 baseEnd_1256277 := by
    simpa [prefixWord, tailWord_1256277, baseEnd_1256277] using wordTrace_append hprefix tailTrace_1256277
  have hstable : (prefixWord ++ tailWord_1256277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256277).length < 2 ^ (prefixWord ++ tailWord_1256277).sum := by decide
  have hdescent : baseEnd_1256277 < baseStart_1256277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256287 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 2, 6]
def baseStart_1256287 : Nat := 118140960795 + 1256287 * 2 ^ 59
def prefixEnd_1256287 : Nat := 4983230072969 + 3 ^ 40 * 1256287 * 2
def baseEnd_1256287 : Nat := 215026356998343835011649

theorem tailTrace_1256287 : CollatzResearch.WordTrace tailWord_1256287 prefixEnd_1256287 215026356998343835011649 := by
  unfold tailWord_1256287
  simp only [CollatzResearch.WordTrace]
  refine ⟨45820551199694230582975115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30547034133129487055316743 45820551199694230582975115)
  ·
    refine ⟨68730826799541345874462673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45820551199694230582975115 68730826799541345874462673)
    ·
      refine ⟨51548120099656009405847005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68730826799541345874462673 51548120099656009405847005)
      ·
        refine ⟨19330545037371003527192627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51548120099656009405847005 19330545037371003527192627)
        ·
          refine ⟨28995817556056505290788941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19330545037371003527192627 28995817556056505290788941)
          ·
            refine ⟨10873431583521189484045853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28995817556056505290788941 10873431583521189484045853)
            ·
              refine ⟨4077536843820446056517195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10873431583521189484045853 4077536843820446056517195)
              ·
                refine ⟨6116305265730669084775793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077536843820446056517195 6116305265730669084775793)
                ·
                  refine ⟨4587228949298001813581845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6116305265730669084775793 4587228949298001813581845)
                  ·
                    refine ⟨215026356998343835011649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4587228949298001813581845 215026356998343835011649)
                    ·
                      rfl

theorem cell23_1256287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_1256287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256287 prefixEnd_1256287 := by exact prefixLift 1256287
  have htrace : WordTrace (prefixWord ++ tailWord_1256287) baseStart_1256287 baseEnd_1256287 := by
    simpa [prefixWord, tailWord_1256287, baseEnd_1256287] using wordTrace_append hprefix tailTrace_1256287
  have hstable : (prefixWord ++ tailWord_1256287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256287).length < 2 ^ (prefixWord ++ tailWord_1256287).sum := by decide
  have hdescent : baseEnd_1256287 < baseStart_1256287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256328 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_1256328 : Nat := 118140960795 + 1256328 * 2 ^ 59
def prefixEnd_1256328 : Nat := 4983230072969 + 3 ^ 40 * 1256328 * 2
def baseEnd_1256328 : Nat := 645100123701865844622259

theorem tailTrace_1256328 : CollatzResearch.WordTrace tailWord_1256328 prefixEnd_1256328 645100123701865844622259 := by
  unfold tailWord_1256328
  simp only [CollatzResearch.WordTrace]
  refine ⟨22911023296272847292608819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30548031061697129723478425 22911023296272847292608819)
  ·
    refine ⟨34366534944409270938913229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22911023296272847292608819 34366534944409270938913229)
    ·
      refine ⟨12887450604153476602092461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34366534944409270938913229 12887450604153476602092461)
      ·
        refine ⟨4832793976557553725784673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12887450604153476602092461 4832793976557553725784673)
        ·
          refine ⟨3624595482418165294338505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4832793976557553725784673 3624595482418165294338505)
          ·
            refine ⟨2718446611813623970753879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3624595482418165294338505 2718446611813623970753879)
            ·
              refine ⟨4077669917720435956130819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718446611813623970753879 4077669917720435956130819)
              ·
                refine ⟨6116504876580653934196229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077669917720435956130819 6116504876580653934196229)
                ·
                  refine ⟨1146844664358872612661793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6116504876580653934196229 1146844664358872612661793)
                  ·
                    refine ⟨860133498269154459496345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1146844664358872612661793 860133498269154459496345)
                    ·
                      refine ⟨645100123701865844622259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860133498269154459496345 645100123701865844622259)
                      ·
                        rfl

theorem cell23_1256328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_1256328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256328 prefixEnd_1256328 := by exact prefixLift 1256328
  have htrace : WordTrace (prefixWord ++ tailWord_1256328) baseStart_1256328 baseEnd_1256328 := by
    simpa [prefixWord, tailWord_1256328, baseEnd_1256328] using wordTrace_append hprefix tailTrace_1256328
  have hstable : (prefixWord ++ tailWord_1256328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256328).length < 2 ^ (prefixWord ++ tailWord_1256328).sum := by decide
  have hdescent : baseEnd_1256328 < baseStart_1256328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256357 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_1256357 : Nat := 118140960795 + 1256357 * 2 ^ 59
def prefixEnd_1256357 : Nat := 4983230072969 + 3 ^ 40 * 1256357 * 2
def baseEnd_1256357 : Nat := 645115014640846231159625

theorem tailTrace_1256357 : CollatzResearch.WordTrace tailWord_1256357 prefixEnd_1256357 645115014640846231159625 := by
  unfold tailWord_1256357
  simp only [CollatzResearch.WordTrace]
  refine ⟨45823104309440632538023325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30548736206293755025348883 45823104309440632538023325)
  ·
    refine ⟨17183664116040237201758747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45823104309440632538023325 17183664116040237201758747)
    ·
      refine ⟨25775496174060355802638121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17183664116040237201758747 25775496174060355802638121)
      ·
        refine ⟨19331622130545266851978591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25775496174060355802638121 19331622130545266851978591)
        ·
          refine ⟨28997433195817900277967887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19331622130545266851978591 28997433195817900277967887)
          ·
            refine ⟨43496149793726850416951831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28997433195817900277967887 43496149793726850416951831)
            ·
              refine ⟨65244224690590275625427747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43496149793726850416951831 65244224690590275625427747)
              ·
                refine ⟨97866337035885413438141621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65244224690590275625427747 97866337035885413438141621)
                ·
                  refine ⟨9174969097114257509825777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97866337035885413438141621 9174969097114257509825777)
                  ·
                    refine ⟨6881226822835693132369333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9174969097114257509825777 6881226822835693132369333)
                    ·
                      refine ⟨645115014640846231159625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6881226822835693132369333 645115014640846231159625)
                      ·
                        rfl

theorem cell23_1256357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_1256357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256357 prefixEnd_1256357 := by exact prefixLift 1256357
  have htrace : WordTrace (prefixWord ++ tailWord_1256357) baseStart_1256357 baseEnd_1256357 := by
    simpa [prefixWord, tailWord_1256357, baseEnd_1256357] using wordTrace_append hprefix tailTrace_1256357
  have hstable : (prefixWord ++ tailWord_1256357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256357).length < 2 ^ (prefixWord ++ tailWord_1256357).sum := by decide
  have hdescent : baseEnd_1256357 < baseStart_1256357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256381 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_1256381 : Nat := 118140960795 + 1256381 * 2 ^ 59
def prefixEnd_1256381 : Nat := 4983230072969 + 3 ^ 40 * 1256381 * 2
def baseEnd_1256381 : Nat := 215042446058851379086505

theorem tailTrace_1256381 : CollatzResearch.WordTrace tailWord_1256381 prefixEnd_1256381 215042446058851379086505 := by
  unfold tailWord_1256381
  simp only [CollatzResearch.WordTrace]
  refine ⟨45823979661353684636896997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30549319774235789757931331 45823979661353684636896997)
  ·
    refine ⟨8591996186503815869418187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45823979661353684636896997 8591996186503815869418187)
    ·
      refine ⟨12887994279755723804127281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8591996186503815869418187 12887994279755723804127281)
      ·
        refine ⟨9665995709816792853095461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12887994279755723804127281 9665995709816792853095461)
        ·
          refine ⟨1812374195590648659955399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9665995709816792853095461 1812374195590648659955399)
          ·
            refine ⟨2718561293385972989933099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812374195590648659955399 2718561293385972989933099)
            ·
              refine ⟨4077841940078959484899649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718561293385972989933099 4077841940078959484899649)
              ·
                refine ⟨3058381455059219613674737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4077841940078959484899649 3058381455059219613674737)
                ·
                  refine ⟨2293786091294414710256053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058381455059219613674737 2293786091294414710256053)
                  ·
                    refine ⟨215042446058851379086505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2293786091294414710256053 215042446058851379086505)
                    ·
                      rfl

theorem cell23_1256381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_1256381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256381 prefixEnd_1256381 := by exact prefixLift 1256381
  have htrace : WordTrace (prefixWord ++ tailWord_1256381) baseStart_1256381 baseEnd_1256381 := by
    simpa [prefixWord, tailWord_1256381, baseEnd_1256381] using wordTrace_append hprefix tailTrace_1256381
  have hstable : (prefixWord ++ tailWord_1256381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256381).length < 2 ^ (prefixWord ++ tailWord_1256381).sum := by decide
  have hdescent : baseEnd_1256381 < baseStart_1256381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256384 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_1256384 : Nat := 118140960795 + 1256384 * 2 ^ 59
def prefixEnd_1256384 : Nat := 4983230072969 + 3 ^ 40 * 1256384 * 2
def baseEnd_1256384 : Nat := 645128878618517625522001

theorem tailTrace_1256384 : CollatzResearch.WordTrace tailWord_1256384 prefixEnd_1256384 645128878618517625522001 := by
  unfold tailWord_1256384
  simp only [CollatzResearch.WordTrace]
  refine ⟨22912044540171408074628103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30549392720228544099504137 22912044540171408074628103)
  ·
    refine ⟨34368066810257112111942155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22912044540171408074628103 34368066810257112111942155)
    ·
      refine ⟨51552100215385668167913233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34368066810257112111942155 51552100215385668167913233)
      ·
        refine ⟨38664075161539251125934925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51552100215385668167913233 38664075161539251125934925)
        ·
          refine ⟨14499028185577219172225597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38664075161539251125934925 14499028185577219172225597)
          ·
            refine ⟨5437135569591457189584599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14499028185577219172225597 5437135569591457189584599)
            ·
              refine ⟨8155703354387185784376899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5437135569591457189584599 8155703354387185784376899)
              ·
                refine ⟨12233555031580778676565349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8155703354387185784376899 12233555031580778676565349)
                ·
                  refine ⟨2293791568421396001856003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12233555031580778676565349 2293791568421396001856003)
                  ·
                    refine ⟨3440687352632094002784005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2293791568421396001856003 3440687352632094002784005)
                    ·
                      refine ⟨645128878618517625522001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3440687352632094002784005 645128878618517625522001)
                      ·
                        rfl

theorem cell23_1256384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_1256384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256384 prefixEnd_1256384 := by exact prefixLift 1256384
  have htrace : WordTrace (prefixWord ++ tailWord_1256384) baseStart_1256384 baseEnd_1256384 := by
    simpa [prefixWord, tailWord_1256384, baseEnd_1256384] using wordTrace_append hprefix tailTrace_1256384
  have hstable : (prefixWord ++ tailWord_1256384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256384).length < 2 ^ (prefixWord ++ tailWord_1256384).sum := by decide
  have hdescent : baseEnd_1256384 < baseStart_1256384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256387 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 5]
def baseStart_1256387 : Nat := 118140960795 + 1256387 * 2 ^ 59
def prefixEnd_1256387 : Nat := 4983230072969 + 3 ^ 40 * 1256387 * 2
def baseEnd_1256387 : Nat := 645130419060481113784487

theorem tailTrace_1256387 : CollatzResearch.WordTrace tailWord_1256387 prefixEnd_1256387 645130419060481113784487 := by
  unfold tailWord_1256387
  simp only [CollatzResearch.WordTrace]
  refine ⟨45824198499331947661615415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30549465666221298441076943 45824198499331947661615415)
  ·
    refine ⟨68736297748997921492423123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45824198499331947661615415 68736297748997921492423123)
    ·
      refine ⟨103104446623496882238634685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68736297748997921492423123 103104446623496882238634685)
      ·
        refine ⟨38664167483811330839488007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103104446623496882238634685 38664167483811330839488007)
        ·
          refine ⟨57996251225716996259232011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38664167483811330839488007 57996251225716996259232011)
          ·
            refine ⟨86994376838575494388848017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57996251225716996259232011 86994376838575494388848017)
            ·
              refine ⟨65245782628931620791636013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86994376838575494388848017 65245782628931620791636013)
              ·
                refine ⟨24467168485849357796863505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65245782628931620791636013 24467168485849357796863505)
                ·
                  refine ⟨18350376364387018347647629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24467168485849357796863505 18350376364387018347647629)
                  ·
                    refine ⟨6881391136645131880367861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18350376364387018347647629 6881391136645131880367861)
                    ·
                      refine ⟨645130419060481113784487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6881391136645131880367861 645130419060481113784487)
                      ·
                        rfl

theorem cell23_1256387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_1256387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256387 prefixEnd_1256387 := by exact prefixLift 1256387
  have htrace : WordTrace (prefixWord ++ tailWord_1256387) baseStart_1256387 baseEnd_1256387 := by
    simpa [prefixWord, tailWord_1256387, baseEnd_1256387] using wordTrace_append hprefix tailTrace_1256387
  have hstable : (prefixWord ++ tailWord_1256387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256387).length < 2 ^ (prefixWord ++ tailWord_1256387).sum := by decide
  have hdescent : baseEnd_1256387 < baseStart_1256387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256407 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 10]
def baseStart_1256407 : Nat := 118140960795 + 1256407 * 2 ^ 59
def prefixEnd_1256407 : Nat := 4983230072969 + 3 ^ 40 * 1256407 * 2
def baseEnd_1256407 : Nat := 71682298741507892837155

theorem tailTrace_1256407 : CollatzResearch.WordTrace tailWord_1256407 prefixEnd_1256407 71682298741507892837155 := by
  unfold tailWord_1256407
  simp only [CollatzResearch.WordTrace]
  refine ⟨45824927959259491077343475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30549951972839660718228983 45824927959259491077343475)
  ·
    refine ⟨68737391938889236616015213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45824927959259491077343475 68737391938889236616015213)
    ·
      refine ⟨25776521977083463731005705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68737391938889236616015213 25776521977083463731005705)
      ·
        refine ⟨19332391482812597798254279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25776521977083463731005705 19332391482812597798254279)
        ·
          refine ⟨28998587224218896697381419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19332391482812597798254279 28998587224218896697381419)
          ·
            refine ⟨43497880836328345046072129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28998587224218896697381419 43497880836328345046072129)
            ·
              refine ⟨32623410627246258784554097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43497880836328345046072129 32623410627246258784554097)
              ·
                refine ⟨24467557970434694088415573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32623410627246258784554097 24467557970434694088415573)
                ·
                  refine ⟨71682298741507892837155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24467557970434694088415573 71682298741507892837155)
                  ·
                    rfl

theorem cell23_1256407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 10].length) (baseStart_1256407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256407 prefixEnd_1256407 := by exact prefixLift 1256407
  have htrace : WordTrace (prefixWord ++ tailWord_1256407) baseStart_1256407 baseEnd_1256407 := by
    simpa [prefixWord, tailWord_1256407, baseEnd_1256407] using wordTrace_append hprefix tailTrace_1256407
  have hstable : (prefixWord ++ tailWord_1256407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256407).length < 2 ^ (prefixWord ++ tailWord_1256407).sum := by decide
  have hdescent : baseEnd_1256407 < baseStart_1256407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256418 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1256418 : Nat := 118140960795 + 1256418 * 2 ^ 59
def prefixEnd_1256418 : Nat := 4983230072969 + 3 ^ 40 * 1256418 * 2
def baseEnd_1256418 : Nat := 645146336960770492496845

theorem tailTrace_1256418 : CollatzResearch.WordTrace tailWord_1256418 prefixEnd_1256418 645146336960770492496845 := by
  unfold tailWord_1256418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11456332290554909988998477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30550219441479759970662605 11456332290554909988998477)
  ·
    refine ⟨4296124608958091245874429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11456332290554909988998477 4296124608958091245874429)
    ·
      refine ⟨1611046728359284217202911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4296124608958091245874429 1611046728359284217202911)
      ·
        refine ⟨2416570092538926325804367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611046728359284217202911 2416570092538926325804367)
        ·
          refine ⟨3624855138808389488706551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416570092538926325804367 3624855138808389488706551)
          ·
            refine ⟨5437282708212584233059827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624855138808389488706551 5437282708212584233059827)
            ·
              refine ⟨8155924062318876349589741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5437282708212584233059827 8155924062318876349589741)
              ·
                refine ⟨3058471523369578631096153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8155924062318876349589741 3058471523369578631096153)
                ·
                  refine ⟨2293853642527183973322115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058471523369578631096153 2293853642527183973322115)
                  ·
                    refine ⟨3440780463790775959983173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2293853642527183973322115 3440780463790775959983173)
                    ·
                      refine ⟨645146336960770492496845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3440780463790775959983173 645146336960770492496845)
                      ·
                        rfl

theorem cell23_1256418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1256418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256418 prefixEnd_1256418 := by exact prefixLift 1256418
  have htrace : WordTrace (prefixWord ++ tailWord_1256418) baseStart_1256418 baseEnd_1256418 := by
    simpa [prefixWord, tailWord_1256418, baseEnd_1256418] using wordTrace_append hprefix tailTrace_1256418
  have hstable : (prefixWord ++ tailWord_1256418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256418).length < 2 ^ (prefixWord ++ tailWord_1256418).sum := by decide
  have hdescent : baseEnd_1256418 < baseStart_1256418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256427 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 8]
def baseStart_1256427 : Nat := 118140960795 + 1256427 * 2 ^ 59
def prefixEnd_1256427 : Nat := 4983230072969 + 3 ^ 40 * 1256427 * 2
def baseEnd_1256427 : Nat := 645150958286660957284303

theorem tailTrace_1256427 : CollatzResearch.WordTrace tailWord_1256427 prefixEnd_1256427 645150958286660957284303 := by
  unfold tailWord_1256427
  simp only [CollatzResearch.WordTrace]
  refine ⟨45825657419187034493071535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30550438279458022995381023 45825657419187034493071535)
  ·
    refine ⟨68738486128780551739607303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45825657419187034493071535 68738486128780551739607303)
    ·
      refine ⟨103107729193170827609410955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68738486128780551739607303 103107729193170827609410955)
      ·
        refine ⟨154661593789756241414116433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103107729193170827609410955 154661593789756241414116433)
        ·
          refine ⟨115996195342317181060587325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154661593789756241414116433 115996195342317181060587325)
          ·
            refine ⟨43498573253368942897720247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115996195342317181060587325 43498573253368942897720247)
            ·
              refine ⟨65247859880053414346580371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43498573253368942897720247 65247859880053414346580371)
              ·
                refine ⟨97871789820080121519870557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65247859880053414346580371 97871789820080121519870557)
                ·
                  refine ⟨36701921182530045569951459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97871789820080121519870557 36701921182530045569951459)
                  ·
                    refine ⟨55052881773795068354927189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36701921182530045569951459 55052881773795068354927189)
                    ·
                      refine ⟨645150958286660957284303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 55052881773795068354927189 645150958286660957284303)
                      ·
                        rfl

theorem cell23_1256427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_1256427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256427 prefixEnd_1256427 := by exact prefixLift 1256427
  have htrace : WordTrace (prefixWord ++ tailWord_1256427) baseStart_1256427 baseEnd_1256427 := by
    simpa [prefixWord, tailWord_1256427, baseEnd_1256427] using wordTrace_append hprefix tailTrace_1256427
  have hstable : (prefixWord ++ tailWord_1256427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256427).length < 2 ^ (prefixWord ++ tailWord_1256427).sum := by decide
  have hdescent : baseEnd_1256427 < baseStart_1256427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256436 : List Nat := [2, 6, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1256436 : Nat := 118140960795 + 1256436 * 2 ^ 59
def prefixEnd_1256436 : Nat := 4983230072969 + 3 ^ 40 * 1256436 * 2
def baseEnd_1256436 : Nat := 71683953290283491341307

theorem tailTrace_1256436 : CollatzResearch.WordTrace tailWord_1256436 prefixEnd_1256436 71683953290283491341307 := by
  unfold tailWord_1256436
  simp only [CollatzResearch.WordTrace]
  refine ⟨22912992838077214515074581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30550657117436286020099441 22912992838077214515074581)
  ·
    refine ⟨1074046539284869430394121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22912992838077214515074581 1074046539284869430394121)
    ·
      refine ⟨805534904463652072795591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1074046539284869430394121 805534904463652072795591)
      ·
        refine ⟨1208302356695478109193387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805534904463652072795591 1208302356695478109193387)
        ·
          refine ⟨1812453535043217163790081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208302356695478109193387 1812453535043217163790081)
          ·
            refine ⟨1359340151282412872842561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1812453535043217163790081 1359340151282412872842561)
            ·
              refine ⟨1019505113461809654631921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359340151282412872842561 1019505113461809654631921)
              ·
                refine ⟨764628835096357240973941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019505113461809654631921 764628835096357240973941)
                ·
                  refine ⟨71683953290283491341307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 764628835096357240973941 71683953290283491341307)
                  ·
                    rfl

theorem cell23_1256436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1256436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256436 prefixEnd_1256436 := by exact prefixLift 1256436
  have htrace : WordTrace (prefixWord ++ tailWord_1256436) baseStart_1256436 baseEnd_1256436 := by
    simpa [prefixWord, tailWord_1256436, baseEnd_1256436] using wordTrace_append hprefix tailTrace_1256436
  have hstable : (prefixWord ++ tailWord_1256436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256436).length < 2 ^ (prefixWord ++ tailWord_1256436).sum := by decide
  have hdescent : baseEnd_1256436 < baseStart_1256436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256438 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1256438 : Nat := 118140960795 + 1256438 * 2 ^ 59
def prefixEnd_1256438 : Nat := 4983230072969 + 3 ^ 40 * 1256438 * 2
def baseEnd_1256438 : Nat := 645156606573860414246753

theorem tailTrace_1256438 : CollatzResearch.WordTrace tailWord_1256438 prefixEnd_1256438 645156606573860414246753 := by
  unfold tailWord_1256438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864128663884198960732623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30550705748098122247814645 2864128663884198960732623)
  ·
    refine ⟨4296192995826298441098935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2864128663884198960732623 4296192995826298441098935)
    ·
      refine ⟨6444289493739447661648403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4296192995826298441098935 6444289493739447661648403)
      ·
        refine ⟨9666434240609171492472605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6444289493739447661648403 9666434240609171492472605)
        ·
          refine ⟨3624912840228439309677227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9666434240609171492472605 3624912840228439309677227)
          ·
            refine ⟨5437369260342658964515841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624912840228439309677227 5437369260342658964515841)
            ·
              refine ⟨4078026945256994223386881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437369260342658964515841 4078026945256994223386881)
              ·
                refine ⟨3058520208942745667540161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4078026945256994223386881 3058520208942745667540161)
                ·
                  refine ⟨2293890156707059250655121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058520208942745667540161 2293890156707059250655121)
                  ·
                    refine ⟨1720417617530294437991341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2293890156707059250655121 1720417617530294437991341)
                    ·
                      refine ⟨645156606573860414246753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1720417617530294437991341 645156606573860414246753)
                      ·
                        rfl

theorem cell23_1256438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1256438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256438 prefixEnd_1256438 := by exact prefixLift 1256438
  have htrace : WordTrace (prefixWord ++ tailWord_1256438) baseStart_1256438 baseEnd_1256438 := by
    simpa [prefixWord, tailWord_1256438, baseEnd_1256438] using wordTrace_append hprefix tailTrace_1256438
  have hstable : (prefixWord ++ tailWord_1256438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256438).length < 2 ^ (prefixWord ++ tailWord_1256438).sum := by decide
  have hdescent : baseEnd_1256438 < baseStart_1256438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256471 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 3, 5]
def baseStart_1256471 : Nat := 118140960795 + 1256471 * 2 ^ 59
def prefixEnd_1256471 : Nat := 4983230072969 + 3 ^ 40 * 1256471 * 2
def baseEnd_1256471 : Nat := 215057850478486261711367

theorem tailTrace_1256471 : CollatzResearch.WordTrace tailWord_1256471 prefixEnd_1256471 215057850478486261711367 := by
  unfold tailWord_1256471
  simp only [CollatzResearch.WordTrace]
  refine ⟨45827262231027630007673267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30551508154018420005115511 45827262231027630007673267)
  ·
    refine ⟨68740893346541445011509901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45827262231027630007673267 68740893346541445011509901)
    ·
      refine ⟨25777835004953041879316213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68740893346541445011509901 25777835004953041879316213)
      ·
        refine ⟨2416672031714347676185895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25777835004953041879316213 2416672031714347676185895)
        ·
          refine ⟨3625008047571521514278843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416672031714347676185895 3625008047571521514278843)
          ·
            refine ⟨5437512071357282271418265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625008047571521514278843 5437512071357282271418265)
            ·
              refine ⟨4078134053517961703563699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437512071357282271418265 4078134053517961703563699)
              ·
                refine ⟨6117201080276942555345549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4078134053517961703563699 6117201080276942555345549)
                ·
                  refine ⟨2293950405103853458254581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6117201080276942555345549 2293950405103853458254581)
                  ·
                    refine ⟨215057850478486261711367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2293950405103853458254581 215057850478486261711367)
                    ·
                      rfl

theorem cell23_1256471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_1256471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256471 prefixEnd_1256471 := by exact prefixLift 1256471
  have htrace : WordTrace (prefixWord ++ tailWord_1256471) baseStart_1256471 baseEnd_1256471 := by
    simpa [prefixWord, tailWord_1256471, baseEnd_1256471] using wordTrace_append hprefix tailTrace_1256471
  have hstable : (prefixWord ++ tailWord_1256471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256471).length < 2 ^ (prefixWord ++ tailWord_1256471).sum := by decide
  have hdescent : baseEnd_1256471 < baseStart_1256471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256485 : List Nat := [1, 3, 1, 2, 2, 2, 4, 3, 1, 1, 3]
def baseStart_1256485 : Nat := 118140960795 + 1256485 * 2 ^ 59
def prefixEnd_1256485 : Nat := 4983230072969 + 3 ^ 40 * 1256485 * 2
def baseEnd_1256485 : Nat := 645180740164621730359037

theorem tailTrace_1256485 : CollatzResearch.WordTrace tailWord_1256485 prefixEnd_1256485 645180740164621730359037 := by
  unfold tailWord_1256485
  simp only [CollatzResearch.WordTrace]
  refine ⟨45827772852976910398682909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30551848568651273599121939 45827772852976910398682909)
  ·
    refine ⟨17185414819866341399506091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45827772852976910398682909 17185414819866341399506091)
    ·
      refine ⟨25778122229799512099259137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17185414819866341399506091 25778122229799512099259137)
      ·
        refine ⟨19333591672349634074444353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25778122229799512099259137 19333591672349634074444353)
        ·
          refine ⟨14500193754262225555833265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19333591672349634074444353 14500193754262225555833265)
          ·
            refine ⟨10875145315696669166874949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14500193754262225555833265 10875145315696669166874949)
            ·
              refine ⟨2039089746693125468789053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10875145315696669166874949 2039089746693125468789053)
              ·
                refine ⟨764658655009922050795895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2039089746693125468789053 764658655009922050795895)
                ·
                  refine ⟨1146987982514883076193843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764658655009922050795895 1146987982514883076193843)
                  ·
                    refine ⟨1720481973772324614290765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1146987982514883076193843 1720481973772324614290765)
                    ·
                      refine ⟨645180740164621730359037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1720481973772324614290765 645180740164621730359037)
                      ·
                        rfl

theorem cell23_1256485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_1256485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256485 prefixEnd_1256485 := by exact prefixLift 1256485
  have htrace : WordTrace (prefixWord ++ tailWord_1256485) baseStart_1256485 baseEnd_1256485 := by
    simpa [prefixWord, tailWord_1256485, baseEnd_1256485] using wordTrace_append hprefix tailTrace_1256485
  have hstable : (prefixWord ++ tailWord_1256485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256485).length < 2 ^ (prefixWord ++ tailWord_1256485).sum := by decide
  have hdescent : baseEnd_1256485 < baseStart_1256485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256491 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 4]
def baseStart_1256491 : Nat := 118140960795 + 1256491 * 2 ^ 59
def prefixEnd_1256491 : Nat := 4983230072969 + 3 ^ 40 * 1256491 * 2
def baseEnd_1256491 : Nat := 645183821048548706884009

theorem tailTrace_1256491 : CollatzResearch.WordTrace tailWord_1256491 prefixEnd_1256491 645183821048548706884009 := by
  unfold tailWord_1256491
  simp only [CollatzResearch.WordTrace]
  refine ⟨45827991690955173423401327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30551994460636782282267551 45827991690955173423401327)
  ·
    refine ⟨68741987536432760135101991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45827991690955173423401327 68741987536432760135101991)
    ·
      refine ⟨103112981304649140202652987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68741987536432760135101991 103112981304649140202652987)
      ·
        refine ⟨154669471956973710303979481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103112981304649140202652987 154669471956973710303979481)
        ·
          refine ⟨116002103967730282727984611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154669471956973710303979481 116002103967730282727984611)
          ·
            refine ⟨174003155951595424091976917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116002103967730282727984611 174003155951595424091976917)
            ·
              refine ⟨4078198967615517752155709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 174003155951595424091976917 4078198967615517752155709)
              ·
                refine ⟨1529324612855819157058391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4078198967615517752155709 1529324612855819157058391)
                ·
                  refine ⟨2293986919283728735587587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529324612855819157058391 2293986919283728735587587)
                  ·
                    refine ⟨3440980378925593103381381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2293986919283728735587587 3440980378925593103381381)
                    ·
                      refine ⟨645183821048548706884009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3440980378925593103381381 645183821048548706884009)
                      ·
                        rfl

theorem cell23_1256491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 4].length) (baseStart_1256491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256491 prefixEnd_1256491 := by exact prefixLift 1256491
  have htrace : WordTrace (prefixWord ++ tailWord_1256491) baseStart_1256491 baseEnd_1256491 := by
    simpa [prefixWord, tailWord_1256491, baseEnd_1256491] using wordTrace_append hprefix tailTrace_1256491
  have hstable : (prefixWord ++ tailWord_1256491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256491).length < 2 ^ (prefixWord ++ tailWord_1256491).sum := by decide
  have hdescent : baseEnd_1256491 < baseStart_1256491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256502 : List Nat := [5, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_1256502 : Nat := 118140960795 + 1256502 * 2 ^ 59
def prefixEnd_1256502 : Nat := 4983230072969 + 3 ^ 40 * 1256502 * 2
def baseEnd_1256502 : Nat := 645189469335748163846459

theorem tailTrace_1256502 : CollatzResearch.WordTrace tailWord_1256502 prefixEnd_1256502 645189469335748163846459 := by
  unfold tailWord_1256502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864274555869707643878235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30552261929276881534701173 2864274555869707643878235)
  ·
    refine ⟨4296411833804561465817353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2864274555869707643878235 4296411833804561465817353)
    ·
      refine ⟨3222308875353421099363015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4296411833804561465817353 3222308875353421099363015)
      ·
        refine ⟨4833463313030131649044523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3222308875353421099363015 4833463313030131649044523)
        ·
          refine ⟨7250194969545197473566785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4833463313030131649044523 7250194969545197473566785)
          ·
            refine ⟨5437646227158898105175089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7250194969545197473566785 5437646227158898105175089)
            ·
              refine ⟨4078234670369173578881317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437646227158898105175089 4078234670369173578881317)
              ·
                refine ⟨764669000694220046040247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4078234670369173578881317 764669000694220046040247)
                ·
                  refine ⟨1147003501041330069060371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764669000694220046040247 1147003501041330069060371)
                  ·
                    refine ⟨1720505251561995103590557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1147003501041330069060371 1720505251561995103590557)
                    ·
                      refine ⟨645189469335748163846459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1720505251561995103590557 645189469335748163846459)
                      ·
                        rfl

theorem cell23_1256502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_1256502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256502 prefixEnd_1256502 := by exact prefixLift 1256502
  have htrace : WordTrace (prefixWord ++ tailWord_1256502) baseStart_1256502 baseEnd_1256502 := by
    simpa [prefixWord, tailWord_1256502, baseEnd_1256502] using wordTrace_append hprefix tailTrace_1256502
  have hstable : (prefixWord ++ tailWord_1256502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256502).length < 2 ^ (prefixWord ++ tailWord_1256502).sum := by decide
  have hdescent : baseEnd_1256502 < baseStart_1256502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256525 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1256525 : Nat := 118140960795 + 1256525 * 2 ^ 59
def prefixEnd_1256525 : Nat := 4983230072969 + 3 ^ 40 * 1256525 * 2
def baseEnd_1256525 : Nat := 645201279390801573858853

theorem tailTrace_1256525 : CollatzResearch.WordTrace tailWord_1256525 prefixEnd_1256525 645201279390801573858853 := by
  unfold tailWord_1256525
  simp only [CollatzResearch.WordTrace]
  refine ⟨45829231772831997230139029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30552821181887998153426019 45829231772831997230139029)
  ·
    refine ⟨2148245239351499870162767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45829231772831997230139029 2148245239351499870162767)
    ·
      refine ⟨3222367859027249805244151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2148245239351499870162767 3222367859027249805244151)
      ·
        refine ⟨4833551788540874707866227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3222367859027249805244151 4833551788540874707866227)
        ·
          refine ⟨7250327682811312061799341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4833551788540874707866227 7250327682811312061799341)
          ·
            refine ⟨2718872881054242023174753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7250327682811312061799341 2718872881054242023174753)
            ·
              refine ⟨2039154660790681517381065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2718872881054242023174753 2039154660790681517381065)
              ·
                refine ⟨1529365995593011138035799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2039154660790681517381065 1529365995593011138035799)
                ·
                  refine ⟨2294048993389516707053699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529365995593011138035799 2294048993389516707053699)
                  ·
                    refine ⟨3441073490084275060580549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2294048993389516707053699 3441073490084275060580549)
                    ·
                      refine ⟨645201279390801573858853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3441073490084275060580549 645201279390801573858853)
                      ·
                        rfl

theorem cell23_1256525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1256525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256525 prefixEnd_1256525 := by exact prefixLift 1256525
  have htrace : WordTrace (prefixWord ++ tailWord_1256525) baseStart_1256525 baseEnd_1256525 := by
    simpa [prefixWord, tailWord_1256525, baseEnd_1256525] using wordTrace_append hprefix tailTrace_1256525
  have hstable : (prefixWord ++ tailWord_1256525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256525).length < 2 ^ (prefixWord ++ tailWord_1256525).sum := by decide
  have hdescent : baseEnd_1256525 < baseStart_1256525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256542 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1256542 : Nat := 118140960795 + 1256542 * 2 ^ 59
def prefixEnd_1256542 : Nat := 4983230072969 + 3 ^ 40 * 1256542 * 2
def baseEnd_1256542 : Nat := 645210008561928007346275

theorem tailTrace_1256542 : CollatzResearch.WordTrace tailWord_1256542 prefixEnd_1256542 645210008561928007346275 := by
  unfold tailWord_1256542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5728731476721301141688485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30553234542513606089005253 5728731476721301141688485)
  ·
    refine ⟨1074137151885243964066591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5728731476721301141688485 1074137151885243964066591)
    ·
      refine ⟨1611205727827865946099887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1074137151885243964066591 1611205727827865946099887)
      ·
        refine ⟨2416808591741798919149831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611205727827865946099887 2416808591741798919149831)
        ·
          refine ⟨3625212887612698378724747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416808591741798919149831 3625212887612698378724747)
          ·
            refine ⟨5437819331419047568087121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625212887612698378724747 5437819331419047568087121)
            ·
              refine ⟨4078364498564285676065341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437819331419047568087121 4078364498564285676065341)
              ·
                refine ⟨1529386686961607128524503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4078364498564285676065341 1529386686961607128524503)
                ·
                  refine ⟨2294080030442410692786755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529386686961607128524503 2294080030442410692786755)
                  ·
                    refine ⟨3441120045663616039180133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2294080030442410692786755 3441120045663616039180133)
                    ·
                      refine ⟨645210008561928007346275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3441120045663616039180133 645210008561928007346275)
                      ·
                        rfl

theorem cell23_1256542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1256542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256542 prefixEnd_1256542 := by exact prefixLift 1256542
  have htrace : WordTrace (prefixWord ++ tailWord_1256542) baseStart_1256542 baseEnd_1256542 := by
    simpa [prefixWord, tailWord_1256542, baseEnd_1256542] using wordTrace_append hprefix tailTrace_1256542
  have hstable : (prefixWord ++ tailWord_1256542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256542).length < 2 ^ (prefixWord ++ tailWord_1256542).sum := by decide
  have hdescent : baseEnd_1256542 < baseStart_1256542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256585 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 1, 3, 2]
def baseStart_1256585 : Nat := 118140960795 + 1256585 * 2 ^ 59
def prefixEnd_1256585 : Nat := 4983230072969 + 3 ^ 40 * 1256585 * 2
def baseEnd_1256585 : Nat := 645232088230071339108577

theorem tailTrace_1256585 : CollatzResearch.WordTrace tailWord_1256585 prefixEnd_1256585 645232088230071339108577 := by
  unfold tailWord_1256585
  simp only [CollatzResearch.WordTrace]
  refine ⟨45831420152614627477323209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30554280101743084984882139 45831420152614627477323209)
  ·
    refine ⟨34373565114460970607992407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45831420152614627477323209 34373565114460970607992407)
    ·
      refine ⟨51560347671691455911988611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34373565114460970607992407 51560347671691455911988611)
      ·
        refine ⟨77340521507537183867982917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51560347671691455911988611 77340521507537183867982917)
        ·
          refine ⟨14501347782663221975246797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77340521507537183867982917 14501347782663221975246797)
          ·
            refine ⟨5438005418498708240717549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14501347782663221975246797 5438005418498708240717549)
            ·
              refine ⟨2039252031937015590269081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5438005418498708240717549 2039252031937015590269081)
              ·
                refine ⟨1529439023952761692701811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2039252031937015590269081 1529439023952761692701811)
                ·
                  refine ⟨2294158535929142539052717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529439023952761692701811 2294158535929142539052717)
                  ·
                    refine ⟨860309450973428452144769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294158535929142539052717 860309450973428452144769)
                    ·
                      refine ⟨645232088230071339108577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860309450973428452144769 645232088230071339108577)
                      ·
                        rfl

theorem cell23_1256585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 3, 2].length) (baseStart_1256585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256585 prefixEnd_1256585 := by exact prefixLift 1256585
  have htrace : WordTrace (prefixWord ++ tailWord_1256585) baseStart_1256585 baseEnd_1256585 := by
    simpa [prefixWord, tailWord_1256585, baseEnd_1256585] using wordTrace_append hprefix tailTrace_1256585
  have hstable : (prefixWord ++ tailWord_1256585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256585).length < 2 ^ (prefixWord ++ tailWord_1256585).sum := by decide
  have hdescent : baseEnd_1256585 < baseStart_1256585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256638 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_1256638 : Nat := 118140960795 + 1256638 * 2 ^ 59
def prefixEnd_1256638 : Nat := 4983230072969 + 3 ^ 40 * 1256638 * 2
def baseEnd_1256638 : Nat := 71695478078306625749537

theorem tailTrace_1256638 : CollatzResearch.WordTrace tailWord_1256638 prefixEnd_1256638 71695478078306625749537 := by
  unfold tailWord_1256638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5729169152677827191125321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30555568814281745019335045 5729169152677827191125321)
  ·
    refine ⟨4296876864508370393343991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5729169152677827191125321 4296876864508370393343991)
    ·
      refine ⟨6445315296762555590015987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4296876864508370393343991 6445315296762555590015987)
      ·
        refine ⟨9667972945143833385023981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6445315296762555590015987 9667972945143833385023981)
        ·
          refine ⟨3625489854428937519383993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9667972945143833385023981 3625489854428937519383993)
          ·
            refine ⟨2719117390821703139537995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3625489854428937519383993 2719117390821703139537995)
            ·
              refine ⟨4078676086232554709306993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719117390821703139537995 4078676086232554709306993)
              ·
                refine ⟨3059007064674416031980245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4078676086232554709306993 3059007064674416031980245)
                ·
                  refine ⟨71695478078306625749537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3059007064674416031980245 71695478078306625749537)
                  ·
                    rfl

theorem cell23_1256638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_1256638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256638 prefixEnd_1256638 := by exact prefixLift 1256638
  have htrace : WordTrace (prefixWord ++ tailWord_1256638) baseStart_1256638 baseEnd_1256638 := by
    simpa [prefixWord, tailWord_1256638, baseEnd_1256638] using wordTrace_append hprefix tailTrace_1256638
  have hstable : (prefixWord ++ tailWord_1256638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256638).length < 2 ^ (prefixWord ++ tailWord_1256638).sum := by decide
  have hdescent : baseEnd_1256638 < baseStart_1256638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256651 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 2, 5]
def baseStart_1256651 : Nat := 118140960795 + 1256651 * 2 ^ 59
def prefixEnd_1256651 : Nat := 4983230072969 + 3 ^ 40 * 1256651 * 2
def baseEnd_1256651 : Nat := 215088659317756026961091

theorem tailTrace_1256651 : CollatzResearch.WordTrace tailWord_1256651 prefixEnd_1256651 215088659317756026961091 := by
  unfold tailWord_1256651
  simp only [CollatzResearch.WordTrace]
  refine ⟨45833827370375520749225807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30555884913583680499483871 45833827370375520749225807)
  ·
    refine ⟨68750741055563281123838711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45833827370375520749225807 68750741055563281123838711)
    ·
      refine ⟨103126111583344921685758067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68750741055563281123838711 103126111583344921685758067)
      ·
        refine ⟨154689167375017382528637101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103126111583344921685758067 154689167375017382528637101)
        ·
          refine ⟨58008437765631518448238913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154689167375017382528637101 58008437765631518448238913)
          ·
            refine ⟨43506328324223638836179185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58008437765631518448238913 43506328324223638836179185)
            ·
              refine ⟨32629746243167729127134389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43506328324223638836179185 32629746243167729127134389)
              ·
                refine ⟨3059038710296974605668849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32629746243167729127134389 3059038710296974605668849)
                ·
                  refine ⟨2294279032722730954251637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3059038710296974605668849 2294279032722730954251637)
                  ·
                    refine ⟨215088659317756026961091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2294279032722730954251637 215088659317756026961091)
                    ·
                      rfl

theorem cell23_1256651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 5].length) (baseStart_1256651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256651 prefixEnd_1256651 := by exact prefixLift 1256651
  have htrace : WordTrace (prefixWord ++ tailWord_1256651) baseStart_1256651 baseEnd_1256651 := by
    simpa [prefixWord, tailWord_1256651, baseEnd_1256651] using wordTrace_append hprefix tailTrace_1256651
  have hstable : (prefixWord ++ tailWord_1256651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256651).length < 2 ^ (prefixWord ++ tailWord_1256651).sum := by decide
  have hdescent : baseEnd_1256651 < baseStart_1256651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256653 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_1256653 : Nat := 118140960795 + 1256653 * 2 ^ 59
def prefixEnd_1256653 : Nat := 4983230072969 + 3 ^ 40 * 1256653 * 2
def baseEnd_1256653 : Nat := 645267004914577073058265

theorem tailTrace_1256653 : CollatzResearch.WordTrace tailWord_1256653 prefixEnd_1256653 645267004914577073058265 := by
  unfold tailWord_1256653
  simp only [CollatzResearch.WordTrace]
  refine ⟨45833900316368275090798613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30555933544245516727199075 45833900316368275090798613)
  ·
    refine ⟨2148464077329762894881185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45833900316368275090798613 2148464077329762894881185)
    ·
      refine ⟨1611348057997322171160889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2148464077329762894881185 1611348057997322171160889)
      ·
        refine ⟨1208511043497991628370667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1611348057997322171160889 1208511043497991628370667)
        ·
          refine ⟨1812766565246987442556001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208511043497991628370667 1812766565246987442556001)
          ·
            refine ⟨1359574923935240581917001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1812766565246987442556001 1359574923935240581917001)
            ·
              refine ⟨1019681192951430436437751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359574923935240581917001 1019681192951430436437751)
              ·
                refine ⟨1529521789427145654656627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019681192951430436437751 1529521789427145654656627)
                ·
                  refine ⟨2294282684140718481984941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529521789427145654656627 2294282684140718481984941)
                  ·
                    refine ⟨860356006552769430744353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294282684140718481984941 860356006552769430744353)
                    ·
                      refine ⟨645267004914577073058265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860356006552769430744353 645267004914577073058265)
                      ·
                        rfl

theorem cell23_1256653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_1256653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256653 prefixEnd_1256653 := by exact prefixLift 1256653
  have htrace : WordTrace (prefixWord ++ tailWord_1256653) baseStart_1256653 baseEnd_1256653 := by
    simpa [prefixWord, tailWord_1256653, baseEnd_1256653] using wordTrace_append hprefix tailTrace_1256653
  have hstable : (prefixWord ++ tailWord_1256653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256653).length < 2 ^ (prefixWord ++ tailWord_1256653).sum := by decide
  have hdescent : baseEnd_1256653 < baseStart_1256653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256698 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_1256698 : Nat := 118140960795 + 1256698 * 2 ^ 59
def prefixEnd_1256698 : Nat := 4983230072969 + 3 ^ 40 * 1256698 * 2
def baseEnd_1256698 : Nat := 215096703848009798998519

theorem tailTrace_1256698 : CollatzResearch.WordTrace tailWord_1256698 prefixEnd_1256698 215096703848009798998519 := by
  unfold tailWord_1256698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11458885400301311944046687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30557027734136831850791165 11458885400301311944046687)
  ·
    refine ⟨17188328100451967916070031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11458885400301311944046687 17188328100451967916070031)
    ·
      refine ⟨25782492150677951874105047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17188328100451967916070031 25782492150677951874105047)
      ·
        refine ⟨38673738226016927811157571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25782492150677951874105047 38673738226016927811157571)
        ·
          refine ⟨58010607339025391716736357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38673738226016927811157571 58010607339025391716736357)
          ·
            refine ⟨10876988876067260946888067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58010607339025391716736357 10876988876067260946888067)
            ·
              refine ⟨16315483314100891420332101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10876988876067260946888067 16315483314100891420332101)
              ·
                refine ⟨3059153121393917141312269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16315483314100891420332101 3059153121393917141312269)
                ·
                  refine ⟨1147182420522718927992101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3059153121393917141312269 1147182420522718927992101)
                  ·
                    refine ⟨215096703848009798998519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1147182420522718927992101 215096703848009798998519)
                    ·
                      rfl

theorem cell23_1256698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_1256698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256698 prefixEnd_1256698 := by exact prefixLift 1256698
  have htrace : WordTrace (prefixWord ++ tailWord_1256698) baseStart_1256698 baseEnd_1256698 := by
    simpa [prefixWord, tailWord_1256698, baseEnd_1256698] using wordTrace_append hprefix tailTrace_1256698
  have hstable : (prefixWord ++ tailWord_1256698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256698).length < 2 ^ (prefixWord ++ tailWord_1256698).sum := by decide
  have hdescent : baseEnd_1256698 < baseStart_1256698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256788 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1256788 : Nat := 118140960795 + 1256788 * 2 ^ 59
def prefixEnd_1256788 : Nat := 4983230072969 + 3 ^ 40 * 1256788 * 2
def baseEnd_1256788 : Nat := 215112108267644681623381

theorem tailTrace_1256788 : CollatzResearch.WordTrace tailWord_1256788 prefixEnd_1256788 215112108267644681623381 := by
  unfold tailWord_1256788
  simp only [CollatzResearch.WordTrace]
  refine ⟨22919412085439596573481509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30559216113919462097975345 22919412085439596573481509)
  ·
    refine ⟨4297389766019924357527783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22919412085439596573481509 4297389766019924357527783)
    ·
      refine ⟨6446084649029886536291675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4297389766019924357527783 6446084649029886536291675)
      ·
        refine ⟨9669126973544829804437513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6446084649029886536291675 9669126973544829804437513)
        ·
          refine ⟨7251845230158622353328135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9669126973544829804437513 7251845230158622353328135)
          ·
            refine ⟨10877767845237933529992203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7251845230158622353328135 10877767845237933529992203)
            ·
              refine ⟨16316651767856900294988305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10877767845237933529992203 16316651767856900294988305)
              ·
                refine ⟨12237488825892675221241229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16316651767856900294988305 12237488825892675221241229)
                ·
                  refine ⟨4589058309709753207965461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12237488825892675221241229 4589058309709753207965461)
                  ·
                    refine ⟨215112108267644681623381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4589058309709753207965461 215112108267644681623381)
                    ·
                      rfl

theorem cell23_1256788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1256788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256788 prefixEnd_1256788 := by exact prefixLift 1256788
  have htrace : WordTrace (prefixWord ++ tailWord_1256788) baseStart_1256788 baseEnd_1256788 := by
    simpa [prefixWord, tailWord_1256788, baseEnd_1256788] using wordTrace_append hprefix tailTrace_1256788
  have hstable : (prefixWord ++ tailWord_1256788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256788).length < 2 ^ (prefixWord ++ tailWord_1256788).sum := by decide
  have hdescent : baseEnd_1256788 < baseStart_1256788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256789 : List Nat := [1, 3, 2, 2, 3, 2, 1, 4, 1, 1, 3]
def baseStart_1256789 : Nat := 118140960795 + 1256789 * 2 ^ 59
def prefixEnd_1256789 : Nat := 4983230072969 + 3 ^ 40 * 1256789 * 2
def baseEnd_1256789 : Nat := 645336838283588540957639

theorem tailTrace_1256789 : CollatzResearch.WordTrace tailWord_1256789 prefixEnd_1256789 645336838283588540957639 := by
  unfold tailWord_1256789
  simp only [CollatzResearch.WordTrace]
  refine ⟨45838860643875570317749421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30559240429250380211832947 45838860643875570317749421)
  ·
    refine ⟨17189572741453338869156033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45838860643875570317749421 17189572741453338869156033)
    ·
      refine ⟨12892179556090004151867025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17189572741453338869156033 12892179556090004151867025)
      ·
        refine ⟨9669134667067503113900269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12892179556090004151867025 9669134667067503113900269)
        ·
          refine ⟨3625925500150313667712601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9669134667067503113900269 3625925500150313667712601)
          ·
            refine ⟨2719444125112735250784451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3625925500150313667712601 2719444125112735250784451)
            ·
              refine ⟨4079166187669102876176677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719444125112735250784451 4079166187669102876176677)
              ·
                refine ⟨764843660187956789283127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4079166187669102876176677 764843660187956789283127)
                ·
                  refine ⟨1147265490281935183924691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764843660187956789283127 1147265490281935183924691)
                  ·
                    refine ⟨1720898235422902775887037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1147265490281935183924691 1720898235422902775887037)
                    ·
                      refine ⟨645336838283588540957639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1720898235422902775887037 645336838283588540957639)
                      ·
                        rfl

theorem cell23_1256789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_1256789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256789 prefixEnd_1256789 := by exact prefixLift 1256789
  have htrace : WordTrace (prefixWord ++ tailWord_1256789) baseStart_1256789 baseEnd_1256789 := by
    simpa [prefixWord, tailWord_1256789, baseEnd_1256789] using wordTrace_append hprefix tailTrace_1256789
  have hstable : (prefixWord ++ tailWord_1256789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256789).length < 2 ^ (prefixWord ++ tailWord_1256789).sum := by decide
  have hdescent : baseEnd_1256789 < baseStart_1256789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256805 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_1256805 : Nat := 118140960795 + 1256805 * 2 ^ 59
def prefixEnd_1256805 : Nat := 4983230072969 + 3 ^ 40 * 1256805 * 2
def baseEnd_1256805 : Nat := 215115017991353492785855

theorem tailTrace_1256805 : CollatzResearch.WordTrace tailWord_1256805 prefixEnd_1256805 215115017991353492785855 := by
  unfold tailWord_1256805
  simp only [CollatzResearch.WordTrace]
  refine ⟨45839444211817605050331869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30559629474545070033554579 45839444211817605050331869)
  ·
    refine ⟨17189791579431601893874451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45839444211817605050331869 17189791579431601893874451)
    ·
      refine ⟨25784687369147402840811677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17189791579431601893874451 25784687369147402840811677)
      ·
        refine ⟨9669257763430276065304379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25784687369147402840811677 9669257763430276065304379)
        ·
          refine ⟨14503886645145414097956569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9669257763430276065304379 14503886645145414097956569)
          ·
            refine ⟨10877914983859060573467427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14503886645145414097956569 10877914983859060573467427)
            ·
              refine ⟨16316872475788590860201141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10877914983859060573467427 16316872475788590860201141)
              ·
                refine ⟨1529706794605180393143857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16316872475788590860201141 1529706794605180393143857)
                ·
                  refine ⟨1147280095953885294857893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1529706794605180393143857 1147280095953885294857893)
                  ·
                    refine ⟨215115017991353492785855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1147280095953885294857893 215115017991353492785855)
                    ·
                      rfl

theorem cell23_1256805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_1256805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256805 prefixEnd_1256805 := by exact prefixLift 1256805
  have htrace : WordTrace (prefixWord ++ tailWord_1256805) baseStart_1256805 baseEnd_1256805 := by
    simpa [prefixWord, tailWord_1256805, baseEnd_1256805] using wordTrace_append hprefix tailTrace_1256805
  have hstable : (prefixWord ++ tailWord_1256805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256805).length < 2 ^ (prefixWord ++ tailWord_1256805).sum := by decide
  have hdescent : baseEnd_1256805 < baseStart_1256805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256812 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 5, 2, 2]
def baseStart_1256812 : Nat := 118140960795 + 1256812 * 2 ^ 59
def prefixEnd_1256812 : Nat := 4983230072969 + 3 ^ 40 * 1256812 * 2
def baseEnd_1256812 : Nat := 645348648338641950970033

theorem tailTrace_1256812 : CollatzResearch.WordTrace tailWord_1256812 prefixEnd_1256812 645348648338641950970033 := by
  unfold tailWord_1256812
  simp only [CollatzResearch.WordTrace]
  refine ⟨22919849761396122622918345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30559799681861496830557793 22919849761396122622918345)
  ·
    refine ⟨17189887321047091967188759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22919849761396122622918345 17189887321047091967188759)
    ·
      refine ⟨25784830981570637950783139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17189887321047091967188759 25784830981570637950783139)
      ·
        refine ⟨38677246472355956926174709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25784830981570637950783139 38677246472355956926174709)
        ·
          refine ⟨3625991856783370961828879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38677246472355956926174709 3625991856783370961828879)
          ·
            refine ⟨5438987785175056442743319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625991856783370961828879 5438987785175056442743319)
            ·
              refine ⟨8158481677762584664114979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5438987785175056442743319 8158481677762584664114979)
              ·
                refine ⟨12237722516643876996172469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8158481677762584664114979 12237722516643876996172469)
                ·
                  refine ⟨1147286485935363468391169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12237722516643876996172469 1147286485935363468391169)
                  ·
                    refine ⟨860464864451522601293377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1147286485935363468391169 860464864451522601293377)
                    ·
                      refine ⟨645348648338641950970033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860464864451522601293377 645348648338641950970033)
                      ·
                        rfl

theorem cell23_1256812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_1256812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256812 prefixEnd_1256812 := by exact prefixLift 1256812
  have htrace : WordTrace (prefixWord ++ tailWord_1256812) baseStart_1256812 baseEnd_1256812 := by
    simpa [prefixWord, tailWord_1256812, baseEnd_1256812] using wordTrace_append hprefix tailTrace_1256812
  have hstable : (prefixWord ++ tailWord_1256812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256812).length < 2 ^ (prefixWord ++ tailWord_1256812).sum := by decide
  have hdescent : baseEnd_1256812 < baseStart_1256812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256815 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 3]
def baseStart_1256815 : Nat := 118140960795 + 1256815 * 2 ^ 59
def prefixEnd_1256815 : Nat := 4983230072969 + 3 ^ 40 * 1256815 * 2
def baseEnd_1256815 : Nat := 645350188780605439232519

theorem tailTrace_1256815 : CollatzResearch.WordTrace tailWord_1256815 prefixEnd_1256815 645350188780605439232519 := by
  unfold tailWord_1256815
  simp only [CollatzResearch.WordTrace]
  refine ⟨45839808941781376758195899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30559872627854251172130599 45839808941781376758195899)
  ·
    refine ⟨68759713412672065137293849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45839808941781376758195899 68759713412672065137293849)
    ·
      refine ⟨51569785059504048852970387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68759713412672065137293849 51569785059504048852970387)
      ·
        refine ⟨77354677589256073279455581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51569785059504048852970387 77354677589256073279455581)
        ·
          refine ⟨29008004095971027479795843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77354677589256073279455581 29008004095971027479795843)
          ·
            refine ⟨43512006143956541219693765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29008004095971027479795843 43512006143956541219693765)
            ·
              refine ⟨8158501151991851478692581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43512006143956541219693765 8158501151991851478692581)
              ·
                refine ⟨1529718965998472152254859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8158501151991851478692581 1529718965998472152254859)
                ·
                  refine ⟨2294578448997708228382289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529718965998472152254859 2294578448997708228382289)
                  ·
                    refine ⟨1720933836748281171286717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2294578448997708228382289 1720933836748281171286717)
                    ·
                      refine ⟨645350188780605439232519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1720933836748281171286717 645350188780605439232519)
                      ·
                        rfl

theorem cell23_1256815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 3].length) (baseStart_1256815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256815 prefixEnd_1256815 := by exact prefixLift 1256815
  have htrace : WordTrace (prefixWord ++ tailWord_1256815) baseStart_1256815 baseEnd_1256815 := by
    simpa [prefixWord, tailWord_1256815, baseEnd_1256815] using wordTrace_append hprefix tailTrace_1256815
  have hstable : (prefixWord ++ tailWord_1256815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256815).length < 2 ^ (prefixWord ++ tailWord_1256815).sum := by decide
  have hdescent : baseEnd_1256815 < baseStart_1256815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256846 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1256846 : Nat := 118140960795 + 1256846 * 2 ^ 59
def prefixEnd_1256846 : Nat := 4983230072969 + 3 ^ 40 * 1256846 * 2
def baseEnd_1256846 : Nat := 645366106680894817944877

theorem tailTrace_1256846 : CollatzResearch.WordTrace tailWord_1256846 prefixEnd_1256846 645366106680894817944877 := by
  unfold tailWord_1256846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5730117450583633631571799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30560626403112712701716261 5730117450583633631571799)
  ·
    refine ⟨8595176175875450447357699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5730117450583633631571799 8595176175875450447357699)
    ·
      refine ⟨12892764263813175671036549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8595176175875450447357699 12892764263813175671036549)
      ·
        refine ⟨2417393299464970438319353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12892764263813175671036549 2417393299464970438319353)
        ·
          refine ⟨1813044974598727828739515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2417393299464970438319353 1813044974598727828739515)
          ·
            refine ⟨2719567461898091743109273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813044974598727828739515 2719567461898091743109273)
            ·
              refine ⟨2039675596423568807331955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2719567461898091743109273 2039675596423568807331955)
              ·
                refine ⟨3059513394635353210997933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039675596423568807331955 3059513394635353210997933)
                ·
                  refine ⟨1147317522988257454124225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3059513394635353210997933 1147317522988257454124225)
                  ·
                    refine ⟨860488142241193090593169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1147317522988257454124225 860488142241193090593169)
                    ·
                      refine ⟨645366106680894817944877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860488142241193090593169 645366106680894817944877)
                      ·
                        rfl

theorem cell23_1256846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1256846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256846 prefixEnd_1256846 := by exact prefixLift 1256846
  have htrace : WordTrace (prefixWord ++ tailWord_1256846) baseStart_1256846 baseEnd_1256846 := by
    simpa [prefixWord, tailWord_1256846, baseEnd_1256846] using wordTrace_append hprefix tailTrace_1256846
  have hstable : (prefixWord ++ tailWord_1256846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256846).length < 2 ^ (prefixWord ++ tailWord_1256846).sum := by decide
  have hdescent : baseEnd_1256846 < baseStart_1256846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256888 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1256888 : Nat := 118140960795 + 1256888 * 2 ^ 59
def prefixEnd_1256888 : Nat := 4983230072969 + 3 ^ 40 * 1256888 * 2
def baseEnd_1256888 : Nat := 645387672868383653619683

theorem tailTrace_1256888 : CollatzResearch.WordTrace tailWord_1256888 prefixEnd_1256888 645387672868383653619683 := by
  unfold tailWord_1256888
  simp only [CollatzResearch.WordTrace]
  refine ⟨22921235735258455112801659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30561647647011273483735545 22921235735258455112801659)
  ·
    refine ⟨34381853602887682669202489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22921235735258455112801659 34381853602887682669202489)
    ·
      refine ⟨25786390202165762001901867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34381853602887682669202489 25786390202165762001901867)
      ·
        refine ⟨38679585303248643002852801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25786390202165762001901867 38679585303248643002852801)
        ·
          refine ⟨29009688977436482252139601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38679585303248643002852801 29009688977436482252139601)
          ·
            refine ⟨21757266733077361689104701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29009688977436482252139601 21757266733077361689104701)
            ·
              refine ⟨8158975024904010633414263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21757266733077361689104701 8158975024904010633414263)
              ·
                refine ⟨12238462537356015950121395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8158975024904010633414263 12238462537356015950121395)
                ·
                  refine ⟨18357693806034023925182093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12238462537356015950121395 18357693806034023925182093)
                  ·
                    refine ⟨6884135177262758971943285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18357693806034023925182093 6884135177262758971943285)
                    ·
                      refine ⟨645387672868383653619683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6884135177262758971943285 645387672868383653619683)
                      ·
                        rfl

theorem cell23_1256888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1256888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256888 prefixEnd_1256888 := by exact prefixLift 1256888
  have htrace : WordTrace (prefixWord ++ tailWord_1256888) baseStart_1256888 baseEnd_1256888 := by
    simpa [prefixWord, tailWord_1256888, baseEnd_1256888] using wordTrace_append hprefix tailTrace_1256888
  have hstable : (prefixWord ++ tailWord_1256888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256888).length < 2 ^ (prefixWord ++ tailWord_1256888).sum := by decide
  have hdescent : baseEnd_1256888 < baseStart_1256888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256942 : List Nat := [4, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_1256942 : Nat := 118140960795 + 1256942 * 2 ^ 59
def prefixEnd_1256942 : Nat := 4983230072969 + 3 ^ 40 * 1256942 * 2
def baseEnd_1256942 : Nat := 71712822313747382482715

theorem tailTrace_1256942 : CollatzResearch.WordTrace tailWord_1256942 prefixEnd_1256942 71712822313747382482715 := by
  unfold tailWord_1256942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5730555126540159681008635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30562960674880851632046053 5730555126540159681008635)
  ·
    refine ⟨8595832689810239521512953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5730555126540159681008635 8595832689810239521512953)
    ·
      refine ⟨6446874517357679641134715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8595832689810239521512953 6446874517357679641134715)
      ·
        refine ⟨9670311776036519461702073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6446874517357679641134715 9670311776036519461702073)
        ·
          refine ⟨7252733832027389596276555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9670311776036519461702073 7252733832027389596276555)
          ·
            refine ⟨10879100748041084394414833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7252733832027389596276555 10879100748041084394414833)
            ·
              refine ⟨8159325561030813295811125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10879100748041084394414833 8159325561030813295811125)
              ·
                refine ⟨764936771346638746482293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8159325561030813295811125 764936771346638746482293)
                ·
                  refine ⟨71712822313747382482715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 764936771346638746482293 71712822313747382482715)
                  ·
                    rfl

theorem cell23_1256942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_1256942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256942 prefixEnd_1256942 := by exact prefixLift 1256942
  have htrace : WordTrace (prefixWord ++ tailWord_1256942) baseStart_1256942 baseEnd_1256942 := by
    simpa [prefixWord, tailWord_1256942, baseEnd_1256942] using wordTrace_append hprefix tailTrace_1256942
  have hstable : (prefixWord ++ tailWord_1256942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256942).length < 2 ^ (prefixWord ++ tailWord_1256942).sum := by decide
  have hdescent : baseEnd_1256942 < baseStart_1256942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256992 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1256992 : Nat := 118140960795 + 1256992 * 2 ^ 59
def prefixEnd_1256992 : Nat := 4983230072969 + 3 ^ 40 * 1256992 * 2
def baseEnd_1256992 : Nat := 645441074856451246719205

theorem tailTrace_1256992 : CollatzResearch.WordTrace tailWord_1256992 prefixEnd_1256992 645441074856451246719205 := by
  unfold tailWord_1256992
  simp only [CollatzResearch.WordTrace]
  refine ⟨22923132331070067993694615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30564176441426757324926153 22923132331070067993694615)
  ·
    refine ⟨34384698496605101990541923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22923132331070067993694615 34384698496605101990541923)
    ·
      refine ⟨51577047744907652985812885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34384698496605101990541923 51577047744907652985812885)
      ·
        refine ⟨2417674113042546233709979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51577047744907652985812885 2417674113042546233709979)
        ·
          refine ⟨3626511169563819350564969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417674113042546233709979 3626511169563819350564969)
          ·
            refine ⟨2719883377172864512923727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3626511169563819350564969 2719883377172864512923727)
            ·
              refine ⟨4079825065759296769385591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719883377172864512923727 4079825065759296769385591)
              ·
                refine ⟨6119737598638945154078387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079825065759296769385591 6119737598638945154078387)
                ·
                  refine ⟨9179606397958417731117581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6119737598638945154078387 9179606397958417731117581)
                  ·
                    refine ⟨3442352399234406649169093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9179606397958417731117581 3442352399234406649169093)
                    ·
                      refine ⟨645441074856451246719205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3442352399234406649169093 645441074856451246719205)
                      ·
                        rfl

theorem cell23_1256992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1256992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1256992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1256992 prefixEnd_1256992 := by exact prefixLift 1256992
  have htrace : WordTrace (prefixWord ++ tailWord_1256992) baseStart_1256992 baseEnd_1256992 := by
    simpa [prefixWord, tailWord_1256992, baseEnd_1256992] using wordTrace_append hprefix tailTrace_1256992
  have hstable : (prefixWord ++ tailWord_1256992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256992).length < 2 ^ (prefixWord ++ tailWord_1256992).sum := by decide
  have hdescent : baseEnd_1256992 < baseStart_1256992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257002 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1257002 : Nat := 118140960795 + 1257002 * 2 ^ 59
def prefixEnd_1257002 : Nat := 4983230072969 + 3 ^ 40 * 1257002 * 2
def baseEnd_1257002 : Nat := 215148736554332069198053

theorem tailTrace_1257002 : CollatzResearch.WordTrace tailWord_1257002 prefixEnd_1257002 215148736554332069198053 := by
  unfold tailWord_1257002
  simp only [CollatzResearch.WordTrace]
  refine ⟨11461657348025976923813315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30564419594735938463502173 11461657348025976923813315)
  ·
    refine ⟨17192486022038965385719973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11461657348025976923813315 17192486022038965385719973)
    ·
      refine ⟨3223591129132306009822495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17192486022038965385719973 3223591129132306009822495)
      ·
        refine ⟨4835386693698459014733743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3223591129132306009822495 4835386693698459014733743)
        ·
          refine ⟨7253080040547688522100615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4835386693698459014733743 7253080040547688522100615)
          ·
            refine ⟨10879620060821532783150923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7253080040547688522100615 10879620060821532783150923)
            ·
              refine ⟨16319430091232299174726385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10879620060821532783150923 16319430091232299174726385)
              ·
                refine ⟨12239572568424224381044789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16319430091232299174726385 12239572568424224381044789)
                ·
                  refine ⟨1147459928289771035722949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12239572568424224381044789 1147459928289771035722949)
                  ·
                    refine ⟨215148736554332069198053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1147459928289771035722949 215148736554332069198053)
                    ·
                      rfl

theorem cell23_1257002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1257002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257002 prefixEnd_1257002 := by exact prefixLift 1257002
  have htrace : WordTrace (prefixWord ++ tailWord_1257002) baseStart_1257002 baseEnd_1257002 := by
    simpa [prefixWord, tailWord_1257002, baseEnd_1257002] using wordTrace_append hprefix tailTrace_1257002
  have hstable : (prefixWord ++ tailWord_1257002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257002).length < 2 ^ (prefixWord ++ tailWord_1257002).sum := by decide
  have hdescent : baseEnd_1257002 < baseStart_1257002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257015 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 8]
def baseStart_1257015 : Nat := 118140960795 + 1257015 * 2 ^ 59
def prefixEnd_1257015 : Nat := 4983230072969 + 3 ^ 40 * 1257015 * 2
def baseEnd_1257015 : Nat := 71716987212389406303511

theorem tailTrace_1257015 : CollatzResearch.WordTrace tailWord_1257015 prefixEnd_1257015 71716987212389406303511 := by
  unfold tailWord_1257015
  simp only [CollatzResearch.WordTrace]
  refine ⟨45847103541056810915476499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30564735694037873943650999 45847103541056810915476499)
  ·
    refine ⟨68770655311585216373214749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45847103541056810915476499 68770655311585216373214749)
    ·
      refine ⟨25788995741844456139955531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68770655311585216373214749 25788995741844456139955531)
      ·
        refine ⟨38683493612766684209933297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25788995741844456139955531 38683493612766684209933297)
        ·
          refine ⟨29012620209575013157449973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38683493612766684209933297 29012620209575013157449973)
          ·
            refine ⟨2719933144647657483510935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29012620209575013157449973 2719933144647657483510935)
            ·
              refine ⟨4079899716971486225266403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719933144647657483510935 4079899716971486225266403)
              ·
                refine ⟨6119849575457229337899605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079899716971486225266403 6119849575457229337899605)
                ·
                  refine ⟨71716987212389406303511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6119849575457229337899605 71716987212389406303511)
                  ·
                    rfl

theorem cell23_1257015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 8].length) (baseStart_1257015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257015 prefixEnd_1257015 := by exact prefixLift 1257015
  have htrace : WordTrace (prefixWord ++ tailWord_1257015) baseStart_1257015 baseEnd_1257015 := by
    simpa [prefixWord, tailWord_1257015, baseEnd_1257015] using wordTrace_append hprefix tailTrace_1257015
  have hstable : (prefixWord ++ tailWord_1257015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257015).length < 2 ^ (prefixWord ++ tailWord_1257015).sum := by decide
  have hdescent : baseEnd_1257015 < baseStart_1257015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257082 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2]
def baseStart_1257082 : Nat := 118140960795 + 1257082 * 2 ^ 59
def prefixEnd_1257082 : Nat := 4983230072969 + 3 ^ 40 * 1257082 * 2
def baseEnd_1257082 : Nat := 645487288115355894593791

theorem tailTrace_1257082 : CollatzResearch.WordTrace tailWord_1257082 prefixEnd_1257082 645487288115355894593791 := by
  unfold tailWord_1257082
  simp only [CollatzResearch.WordTrace]
  refine ⟨11462386807953520339541375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30566364821209387572110333 11462386807953520339541375)
  ·
    refine ⟨17193580211930280509312063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11462386807953520339541375 17193580211930280509312063)
    ·
      refine ⟨25790370317895420763968095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17193580211930280509312063 25790370317895420763968095)
      ·
        refine ⟨38685555476843131145952143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25790370317895420763968095 38685555476843131145952143)
        ·
          refine ⟨58028333215264696718928215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38685555476843131145952143 58028333215264696718928215)
          ·
            refine ⟨87042499822897045078392323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58028333215264696718928215 87042499822897045078392323)
            ·
              refine ⟨130563749734345567617588485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87042499822897045078392323 130563749734345567617588485)
              ·
                refine ⟨24480703075189793928297841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130563749734345567617588485 24480703075189793928297841)
                ·
                  refine ⟨18360527306392345446223381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24480703075189793928297841 18360527306392345446223381)
                  ·
                    refine ⟨860649717487141192791721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18360527306392345446223381 860649717487141192791721)
                    ·
                      refine ⟨645487288115355894593791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860649717487141192791721 645487288115355894593791)
                      ·
                        rfl

theorem cell23_1257082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_1257082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257082 prefixEnd_1257082 := by exact prefixLift 1257082
  have htrace : WordTrace (prefixWord ++ tailWord_1257082) baseStart_1257082 baseEnd_1257082 := by
    simpa [prefixWord, tailWord_1257082, baseEnd_1257082] using wordTrace_append hprefix tailTrace_1257082
  have hstable : (prefixWord ++ tailWord_1257082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257082).length < 2 ^ (prefixWord ++ tailWord_1257082).sum := by decide
  have hdescent : baseEnd_1257082 < baseStart_1257082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257099 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 5, 2, 2]
def baseStart_1257099 : Nat := 118140960795 + 1257099 * 2 ^ 59
def prefixEnd_1257099 : Nat := 4983230072969 + 3 ^ 40 * 1257099 * 2
def baseEnd_1257099 : Nat := 645496017286482328081213

theorem tailTrace_1257099 : CollatzResearch.WordTrace tailWord_1257099 prefixEnd_1257099 645496017286482328081213 := by
  unfold tailWord_1257099
  simp only [CollatzResearch.WordTrace]
  refine ⟨45850167272752493261534351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30566778181834995507689567 45850167272752493261534351)
  ·
    refine ⟨68775250909128739892301527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45850167272752493261534351 68775250909128739892301527)
    ·
      refine ⟨103162876363693109838452291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68775250909128739892301527 103162876363693109838452291)
      ·
        refine ⟨154744314545539664757678437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103162876363693109838452291 154744314545539664757678437)
        ·
          refine ⟨29014558977288687142064707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154744314545539664757678437 29014558977288687142064707)
          ·
            refine ⟨43521838465933030713097061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29014558977288687142064707 43521838465933030713097061)
            ·
              refine ⟨8160344712362443258705699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43521838465933030713097061 8160344712362443258705699)
              ·
                refine ⟨12240517068543664888058549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8160344712362443258705699 12240517068543664888058549)
                ·
                  refine ⟨1147548475175968583255489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12240517068543664888058549 1147548475175968583255489)
                  ·
                    refine ⟨860661356381976437441617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1147548475175968583255489 860661356381976437441617)
                    ·
                      refine ⟨645496017286482328081213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860661356381976437441617 645496017286482328081213)
                      ·
                        rfl

theorem cell23_1257099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 2, 2].length) (baseStart_1257099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257099 prefixEnd_1257099 := by exact prefixLift 1257099
  have htrace : WordTrace (prefixWord ++ tailWord_1257099) baseStart_1257099 baseEnd_1257099 := by
    simpa [prefixWord, tailWord_1257099, baseEnd_1257099] using wordTrace_append hprefix tailTrace_1257099
  have hstable : (prefixWord ++ tailWord_1257099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257099).length < 2 ^ (prefixWord ++ tailWord_1257099).sum := by decide
  have hdescent : baseEnd_1257099 < baseStart_1257099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257112 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1257112 : Nat := 118140960795 + 1257112 * 2 ^ 59
def prefixEnd_1257112 : Nat := 4983230072969 + 3 ^ 40 * 1257112 * 2
def baseEnd_1257112 : Nat := 645502692534990777218653

theorem tailTrace_1257112 : CollatzResearch.WordTrace tailWord_1257112 prefixEnd_1257112 645502692534990777218653 := by
  unfold tailWord_1257112
  simp only [CollatzResearch.WordTrace]
  refine ⟨22925320710852698240878795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30567094281136930987838393 22925320710852698240878795)
  ·
    refine ⟨34387981066279047361318193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22925320710852698240878795 34387981066279047361318193)
    ·
      refine ⟨25790985799709285520988645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34387981066279047361318193 25790985799709285520988645)
      ·
        refine ⟨4835809837445491035185371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25790985799709285520988645 4835809837445491035185371)
        ·
          refine ⟨7253714756168236552778057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4835809837445491035185371 7253714756168236552778057)
          ·
            refine ⟨5440286067126177414583543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7253714756168236552778057 5440286067126177414583543)
            ·
              refine ⟨8160429100689266121875315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5440286067126177414583543 8160429100689266121875315)
              ·
                refine ⟨12240643651033899182812973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8160429100689266121875315 12240643651033899182812973)
                ·
                  refine ⟨4590241369137712193554865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12240643651033899182812973 4590241369137712193554865)
                  ·
                    refine ⟨3442681026853284145166149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4590241369137712193554865 3442681026853284145166149)
                    ·
                      refine ⟨645502692534990777218653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3442681026853284145166149 645502692534990777218653)
                      ·
                        rfl

theorem cell23_1257112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1257112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257112 prefixEnd_1257112 := by exact prefixLift 1257112
  have htrace : WordTrace (prefixWord ++ tailWord_1257112) baseStart_1257112 baseEnd_1257112 := by
    simpa [prefixWord, tailWord_1257112, baseEnd_1257112] using wordTrace_append hprefix tailTrace_1257112
  have hstable : (prefixWord ++ tailWord_1257112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257112).length < 2 ^ (prefixWord ++ tailWord_1257112).sum := by decide
  have hdescent : baseEnd_1257112 < baseStart_1257112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257122 : List Nat := [3, 3, 1, 4, 12]
def baseStart_1257122 : Nat := 118140960795 + 1257122 * 2 ^ 59
def prefixEnd_1257122 : Nat := 4983230072969 + 3 ^ 40 * 1257122 * 2
def baseEnd_1257122 : Nat := 885470270701695113983

theorem tailTrace_1257122 : CollatzResearch.WordTrace tailWord_1257122 prefixEnd_1257122 885470270701695113983 := by
  unfold tailWord_1257122
  simp only [CollatzResearch.WordTrace]
  refine ⟨11462751537917292047405405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30567337434446112126414413 11462751537917292047405405)
  ·
    refine ⟨4298531826718984517777027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11462751537917292047405405 4298531826718984517777027)
    ·
      refine ⟨6447797740078476776665541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4298531826718984517777027 6447797740078476776665541)
      ·
        refine ⟨1208962076264714395624789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6447797740078476776665541 1208962076264714395624789)
        ·
          refine ⟨885470270701695113983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1208962076264714395624789 885470270701695113983)
          ·
            rfl

theorem cell23_1257122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 12].length) (baseStart_1257122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257122 prefixEnd_1257122 := by exact prefixLift 1257122
  have htrace : WordTrace (prefixWord ++ tailWord_1257122) baseStart_1257122 baseEnd_1257122 := by
    simpa [prefixWord, tailWord_1257122, baseEnd_1257122] using wordTrace_append hprefix tailTrace_1257122
  have hstable : (prefixWord ++ tailWord_1257122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257122).length < 2 ^ (prefixWord ++ tailWord_1257122).sum := by decide
  have hdescent : baseEnd_1257122 < baseStart_1257122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257135 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 1, 9]
def baseStart_1257135 : Nat := 118140960795 + 1257135 * 2 ^ 59
def prefixEnd_1257135 : Nat := 4983230072969 + 3 ^ 40 * 1257135 * 2
def baseEnd_1257135 : Nat := 215171500863348062410349

theorem tailTrace_1257135 : CollatzResearch.WordTrace tailWord_1257135 prefixEnd_1257135 215171500863348062410349 := by
  unfold tailWord_1257135
  simp only [CollatzResearch.WordTrace]
  refine ⟨45851480300622071409844859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30567653533748047606563239 45851480300622071409844859)
  ·
    refine ⟨68777220450933107114767289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45851480300622071409844859 68777220450933107114767289)
    ·
      refine ⟨51582915338199830336075467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68777220450933107114767289 51582915338199830336075467)
      ·
        refine ⟨77374373007299745504113201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51582915338199830336075467 77374373007299745504113201)
        ·
          refine ⟨58030779755474809128084901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77374373007299745504113201 58030779755474809128084901)
          ·
            refine ⟨10880771204151526711515919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58030779755474809128084901 10880771204151526711515919)
            ·
              refine ⟨16321156806227290067273879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10880771204151526711515919 16321156806227290067273879)
              ·
                refine ⟨24481735209340935100910819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16321156806227290067273879 24481735209340935100910819)
                ·
                  refine ⟨36722602814011402651366229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24481735209340935100910819 36722602814011402651366229)
                  ·
                    refine ⟨215171500863348062410349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 36722602814011402651366229 215171500863348062410349)
                    ·
                      rfl

theorem cell23_1257135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_1257135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257135 prefixEnd_1257135 := by exact prefixLift 1257135
  have htrace : WordTrace (prefixWord ++ tailWord_1257135) baseStart_1257135 baseEnd_1257135 := by
    simpa [prefixWord, tailWord_1257135, baseEnd_1257135] using wordTrace_append hprefix tailTrace_1257135
  have hstable : (prefixWord ++ tailWord_1257135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257135).length < 2 ^ (prefixWord ++ tailWord_1257135).sum := by decide
  have hdescent : baseEnd_1257135 < baseStart_1257135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257149 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_1257149 : Nat := 118140960795 + 1257149 * 2 ^ 59
def prefixEnd_1257149 : Nat := 4983230072969 + 3 ^ 40 * 1257149 * 2
def baseEnd_1257149 : Nat := 645521691319207132455983

theorem tailTrace_1257149 : CollatzResearch.WordTrace tailWord_1257149 prefixEnd_1257149 645521691319207132455983 := by
  unfold tailWord_1257149
  simp only [CollatzResearch.WordTrace]
  refine ⟨45851990922571351800854501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30567993948380901200569667 45851990922571351800854501)
  ·
    refine ⟨8597248297982128462660219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45851990922571351800854501 8597248297982128462660219)
    ·
      refine ⟨12895872446973192693990329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8597248297982128462660219 12895872446973192693990329)
      ·
        refine ⟨9671904335229894520492747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12895872446973192693990329 9671904335229894520492747)
        ·
          refine ⟨14507856502844841780739121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9671904335229894520492747 14507856502844841780739121)
          ·
            refine ⟨10880892377133631335554341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14507856502844841780739121 10880892377133631335554341)
            ·
              refine ⟨2040167320712555875416439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10880892377133631335554341 2040167320712555875416439)
              ·
                refine ⟨3060250981068833813124659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040167320712555875416439 3060250981068833813124659)
                ·
                  refine ⟨4590376471603250719686989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060250981068833813124659 4590376471603250719686989)
                  ·
                    refine ⟨1721391176851219019882621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4590376471603250719686989 1721391176851219019882621)
                    ·
                      refine ⟨645521691319207132455983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1721391176851219019882621 645521691319207132455983)
                      ·
                        rfl

theorem cell23_1257149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_1257149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257149 prefixEnd_1257149 := by exact prefixLift 1257149
  have htrace : WordTrace (prefixWord ++ tailWord_1257149) baseStart_1257149 baseEnd_1257149 := by
    simpa [prefixWord, tailWord_1257149, baseEnd_1257149] using wordTrace_append hprefix tailTrace_1257149
  have hstable : (prefixWord ++ tailWord_1257149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257149).length < 2 ^ (prefixWord ++ tailWord_1257149).sum := by decide
  have hdescent : baseEnd_1257149 < baseStart_1257149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257154 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_1257154 : Nat := 118140960795 + 1257154 * 2 ^ 59
def prefixEnd_1257154 : Nat := 4983230072969 + 3 ^ 40 * 1257154 * 2
def baseEnd_1257154 : Nat := 645524258722479612893461

theorem tailTrace_1257154 : CollatzResearch.WordTrace tailWord_1257154 prefixEnd_1257154 645524258722479612893461 := by
  unfold tailWord_1257154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11463043321888309413696629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30568115525035491769857677 11463043321888309413696629)
  ·
    refine ⟨1074660311427029007534059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11463043321888309413696629 1074660311427029007534059)
    ·
      refine ⟨1611990467140543511301089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1074660311427029007534059 1611990467140543511301089)
      ·
        refine ⟨1208992850355407633475817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1611990467140543511301089 1208992850355407633475817)
        ·
          refine ⟨906744637766555725106863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1208992850355407633475817 906744637766555725106863)
          ·
            refine ⟨1360116956649833587660295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906744637766555725106863 1360116956649833587660295)
            ·
              refine ⟨2040175434974750381490443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360116956649833587660295 2040175434974750381490443)
              ·
                refine ⟨3060263152462125572235665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040175434974750381490443 3060263152462125572235665)
                ·
                  refine ⟨2295197364346594179176749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3060263152462125572235665 2295197364346594179176749)
                  ·
                    refine ⟨860699011629972817191281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295197364346594179176749 860699011629972817191281)
                    ·
                      refine ⟨645524258722479612893461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860699011629972817191281 645524258722479612893461)
                      ·
                        rfl

theorem cell23_1257154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_1257154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257154 prefixEnd_1257154 := by exact prefixLift 1257154
  have htrace : WordTrace (prefixWord ++ tailWord_1257154) baseStart_1257154 baseEnd_1257154 := by
    simpa [prefixWord, tailWord_1257154, baseEnd_1257154] using wordTrace_append hprefix tailTrace_1257154
  have hstable : (prefixWord ++ tailWord_1257154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257154).length < 2 ^ (prefixWord ++ tailWord_1257154).sum := by decide
  have hdescent : baseEnd_1257154 < baseStart_1257154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257159 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_1257159 : Nat := 118140960795 + 1257159 * 2 ^ 59
def prefixEnd_1257159 : Nat := 4983230072969 + 3 ^ 40 * 1257159 * 2
def baseEnd_1257159 : Nat := 645526826125752093330937

theorem tailTrace_1257159 : CollatzResearch.WordTrace tailWord_1257159 prefixEnd_1257159 645526826125752093330937 := by
  unfold tailWord_1257159
  simp only [CollatzResearch.WordTrace]
  refine ⟨45852355652535123508718531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30568237101690082339145687 45852355652535123508718531)
  ·
    refine ⟨68778533478802685263077797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45852355652535123508718531 68778533478802685263077797)
    ·
      refine ⟨12895975027275503486827087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68778533478802685263077797 12895975027275503486827087)
      ·
        refine ⟨19343962540913255230240631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12895975027275503486827087 19343962540913255230240631)
        ·
          refine ⟨29015943811369882845360947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19343962540913255230240631 29015943811369882845360947)
          ·
            refine ⟨43523915717054824268041421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29015943811369882845360947 43523915717054824268041421)
            ·
              refine ⟨16321468393895559100515533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43523915717054824268041421 16321468393895559100515533)
              ·
                refine ⟨6120550647710834662693325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16321468393895559100515533 6120550647710834662693325)
                ·
                  refine ⟨2295206492891562998509997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6120550647710834662693325 2295206492891562998509997)
                  ·
                    refine ⟨860702434834336124441249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295206492891562998509997 860702434834336124441249)
                    ·
                      refine ⟨645526826125752093330937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860702434834336124441249 645526826125752093330937)
                      ·
                        rfl

theorem cell23_1257159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_1257159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257159 prefixEnd_1257159 := by exact prefixLift 1257159
  have htrace : WordTrace (prefixWord ++ tailWord_1257159) baseStart_1257159 baseEnd_1257159 := by
    simpa [prefixWord, tailWord_1257159, baseEnd_1257159] using wordTrace_append hprefix tailTrace_1257159
  have hstable : (prefixWord ++ tailWord_1257159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257159).length < 2 ^ (prefixWord ++ tailWord_1257159).sum := by decide
  have hdescent : baseEnd_1257159 < baseStart_1257159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257176 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 1, 3, 2]
def baseStart_1257176 : Nat := 118140960795 + 1257176 * 2 ^ 59
def prefixEnd_1257176 : Nat := 4983230072969 + 3 ^ 40 * 1257176 * 2
def baseEnd_1257176 : Nat := 645535555296878526818359

theorem tailTrace_1257176 : CollatzResearch.WordTrace tailWord_1257176 prefixEnd_1257176 645535555296878526818359 := by
  unfold tailWord_1257176
  simp only [CollatzResearch.WordTrace]
  refine ⟨22926487846736767706043691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30568650462315690274724921 22926487846736767706043691)
  ·
    refine ⟨34389731770105151559065537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22926487846736767706043691 34389731770105151559065537)
    ·
      refine ⟨25792298827578863669299153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34389731770105151559065537 25792298827578863669299153)
      ·
        refine ⟨19344224120684147751974365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25792298827578863669299153 19344224120684147751974365)
        ·
          refine ⟨7254084045256555406990387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19344224120684147751974365 7254084045256555406990387)
          ·
            refine ⟨10881126067884833110485581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7254084045256555406990387 10881126067884833110485581)
            ·
              refine ⟨4080422275456812416432093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10881126067884833110485581 4080422275456812416432093)
              ·
                refine ⟨1530158353296304656162035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4080422275456812416432093 1530158353296304656162035)
                ·
                  refine ⟨2295237529944456984243053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530158353296304656162035 2295237529944456984243053)
                  ·
                    refine ⟨860714073729171369091145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295237529944456984243053 860714073729171369091145)
                    ·
                      refine ⟨645535555296878526818359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860714073729171369091145 645535555296878526818359)
                      ·
                        rfl

theorem cell23_1257176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_1257176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257176 prefixEnd_1257176 := by exact prefixLift 1257176
  have htrace : WordTrace (prefixWord ++ tailWord_1257176) baseStart_1257176 baseEnd_1257176 := by
    simpa [prefixWord, tailWord_1257176, baseEnd_1257176] using wordTrace_append hprefix tailTrace_1257176
  have hstable : (prefixWord ++ tailWord_1257176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257176).length < 2 ^ (prefixWord ++ tailWord_1257176).sum := by decide
  have hdescent : baseEnd_1257176 < baseStart_1257176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257212 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 7]
def baseStart_1257212 : Nat := 118140960795 + 1257212 * 2 ^ 59
def prefixEnd_1257212 : Nat := 4983230072969 + 3 ^ 40 * 1257212 * 2
def baseEnd_1257212 : Nat := 71728226733382265107577

theorem tailTrace_1257212 : CollatzResearch.WordTrace tailWord_1257212 prefixEnd_1257212 71728226733382265107577 := by
  unfold tailWord_1257212
  simp only [CollatzResearch.WordTrace]
  refine ⟨22927144360671556780198945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30569525814228742373598593 22927144360671556780198945)
  ·
    refine ⟨17195358270503667585149209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22927144360671556780198945 17195358270503667585149209)
    ·
      refine ⟨12896518702877750688861907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17195358270503667585149209 12896518702877750688861907)
      ·
        refine ⟨19344778054316626033292861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12896518702877750688861907 19344778054316626033292861)
        ·
          refine ⟨7254291770368734762484823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19344778054316626033292861 7254291770368734762484823)
          ·
            refine ⟨10881437655553102143727235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7254291770368734762484823 10881437655553102143727235)
            ·
              refine ⟨16322156483329653215590853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10881437655553102143727235 16322156483329653215590853)
              ·
                refine ⟨3060404340624309977923285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16322156483329653215590853 3060404340624309977923285)
                ·
                  refine ⟨71728226733382265107577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3060404340624309977923285 71728226733382265107577)
                  ·
                    rfl

theorem cell23_1257212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_1257212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257212 prefixEnd_1257212 := by exact prefixLift 1257212
  have htrace : WordTrace (prefixWord ++ tailWord_1257212) baseStart_1257212 baseEnd_1257212 := by
    simpa [prefixWord, tailWord_1257212, baseEnd_1257212] using wordTrace_append hprefix tailTrace_1257212
  have hstable : (prefixWord ++ tailWord_1257212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257212).length < 2 ^ (prefixWord ++ tailWord_1257212).sum := by decide
  have hdescent : baseEnd_1257212 < baseStart_1257212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257319 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 6]
def baseStart_1257319 : Nat := 118140960795 + 1257319 * 2 ^ 59
def prefixEnd_1257319 : Nat := 4983230072969 + 3 ^ 40 * 1257319 * 2
def baseEnd_1257319 : Nat := 71734331447830163036689

theorem tailTrace_1257319 : CollatzResearch.WordTrace tailWord_1257319 prefixEnd_1257319 71734331447830163036689 := by
  unfold tailWord_1257319
  simp only [CollatzResearch.WordTrace]
  refine ⟨45858191331955470834543011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30572127554636980556362007 45858191331955470834543011)
  ·
    refine ⟨68787286997933206251814517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45858191331955470834543011 68787286997933206251814517)
    ·
      refine ⟨6448808156056238086107611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68787286997933206251814517 6448808156056238086107611)
      ·
        refine ⟨9673212234084357129161417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6448808156056238086107611 9673212234084357129161417)
        ·
          refine ⟨7254909175563267846871063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9673212234084357129161417 7254909175563267846871063)
          ·
            refine ⟨10882363763344901770306595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7254909175563267846871063 10882363763344901770306595)
            ·
              refine ⟨16323545645017352655459893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10882363763344901770306595 16323545645017352655459893)
              ·
                refine ⟨1530332404220376811449365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16323545645017352655459893 1530332404220376811449365)
                ·
                  refine ⟨71734331447830163036689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1530332404220376811449365 71734331447830163036689)
                  ·
                    rfl

theorem cell23_1257319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 6].length) (baseStart_1257319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257319 prefixEnd_1257319 := by exact prefixLift 1257319
  have htrace : WordTrace (prefixWord ++ tailWord_1257319) baseStart_1257319 baseEnd_1257319 := by
    simpa [prefixWord, tailWord_1257319, baseEnd_1257319] using wordTrace_append hprefix tailTrace_1257319
  have hstable : (prefixWord ++ tailWord_1257319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257319).length < 2 ^ (prefixWord ++ tailWord_1257319).sum := by decide
  have hdescent : baseEnd_1257319 < baseStart_1257319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257356 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 4, 3, 2]
def baseStart_1257356 : Nat := 118140960795 + 1257356 * 2 ^ 59
def prefixEnd_1257356 : Nat := 4983230072969 + 3 ^ 40 * 1257356 * 2
def baseEnd_1257356 : Nat := 645627981814687822567531

theorem tailTrace_1257356 : CollatzResearch.WordTrace tailWord_1257356 prefixEnd_1257356 645627981814687822567531 := by
  unfold tailWord_1257356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22929770416410713076819961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30573027221880950769093281 22929770416410713076819961)
  ·
    refine ⟨17197327812308034807614971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22929770416410713076819961 17197327812308034807614971)
    ·
      refine ⟨25795991718462052211422457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17197327812308034807614971 25795991718462052211422457)
      ·
        refine ⟨19346993788846539158566843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25795991718462052211422457 19346993788846539158566843)
        ·
          refine ⟨29020490683269808737850265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19346993788846539158566843 29020490683269808737850265)
          ·
            refine ⟨21765368012452356553387699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29020490683269808737850265 21765368012452356553387699)
            ·
              refine ⟨32648052018678534830081549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21765368012452356553387699 32648052018678534830081549)
              ·
                refine ⟨12243019507004450561280581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32648052018678534830081549 12243019507004450561280581)
                ·
                  refine ⟨2295566157563334480240109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12243019507004450561280581 2295566157563334480240109)
                  ·
                    refine ⟨860837309086250430090041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295566157563334480240109 860837309086250430090041)
                    ·
                      refine ⟨645627981814687822567531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860837309086250430090041 645627981814687822567531)
                      ·
                        rfl

theorem cell23_1257356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_1257356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257356 prefixEnd_1257356 := by exact prefixLift 1257356
  have htrace : WordTrace (prefixWord ++ tailWord_1257356) baseStart_1257356 baseEnd_1257356 := by
    simpa [prefixWord, tailWord_1257356, baseEnd_1257356] using wordTrace_append hprefix tailTrace_1257356
  have hstable : (prefixWord ++ tailWord_1257356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257356).length < 2 ^ (prefixWord ++ tailWord_1257356).sum := by decide
  have hdescent : baseEnd_1257356 < baseStart_1257356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257369 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_1257369 : Nat := 118140960795 + 1257369 * 2 ^ 59
def prefixEnd_1257369 : Nat := 4983230072969 + 3 ^ 40 * 1257369 * 2
def baseEnd_1257369 : Nat := 645634657063196271704971

theorem tailTrace_1257369 : CollatzResearch.WordTrace tailWord_1257369 prefixEnd_1257369 645634657063196271704971 := by
  unfold tailWord_1257369
  simp only [CollatzResearch.WordTrace]
  refine ⟨45860014981774329373863161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30573343321182886249242107 45860014981774329373863161)
  ·
    refine ⟨34395011236330747030397371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45860014981774329373863161 34395011236330747030397371)
    ·
      refine ⟨51592516854496120545596057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34395011236330747030397371 51592516854496120545596057)
      ·
        refine ⟨38694387640872090409197043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51592516854496120545596057 38694387640872090409197043)
        ·
          refine ⟨58041581461308135613795565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38694387640872090409197043 58041581461308135613795565)
          ·
            refine ⟨21765593047990550855173337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58041581461308135613795565 21765593047990550855173337)
            ·
              refine ⟨16324194785992913141380003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21765593047990550855173337 16324194785992913141380003)
              ·
                refine ⟨24486292178989369712070005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16324194785992913141380003 24486292178989369712070005)
                ·
                  refine ⟨2295589891780253410506563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24486292178989369712070005 2295589891780253410506563)
                  ·
                    refine ⟨3443384837670380115759845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2295589891780253410506563 3443384837670380115759845)
                    ·
                      refine ⟨645634657063196271704971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3443384837670380115759845 645634657063196271704971)
                      ·
                        rfl

theorem cell23_1257369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_1257369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257369 prefixEnd_1257369 := by exact prefixLift 1257369
  have htrace : WordTrace (prefixWord ++ tailWord_1257369) baseStart_1257369 baseEnd_1257369 := by
    simpa [prefixWord, tailWord_1257369, baseEnd_1257369] using wordTrace_append hprefix tailTrace_1257369
  have hstable : (prefixWord ++ tailWord_1257369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257369).length < 2 ^ (prefixWord ++ tailWord_1257369).sum := by decide
  have hdescent : baseEnd_1257369 < baseStart_1257369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257383 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 1, 5]
def baseStart_1257383 : Nat := 118140960795 + 1257383 * 2 ^ 59
def prefixEnd_1257383 : Nat := 4983230072969 + 3 ^ 40 * 1257383 * 2
def baseEnd_1257383 : Nat := 215213948597453072309969

theorem tailTrace_1257383 : CollatzResearch.WordTrace tailWord_1257383 prefixEnd_1257383 215213948597453072309969 := by
  unfold tailWord_1257383
  simp only [CollatzResearch.WordTrace]
  refine ⟨45860525603723609764872803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30573683735815739843248535 45860525603723609764872803)
  ·
    refine ⟨68790788405585414647309205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45860525603723609764872803 68790788405585414647309205)
    ·
      refine ⟨3224568206511816311592619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68790788405585414647309205 3224568206511816311592619)
      ·
        refine ⟨4836852309767724467388929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224568206511816311592619 4836852309767724467388929)
        ·
          refine ⟨3627639232325793350541697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4836852309767724467388929 3627639232325793350541697)
          ·
            refine ⟨2720729424244345012906273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3627639232325793350541697 2720729424244345012906273)
            ·
              refine ⟨2040547068183258759679705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720729424244345012906273 2040547068183258759679705)
              ·
                refine ⟨1530410301137444069759779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2040547068183258759679705 1530410301137444069759779)
                ·
                  refine ⟨2295615451706166104639669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530410301137444069759779 2295615451706166104639669)
                  ·
                    refine ⟨215213948597453072309969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2295615451706166104639669 215213948597453072309969)
                    ·
                      rfl

theorem cell23_1257383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_1257383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257383 prefixEnd_1257383 := by exact prefixLift 1257383
  have htrace : WordTrace (prefixWord ++ tailWord_1257383) baseStart_1257383 baseEnd_1257383 := by
    simpa [prefixWord, tailWord_1257383, baseEnd_1257383] using wordTrace_append hprefix tailTrace_1257383
  have hstable : (prefixWord ++ tailWord_1257383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257383).length < 2 ^ (prefixWord ++ tailWord_1257383).sum := by decide
  have hdescent : baseEnd_1257383 < baseStart_1257383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257397 : List Nat := [1, 3, 3, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_1257397 : Nat := 118140960795 + 1257397 * 2 ^ 59
def prefixEnd_1257397 : Nat := 4983230072969 + 3 ^ 40 * 1257397 * 2
def baseEnd_1257397 : Nat := 645649034521522162154843

theorem tailTrace_1257397 : CollatzResearch.WordTrace tailWord_1257397 prefixEnd_1257397 645649034521522162154843 := by
  unfold tailWord_1257397
  simp only [CollatzResearch.WordTrace]
  refine ⟨45861036225672890155882445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30574024150448593437254963 45861036225672890155882445)
  ·
    refine ⟨17197888584627333808455917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45861036225672890155882445 17197888584627333808455917)
    ·
      refine ⟨6449208219235250178170969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17197888584627333808455917 6449208219235250178170969)
      ·
        refine ⟨4836906164426437633628227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6449208219235250178170969 4836906164426437633628227)
        ·
          refine ⟨7255359246639656450442341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4836906164426437633628227 7255359246639656450442341)
          ·
            refine ⟨1360379858744935584457939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7255359246639656450442341 1360379858744935584457939)
            ·
              refine ⟨2040569788117403376686909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360379858744935584457939 2040569788117403376686909)
              ·
                refine ⟨765213670544026266257591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2040569788117403376686909 765213670544026266257591)
                ·
                  refine ⟨1147820505816039399386387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765213670544026266257591 1147820505816039399386387)
                  ·
                    refine ⟨1721730758724059099079581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1147820505816039399386387 1721730758724059099079581)
                    ·
                      refine ⟨645649034521522162154843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1721730758724059099079581 645649034521522162154843)
                      ·
                        rfl

theorem cell23_1257397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_1257397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257397 prefixEnd_1257397 := by exact prefixLift 1257397
  have htrace : WordTrace (prefixWord ++ tailWord_1257397) baseStart_1257397 baseEnd_1257397 := by
    simpa [prefixWord, tailWord_1257397, baseEnd_1257397] using wordTrace_append hprefix tailTrace_1257397
  have hstable : (prefixWord ++ tailWord_1257397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257397).length < 2 ^ (prefixWord ++ tailWord_1257397).sum := by decide
  have hdescent : baseEnd_1257397 < baseStart_1257397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257399 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_1257399 : Nat := 118140960795 + 1257399 * 2 ^ 59
def prefixEnd_1257399 : Nat := 4983230072969 + 3 ^ 40 * 1257399 * 2
def baseEnd_1257399 : Nat := 645650061482831154329833

theorem tailTrace_1257399 : CollatzResearch.WordTrace tailWord_1257399 prefixEnd_1257399 645650061482831154329833 := by
  unfold tailWord_1257399
  simp only [CollatzResearch.WordTrace]
  refine ⟨45861109171665644497455251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30574072781110429664970167 45861109171665644497455251)
  ·
    refine ⟨68791663757498466746182877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45861109171665644497455251 68791663757498466746182877)
    ·
      refine ⟨25796873909061925029818579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68791663757498466746182877 25796873909061925029818579)
      ·
        refine ⟨38695310863592887544727869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25796873909061925029818579 38695310863592887544727869)
        ·
          refine ⟨14510741573847332829272951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38695310863592887544727869 14510741573847332829272951)
          ·
            refine ⟨21766112360770999243909427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14510741573847332829272951 21766112360770999243909427)
            ·
              refine ⟨32649168541156498865864141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21766112360770999243909427 32649168541156498865864141)
              ·
                refine ⟨12243438202933687074699053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32649168541156498865864141 12243438202933687074699053)
                ·
                  refine ⟨4591289326100132653012145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12243438202933687074699053 4591289326100132653012145)
                  ·
                    refine ⟨3443466994575099489759109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4591289326100132653012145 3443466994575099489759109)
                    ·
                      refine ⟨645650061482831154329833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3443466994575099489759109 645650061482831154329833)
                      ·
                        rfl

theorem cell23_1257399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_1257399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257399 prefixEnd_1257399 := by exact prefixLift 1257399
  have htrace : WordTrace (prefixWord ++ tailWord_1257399) baseStart_1257399 baseEnd_1257399 := by
    simpa [prefixWord, tailWord_1257399, baseEnd_1257399] using wordTrace_append hprefix tailTrace_1257399
  have hstable : (prefixWord ++ tailWord_1257399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257399).length < 2 ^ (prefixWord ++ tailWord_1257399).sum := by decide
  have hdescent : baseEnd_1257399 < baseStart_1257399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257406 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1257406 : Nat := 118140960795 + 1257406 * 2 ^ 59
def prefixEnd_1257406 : Nat := 4983230072969 + 3 ^ 40 * 1257406 * 2
def baseEnd_1257406 : Nat := 645653655847412626942301

theorem tailTrace_1257406 : CollatzResearch.WordTrace tailWord_1257406 prefixEnd_1257406 645653655847412626942301 := by
  unfold tailWord_1257406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5732670560330035586620009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30574242988426856461973381 5732670560330035586620009)
  ·
    refine ⟨4299502920247526689965007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5732670560330035586620009 4299502920247526689965007)
    ·
      refine ⟨6449254380371290034947511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4299502920247526689965007 6449254380371290034947511)
      ·
        refine ⟨9673881570556935052421267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6449254380371290034947511 9673881570556935052421267)
        ·
          refine ⟨14510822355835402578631901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9673881570556935052421267 14510822355835402578631901)
          ·
            refine ⟨5441558383438275966986963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14510822355835402578631901 5441558383438275966986963)
            ·
              refine ⟨8162337575157413950480445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5441558383438275966986963 8162337575157413950480445)
              ·
                refine ⟨3060876590684030231430167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8162337575157413950480445 3060876590684030231430167)
                ·
                  refine ⟨4591314886026045347145251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060876590684030231430167 4591314886026045347145251)
                  ·
                    refine ⟨6886972329039068020717877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4591314886026045347145251 6886972329039068020717877)
                    ·
                      refine ⟨645653655847412626942301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6886972329039068020717877 645653655847412626942301)
                      ·
                        rfl

theorem cell23_1257406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1257406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257406 prefixEnd_1257406 := by exact prefixLift 1257406
  have htrace : WordTrace (prefixWord ++ tailWord_1257406) baseStart_1257406 baseEnd_1257406 := by
    simpa [prefixWord, tailWord_1257406, baseEnd_1257406] using wordTrace_append hprefix tailTrace_1257406
  have hstable : (prefixWord ++ tailWord_1257406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257406).length < 2 ^ (prefixWord ++ tailWord_1257406).sum := by decide
  have hdescent : baseEnd_1257406 < baseStart_1257406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257420 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 3, 2, 2]
def baseStart_1257420 : Nat := 118140960795 + 1257420 * 2 ^ 59
def prefixEnd_1257420 : Nat := 4983230072969 + 3 ^ 40 * 1257420 * 2
def baseEnd_1257420 : Nat := 645660844576575572167237

theorem tailTrace_1257420 : CollatzResearch.WordTrace tailWord_1257420 prefixEnd_1257420 645660844576575572167237 := by
  unfold tailWord_1257420
  simp only [CollatzResearch.WordTrace]
  refine ⟨22930937552294782541984857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30574583403059710055979809 22930937552294782541984857)
  ·
    refine ⟨17198203164221086906488643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22930937552294782541984857 17198203164221086906488643)
    ·
      refine ⟨25797304746331630359732965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17198203164221086906488643 25797304746331630359732965)
      ·
        refine ⟨4836994639937180692449931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25797304746331630359732965 4836994639937180692449931)
        ·
          refine ⟨7255491959905771038674897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4836994639937180692449931 7255491959905771038674897)
          ·
            refine ⟨5441618969929328279006173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7255491959905771038674897 5441618969929328279006173)
            ·
              refine ⟨2040607113723498104627315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5441618969929328279006173 2040607113723498104627315)
              ·
                refine ⟨3060910670585247156940973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040607113723498104627315 3060910670585247156940973)
                ·
                  refine ⟨1147841501469467683852865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3060910670585247156940973 1147841501469467683852865)
                  ·
                    refine ⟨860881126102100762889649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1147841501469467683852865 860881126102100762889649)
                    ·
                      refine ⟨645660844576575572167237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860881126102100762889649 645660844576575572167237)
                      ·
                        rfl

theorem cell23_1257420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_1257420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257420 prefixEnd_1257420 := by exact prefixLift 1257420
  have htrace : WordTrace (prefixWord ++ tailWord_1257420) baseStart_1257420 baseEnd_1257420 := by
    simpa [prefixWord, tailWord_1257420, baseEnd_1257420] using wordTrace_append hprefix tailTrace_1257420
  have hstable : (prefixWord ++ tailWord_1257420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257420).length < 2 ^ (prefixWord ++ tailWord_1257420).sum := by decide
  have hdescent : baseEnd_1257420 < baseStart_1257420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257437 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_1257437 : Nat := 118140960795 + 1257437 * 2 ^ 59
def prefixEnd_1257437 : Nat := 4983230072969 + 3 ^ 40 * 1257437 * 2
def baseEnd_1257437 : Nat := 645669573747702005654659

theorem tailTrace_1257437 : CollatzResearch.WordTrace tailWord_1257437 prefixEnd_1257437 645669573747702005654659 := by
  unfold tailWord_1257437
  simp only [CollatzResearch.WordTrace]
  refine ⟨45862495145527976987338565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30574996763685317991559043 45862495145527976987338565)
  ·
    refine ⟨8599217839786495685125981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45862495145527976987338565 8599217839786495685125981)
    ·
      refine ⟨3224706689919935881922243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8599217839786495685125981 3224706689919935881922243)
      ·
        refine ⟨4837060034879903822883365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224706689919935881922243 4837060034879903822883365)
        ·
          refine ⟨906948756539981966790631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4837060034879903822883365 906948756539981966790631)
          ·
            refine ⟨1360423134809972950185947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906948756539981966790631 1360423134809972950185947)
            ·
              refine ⟨2040634702214959425278921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360423134809972950185947 2040634702214959425278921)
              ·
                refine ⟨1530476026661219568959191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2040634702214959425278921 1530476026661219568959191)
                ·
                  refine ⟨2295714039991829353438787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530476026661219568959191 2295714039991829353438787)
                  ·
                    refine ⟨3443571059987744030158181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2295714039991829353438787 3443571059987744030158181)
                    ·
                      refine ⟨645669573747702005654659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3443571059987744030158181 645669573747702005654659)
                      ·
                        rfl

theorem cell23_1257437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_1257437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257437 prefixEnd_1257437 := by exact prefixLift 1257437
  have htrace : WordTrace (prefixWord ++ tailWord_1257437) baseStart_1257437 baseEnd_1257437 := by
    simpa [prefixWord, tailWord_1257437, baseEnd_1257437] using wordTrace_append hprefix tailTrace_1257437
  have hstable : (prefixWord ++ tailWord_1257437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257437).length < 2 ^ (prefixWord ++ tailWord_1257437).sum := by decide
  have hdescent : baseEnd_1257437 < baseStart_1257437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257459 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 4]
def baseStart_1257459 : Nat := 118140960795 + 1257459 * 2 ^ 59
def prefixEnd_1257459 : Nat := 4983230072969 + 3 ^ 40 * 1257459 * 2
def baseEnd_1257459 : Nat := 645680870322100919579557

theorem tailTrace_1257459 : CollatzResearch.WordTrace tailWord_1257459 prefixEnd_1257459 645680870322100919579557 := by
  unfold tailWord_1257459
  simp only [CollatzResearch.WordTrace]
  refine ⟨45863297551448274744639431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30575531700965516496426287 45863297551448274744639431)
  ·
    refine ⟨68794946327172412116959147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45863297551448274744639431 68794946327172412116959147)
    ·
      refine ⟨103192419490758618175438721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68794946327172412116959147 103192419490758618175438721)
      ·
        refine ⟨77394314618068963631579041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103192419490758618175438721 77394314618068963631579041)
        ·
          refine ⟨58045735963551722723684281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77394314618068963631579041 58045735963551722723684281)
          ·
            refine ⟨43534301972663792042763211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58045735963551722723684281 43534301972663792042763211)
            ·
              refine ⟨65301452958995688064144817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43534301972663792042763211 65301452958995688064144817)
              ·
                refine ⟨48976089719246766048108613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65301452958995688064144817 48976089719246766048108613)
                ·
                  refine ⟨9183016822358768634020365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48976089719246766048108613 9183016822358768634020365)
                  ·
                    refine ⟨3443631308384538237757637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9183016822358768634020365 3443631308384538237757637)
                    ·
                      refine ⟨645680870322100919579557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3443631308384538237757637 645680870322100919579557)
                      ·
                        rfl

theorem cell23_1257459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_1257459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257459 prefixEnd_1257459 := by exact prefixLift 1257459
  have htrace : WordTrace (prefixWord ++ tailWord_1257459) baseStart_1257459 baseEnd_1257459 := by
    simpa [prefixWord, tailWord_1257459, baseEnd_1257459] using wordTrace_append hprefix tailTrace_1257459
  have hstable : (prefixWord ++ tailWord_1257459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257459).length < 2 ^ (prefixWord ++ tailWord_1257459).sum := by decide
  have hdescent : baseEnd_1257459 < baseStart_1257459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257486 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_1257486 : Nat := 118140960795 + 1257486 * 2 ^ 59
def prefixEnd_1257486 : Nat := 4983230072969 + 3 ^ 40 * 1257486 * 2
def baseEnd_1257486 : Nat := 215231578099924104647311

theorem tailTrace_1257486 : CollatzResearch.WordTrace tailWord_1257486 prefixEnd_1257486 215231578099924104647311 := by
  unfold tailWord_1257486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5733035290293807294484039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30576188214900305570581541 5733035290293807294484039)
  ·
    refine ⟨8599552935440710941726059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5733035290293807294484039 8599552935440710941726059)
    ·
      refine ⟨12899329403161066412589089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8599552935440710941726059 12899329403161066412589089)
      ·
        refine ⟨9674497052370799809441817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12899329403161066412589089 9674497052370799809441817)
        ·
          refine ⟨7255872789278099857081363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9674497052370799809441817 7255872789278099857081363)
          ·
            refine ⟨10883809183917149785622045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7255872789278099857081363 10883809183917149785622045)
            ·
              refine ⟨4081428443968931169608267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10883809183917149785622045 4081428443968931169608267)
              ·
                refine ⟨6122142665953396754412401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4081428443968931169608267 6122142665953396754412401)
                ·
                  refine ⟨4591606999465047565809301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6122142665953396754412401 4591606999465047565809301)
                  ·
                    refine ⟨215231578099924104647311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4591606999465047565809301 215231578099924104647311)
                    ·
                      rfl

theorem cell23_1257486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_1257486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257486 prefixEnd_1257486 := by exact prefixLift 1257486
  have htrace : WordTrace (prefixWord ++ tailWord_1257486) baseStart_1257486 baseEnd_1257486 := by
    simpa [prefixWord, tailWord_1257486, baseEnd_1257486] using wordTrace_append hprefix tailTrace_1257486
  have hstable : (prefixWord ++ tailWord_1257486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257486).length < 2 ^ (prefixWord ++ tailWord_1257486).sum := by decide
  have hdescent : baseEnd_1257486 < baseStart_1257486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257496 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1257496 : Nat := 118140960795 + 1257496 * 2 ^ 59
def prefixEnd_1257496 : Nat := 4983230072969 + 3 ^ 40 * 1257496 * 2
def baseEnd_1257496 : Nat := 645699869106317274816887

theorem tailTrace_1257496 : CollatzResearch.WordTrace tailWord_1257496 prefixEnd_1257496 645699869106317274816887 := by
  unfold tailWord_1257496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22932323526157115031868171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30576431368209486709157561 22932323526157115031868171)
  ·
    refine ⟨34398485289235672547802257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22932323526157115031868171 34398485289235672547802257)
    ·
      refine ⟨25798863966926754410851693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34398485289235672547802257 25798863966926754410851693)
      ·
        refine ⟨9674573987597532904069385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25798863966926754410851693 9674573987597532904069385)
        ·
          refine ⟨7255930490698149678052039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9674573987597532904069385 7255930490698149678052039)
          ·
            refine ⟨10883895736047224517078059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7255930490698149678052039 10883895736047224517078059)
            ·
              refine ⟨16325843604070836775617089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10883895736047224517078059 16325843604070836775617089)
              ·
                refine ⟨12244382703053127581712817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16325843604070836775617089 12244382703053127581712817)
                ·
                  refine ⟨9183287027289845686284613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12244382703053127581712817 9183287027289845686284613)
                  ·
                    refine ⟨1721866317616846066178365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9183287027289845686284613 1721866317616846066178365)
                    ·
                      refine ⟨645699869106317274816887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1721866317616846066178365 645699869106317274816887)
                      ·
                        rfl

theorem cell23_1257496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1257496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257496 prefixEnd_1257496 := by exact prefixLift 1257496
  have htrace : WordTrace (prefixWord ++ tailWord_1257496) baseStart_1257496 baseEnd_1257496 := by
    simpa [prefixWord, tailWord_1257496, baseEnd_1257496] using wordTrace_append hprefix tailTrace_1257496
  have hstable : (prefixWord ++ tailWord_1257496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257496).length < 2 ^ (prefixWord ++ tailWord_1257496).sum := by decide
  have hdescent : baseEnd_1257496 < baseStart_1257496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257506 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1257506 : Nat := 118140960795 + 1257506 * 2 ^ 59
def prefixEnd_1257506 : Nat := 4983230072969 + 3 ^ 40 * 1257506 * 2
def baseEnd_1257506 : Nat := 645705003912862235691841

theorem tailTrace_1257506 : CollatzResearch.WordTrace tailWord_1257506 prefixEnd_1257506 645705003912862235691841 := by
  unfold tailWord_1257506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11466252945569500442900093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30576674521518667847733581 11466252945569500442900093)
  ·
    refine ⟨4299844854588562666087535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11466252945569500442900093 4299844854588562666087535)
    ·
      refine ⟨6449767281882843999131303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4299844854588562666087535 6449767281882843999131303)
      ·
        refine ⟨9674650922824265998696955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6449767281882843999131303 9674650922824265998696955)
        ·
          refine ⟨14511976384236398998045433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9674650922824265998696955 14511976384236398998045433)
          ·
            refine ⟨10883982288177299248534075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14511976384236398998045433 10883982288177299248534075)
            ·
              refine ⟨16325973432265948872801113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10883982288177299248534075 16325973432265948872801113)
              ·
                refine ⟨12244480074199461654600835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16325973432265948872801113 12244480074199461654600835)
                ·
                  refine ⟨18366720111299192481901253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12244480074199461654600835 18366720111299192481901253)
                  ·
                    refine ⟨3443760020868598590356485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18366720111299192481901253 3443760020868598590356485)
                    ·
                      refine ⟨645705003912862235691841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3443760020868598590356485 645705003912862235691841)
                      ·
                        rfl

theorem cell23_1257506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1257506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257506 prefixEnd_1257506 := by exact prefixLift 1257506
  have htrace : WordTrace (prefixWord ++ tailWord_1257506) baseStart_1257506 baseEnd_1257506 := by
    simpa [prefixWord, tailWord_1257506, baseEnd_1257506] using wordTrace_append hprefix tailTrace_1257506
  have hstable : (prefixWord ++ tailWord_1257506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257506).length < 2 ^ (prefixWord ++ tailWord_1257506).sum := by decide
  have hdescent : baseEnd_1257506 < baseStart_1257506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257514 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_1257514 : Nat := 118140960795 + 1257514 * 2 ^ 59
def prefixEnd_1257514 : Nat := 4983230072969 + 3 ^ 40 * 1257514 * 2
def baseEnd_1257514 : Nat := 645709111758098204391805

theorem tailTrace_1257514 : CollatzResearch.WordTrace tailWord_1257514 prefixEnd_1257514 645709111758098204391805 := by
  unfold tailWord_1257514
  simp only [CollatzResearch.WordTrace]
  refine ⟨11466325891562254784472899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30576869044166012758594397 11466325891562254784472899)
  ·
    refine ⟨17199488837343382176709349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11466325891562254784472899 17199488837343382176709349)
    ·
      refine ⟨3224904157001884158133003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17199488837343382176709349 3224904157001884158133003)
      ·
        refine ⟨4837356235502826237199505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224904157001884158133003 4837356235502826237199505)
        ·
          refine ⟨3628017176627119677899629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4837356235502826237199505 3628017176627119677899629)
          ·
            refine ⟨1360506441235169879212361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3628017176627119677899629 1360506441235169879212361)
            ·
              refine ⟨1020379830926377409409271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1360506441235169879212361 1020379830926377409409271)
              ·
                refine ⟨1530569746389566114113907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020379830926377409409271 1530569746389566114113907)
                ·
                  refine ⟨2295854619584349171170861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530569746389566114113907 2295854619584349171170861)
                  ·
                    refine ⟨860945482344130939189073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295854619584349171170861 860945482344130939189073)
                    ·
                      refine ⟨645709111758098204391805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 860945482344130939189073 645709111758098204391805)
                      ·
                        rfl

theorem cell23_1257514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_1257514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257514 prefixEnd_1257514 := by exact prefixLift 1257514
  have htrace : WordTrace (prefixWord ++ tailWord_1257514) baseStart_1257514 baseEnd_1257514 := by
    simpa [prefixWord, tailWord_1257514, baseEnd_1257514] using wordTrace_append hprefix tailTrace_1257514
  have hstable : (prefixWord ++ tailWord_1257514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257514).length < 2 ^ (prefixWord ++ tailWord_1257514).sum := by decide
  have hdescent : baseEnd_1257514 < baseStart_1257514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257533 : List Nat := [1, 4, 1, 3, 1, 1, 1, 6, 5]
def baseStart_1257533 : Nat := 118140960795 + 1257533 * 2 ^ 59
def prefixEnd_1257533 : Nat := 4983230072969 + 3 ^ 40 * 1257533 * 2
def baseEnd_1257533 : Nat := 71746540876725958894913

theorem tailTrace_1257533 : CollatzResearch.WordTrace tailWord_1257533 prefixEnd_1257533 71746540876725958894913 := by
  unfold tailWord_1257533
  simp only [CollatzResearch.WordTrace]
  refine ⟨45865996553180185382833253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30577331035453456921888835 45865996553180185382833253)
  ·
    refine ⟨8599874353721284759281235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45865996553180185382833253 8599874353721284759281235)
    ·
      refine ⟨12899811530581927138921853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8599874353721284759281235 12899811530581927138921853)
      ·
        refine ⟨4837429323968222677095695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12899811530581927138921853 4837429323968222677095695)
        ·
          refine ⟨7256143985952334015643543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4837429323968222677095695 7256143985952334015643543)
          ·
            refine ⟨10884215978928501023465315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7256143985952334015643543 10884215978928501023465315)
            ·
              refine ⟨16326323968392751535197973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10884215978928501023465315 16326323968392751535197973)
              ·
                refine ⟨765296436018410228212405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16326323968392751535197973 765296436018410228212405)
                ·
                  refine ⟨71746540876725958894913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 765296436018410228212405 71746540876725958894913)
                  ·
                    rfl

theorem cell23_1257533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_1257533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257533 prefixEnd_1257533 := by exact prefixLift 1257533
  have htrace : WordTrace (prefixWord ++ tailWord_1257533) baseStart_1257533 baseEnd_1257533 := by
    simpa [prefixWord, tailWord_1257533, baseEnd_1257533] using wordTrace_append hprefix tailTrace_1257533
  have hstable : (prefixWord ++ tailWord_1257533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257533).length < 2 ^ (prefixWord ++ tailWord_1257533).sum := by decide
  have hdescent : baseEnd_1257533 < baseStart_1257533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257556 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1257556 : Nat := 118140960795 + 1257556 * 2 ^ 59
def prefixEnd_1257556 : Nat := 4983230072969 + 3 ^ 40 * 1257556 * 2
def baseEnd_1257556 : Nat := 645730677945587040066611

theorem tailTrace_1257556 : CollatzResearch.WordTrace tailWord_1257556 prefixEnd_1257556 645730677945587040066611 := by
  unfold tailWord_1257556
  simp only [CollatzResearch.WordTrace]
  refine ⟨22933417716048430155460261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30577890288064573540613681 22933417716048430155460261)
  ·
    refine ⟨4300015821759080654148799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22933417716048430155460261 4300015821759080654148799)
    ·
      refine ⟨6450023732638620981223199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4300015821759080654148799 6450023732638620981223199)
      ·
        refine ⟨9675035598957931471834799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6450023732638620981223199 9675035598957931471834799)
        ·
          refine ⟨14512553398436897207752199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9675035598957931471834799 14512553398436897207752199)
          ·
            refine ⟨21768830097655345811628299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14512553398436897207752199 21768830097655345811628299)
            ·
              refine ⟨32653245146483018717442449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21768830097655345811628299 32653245146483018717442449)
              ·
                refine ⟨24489933859862264038081837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32653245146483018717442449 24489933859862264038081837)
                ·
                  refine ⟨9183725197448349014280689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24489933859862264038081837 9183725197448349014280689)
                  ·
                    refine ⟨6887793898086261760710517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9183725197448349014280689 6887793898086261760710517)
                    ·
                      refine ⟨645730677945587040066611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6887793898086261760710517 645730677945587040066611)
                      ·
                        rfl

theorem cell23_1257556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1257556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257556 prefixEnd_1257556 := by exact prefixLift 1257556
  have htrace : WordTrace (prefixWord ++ tailWord_1257556) baseStart_1257556 baseEnd_1257556 := by
    simpa [prefixWord, tailWord_1257556, baseEnd_1257556] using wordTrace_append hprefix tailTrace_1257556
  have hstable : (prefixWord ++ tailWord_1257556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257556).length < 2 ^ (prefixWord ++ tailWord_1257556).sum := by decide
  have hdescent : baseEnd_1257556 < baseStart_1257556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257583 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_1257583 : Nat := 118140960795 + 1257583 * 2 ^ 59
def prefixEnd_1257583 : Nat := 4983230072969 + 3 ^ 40 * 1257583 * 2
def baseEnd_1257583 : Nat := 645744541923258434428987

theorem tailTrace_1257583 : CollatzResearch.WordTrace tailWord_1257583 prefixEnd_1257583 645744541923258434428987 := by
  unfold tailWord_1257583
  simp only [CollatzResearch.WordTrace]
  refine ⟨45867820202999043922153403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30578546801999362614768935 45867820202999043922153403)
  ·
    refine ⟨68801730304498565883230105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45867820202999043922153403 68801730304498565883230105)
    ·
      refine ⟨51601297728373924412422579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68801730304498565883230105 51601297728373924412422579)
      ·
        refine ⟨77401946592560886618633869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51601297728373924412422579 77401946592560886618633869)
        ·
          refine ⟨29025729972210332481987701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77401946592560886618633869 29025729972210332481987701)
          ·
            refine ⟨2721162184894718670186347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29025729972210332481987701 2721162184894718670186347)
            ·
              refine ⟨4081743277342078005279521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721162184894718670186347 4081743277342078005279521)
              ·
                refine ⟨3061307458006558503959641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4081743277342078005279521 3061307458006558503959641)
                ·
                  refine ⟨2295980593504918877969731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3061307458006558503959641 2295980593504918877969731)
                  ·
                    refine ⟨3443970890257378316954597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2295980593504918877969731 3443970890257378316954597)
                    ·
                      refine ⟨645744541923258434428987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3443970890257378316954597 645744541923258434428987)
                      ·
                        rfl

theorem cell23_1257583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_1257583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257583 prefixEnd_1257583 := by exact prefixLift 1257583
  have htrace : WordTrace (prefixWord ++ tailWord_1257583) baseStart_1257583 baseEnd_1257583 := by
    simpa [prefixWord, tailWord_1257583, baseEnd_1257583] using wordTrace_append hprefix tailTrace_1257583
  have hstable : (prefixWord ++ tailWord_1257583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257583).length < 2 ^ (prefixWord ++ tailWord_1257583).sum := by decide
  have hdescent : baseEnd_1257583 < baseStart_1257583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257650 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_1257650 : Nat := 118140960795 + 1257650 * 2 ^ 59
def prefixEnd_1257650 : Nat := 4983230072969 + 3 ^ 40 * 1257650 * 2
def baseEnd_1257650 : Nat := 645778945127109672291179

theorem tailTrace_1257650 : CollatzResearch.WordTrace tailWord_1257650 prefixEnd_1257650 645778945127109672291179 := by
  unfold tailWord_1257650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11467565973439078591210601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30580175929170876243228269 11467565973439078591210601)
  ·
    refine ⟨8600674480079308943407951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11467565973439078591210601 8600674480079308943407951)
    ·
      refine ⟨12901011720118963415111927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8600674480079308943407951 12901011720118963415111927)
      ·
        refine ⟨19351517580178445122667891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12901011720118963415111927 19351517580178445122667891)
        ·
          refine ⟨29027276370267667684001837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19351517580178445122667891 29027276370267667684001837)
          ·
            refine ⟨10885228638850375381500689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29027276370267667684001837 10885228638850375381500689)
            ·
              refine ⟨8163921479137781536125517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10885228638850375381500689 8163921479137781536125517)
              ·
                refine ⟨3061470554676668076047069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8163921479137781536125517 3061470554676668076047069)
                ·
                  refine ⟨1148051458003750528517651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3061470554676668076047069 1148051458003750528517651)
                  ·
                    refine ⟨1722077187005625792776477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1148051458003750528517651 1722077187005625792776477)
                    ·
                      refine ⟨645778945127109672291179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1722077187005625792776477 645778945127109672291179)
                      ·
                        rfl

theorem cell23_1257650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_1257650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257650 prefixEnd_1257650 := by exact prefixLift 1257650
  have htrace : WordTrace (prefixWord ++ tailWord_1257650) baseStart_1257650 baseEnd_1257650 := by
    simpa [prefixWord, tailWord_1257650, baseEnd_1257650] using wordTrace_append hprefix tailTrace_1257650
  have hstable : (prefixWord ++ tailWord_1257650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257650).length < 2 ^ (prefixWord ++ tailWord_1257650).sum := by decide
  have hdescent : baseEnd_1257650 < baseStart_1257650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257673 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 1, 8, 2]
def baseStart_1257673 : Nat := 118140960795 + 1257673 * 2 ^ 59
def prefixEnd_1257673 : Nat := 4983230072969 + 3 ^ 40 * 1257673 * 2
def baseEnd_1257673 : Nat := 645790755182163082303573

theorem tailTrace_1257673 : CollatzResearch.WordTrace tailWord_1257673 prefixEnd_1257673 645790755182163082303573 := by
  unfold tailWord_1257673
  simp only [CollatzResearch.WordTrace]
  refine ⟨45871102772672989292929673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30580735181781992861953115 45871102772672989292929673)
  ·
    refine ⟨34403327079504741969697255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45871102772672989292929673 34403327079504741969697255)
    ·
      refine ⟨51604990619257112954545883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34403327079504741969697255 51604990619257112954545883)
      ·
        refine ⟨77407485928885669431818825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51604990619257112954545883 77407485928885669431818825)
        ·
          refine ⟨58055614446664252073864119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77407485928885669431818825 58055614446664252073864119)
          ·
            refine ⟨87083421669996378110796179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58055614446664252073864119 87083421669996378110796179)
            ·
              refine ⟨130625132504994567166194269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87083421669996378110796179 130625132504994567166194269)
              ·
                refine ⟨48984424689372962687322851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130625132504994567166194269 48984424689372962687322851)
                ·
                  refine ⟨73476637034059444030984277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48984424689372962687322851 73476637034059444030984277)
                  ·
                    refine ⟨861054340242884109738097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73476637034059444030984277 861054340242884109738097)
                    ·
                      refine ⟨645790755182163082303573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861054340242884109738097 645790755182163082303573)
                      ·
                        rfl

theorem cell23_1257673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 8, 2].length) (baseStart_1257673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257673 prefixEnd_1257673 := by exact prefixLift 1257673
  have htrace : WordTrace (prefixWord ++ tailWord_1257673) baseStart_1257673 baseEnd_1257673 := by
    simpa [prefixWord, tailWord_1257673, baseEnd_1257673] using wordTrace_append hprefix tailTrace_1257673
  have hstable : (prefixWord ++ tailWord_1257673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257673).length < 2 ^ (prefixWord ++ tailWord_1257673).sum := by decide
  have hdescent : baseEnd_1257673 < baseStart_1257673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257696 : List Nat := [2, 1, 1, 3, 1, 3, 12]
def baseStart_1257696 : Nat := 118140960795 + 1257696 * 2 ^ 59
def prefixEnd_1257696 : Nat := 4983230072969 + 3 ^ 40 * 1257696 * 2
def baseEnd_1257696 : Nat := 7972871175768104843407

theorem tailTrace_1257696 : CollatzResearch.WordTrace tailWord_1257696 prefixEnd_1257696 7972871175768104843407 := by
  unfold tailWord_1257696
  simp only [CollatzResearch.WordTrace]
  refine ⟨22935970825794832110508471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30581294434393109480677961 22935970825794832110508471)
  ·
    refine ⟨34403956238692248165762707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22935970825794832110508471 34403956238692248165762707)
    ·
      refine ⟨51605934358038372248644061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34403956238692248165762707 51605934358038372248644061)
      ·
        refine ⟨19352225384264389593241523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51605934358038372248644061 19352225384264389593241523)
        ·
          refine ⟨29028338076396584389862285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19352225384264389593241523 29028338076396584389862285)
          ·
            refine ⟨10885626778648719146198357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29028338076396584389862285 10885626778648719146198357)
            ·
              refine ⟨7972871175768104843407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 10885626778648719146198357 7972871175768104843407)
              ·
                rfl

theorem cell23_1257696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 12].length) (baseStart_1257696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257696 prefixEnd_1257696 := by exact prefixLift 1257696
  have htrace : WordTrace (prefixWord ++ tailWord_1257696) baseStart_1257696 baseEnd_1257696 := by
    simpa [prefixWord, tailWord_1257696, baseEnd_1257696] using wordTrace_append hprefix tailTrace_1257696
  have hstable : (prefixWord ++ tailWord_1257696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257696).length < 2 ^ (prefixWord ++ tailWord_1257696).sum := by decide
  have hdescent : baseEnd_1257696 < baseStart_1257696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257707 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 3, 2, 2]
def baseStart_1257707 : Nat := 118140960795 + 1257707 * 2 ^ 59
def prefixEnd_1257707 : Nat := 4983230072969 + 3 ^ 40 * 1257707 * 2
def baseEnd_1257707 : Nat := 645808213524415949278417

theorem tailTrace_1257707 : CollatzResearch.WordTrace tailWord_1257707 prefixEnd_1257707 645808213524415949278417 := by
  unfold tailWord_1257707
  simp only [CollatzResearch.WordTrace]
  refine ⟨45872342854549813099667375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30581561903033208733111583 45872342854549813099667375)
  ·
    refine ⟨68808514281824719649501063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45872342854549813099667375 68808514281824719649501063)
    ·
      refine ⟨103212771422737079474251595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68808514281824719649501063 103212771422737079474251595)
      ·
        refine ⟨154819157134105619211377393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103212771422737079474251595 154819157134105619211377393)
        ·
          refine ⟨116114367850579214408533045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154819157134105619211377393 116114367850579214408533045)
          ·
            refine ⟨10885721985991801350799973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116114367850579214408533045 10885721985991801350799973)
            ·
              refine ⟨2041072872373462753274995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10885721985991801350799973 2041072872373462753274995)
              ·
                refine ⟨3061609308560194129912493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041072872373462753274995 3061609308560194129912493)
                ·
                  refine ⟨1148103490710072798717185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3061609308560194129912493 1148103490710072798717185)
                  ·
                    refine ⟨861077618032554599037889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1148103490710072798717185 861077618032554599037889)
                    ·
                      refine ⟨645808213524415949278417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861077618032554599037889 645808213524415949278417)
                      ·
                        rfl

theorem cell23_1257707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 2, 2].length) (baseStart_1257707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257707 prefixEnd_1257707 := by exact prefixLift 1257707
  have htrace : WordTrace (prefixWord ++ tailWord_1257707) baseStart_1257707 baseEnd_1257707 := by
    simpa [prefixWord, tailWord_1257707, baseEnd_1257707] using wordTrace_append hprefix tailTrace_1257707
  have hstable : (prefixWord ++ tailWord_1257707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257707).length < 2 ^ (prefixWord ++ tailWord_1257707).sum := by decide
  have hdescent : baseEnd_1257707 < baseStart_1257707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257730 : List Nat := [3, 4, 1, 1, 2, 2, 1, 9]
def baseStart_1257730 : Nat := 118140960795 + 1257730 * 2 ^ 59
def prefixEnd_1257730 : Nat := 4983230072969 + 3 ^ 40 * 1257730 * 2
def baseEnd_1257730 : Nat := 23919260132572939232993

theorem tailTrace_1257730 : CollatzResearch.WordTrace tailWord_1257730 prefixEnd_1257730 23919260132572939232993 := by
  unfold tailWord_1257730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11468295433366622006938661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30582121155644325351836429 11468295433366622006938661)
  ·
    refine ⟨2150305393756241626300999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11468295433366622006938661 2150305393756241626300999)
    ·
      refine ⟨3225458090634362439451499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2150305393756241626300999 3225458090634362439451499)
      ·
        refine ⟨4838187135951543659177249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3225458090634362439451499 4838187135951543659177249)
        ·
          refine ⟨3628640351963657744382937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4838187135951543659177249 3628640351963657744382937)
          ·
            refine ⟨2721480263972743308287203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3628640351963657744382937 2721480263972743308287203)
            ·
              refine ⟨4082220395959114962430805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721480263972743308287203 4082220395959114962430805)
              ·
                refine ⟨23919260132572939232993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4082220395959114962430805 23919260132572939232993)
                ·
                  rfl

theorem cell23_1257730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 9].length) (baseStart_1257730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257730 prefixEnd_1257730 := by exact prefixLift 1257730
  have htrace : WordTrace (prefixWord ++ tailWord_1257730) baseStart_1257730 baseEnd_1257730 := by
    simpa [prefixWord, tailWord_1257730, baseEnd_1257730] using wordTrace_append hprefix tailTrace_1257730
  have hstable : (prefixWord ++ tailWord_1257730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257730).length < 2 ^ (prefixWord ++ tailWord_1257730).sum := by decide
  have hdescent : baseEnd_1257730 < baseStart_1257730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257740 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 6, 1, 3]
def baseStart_1257740 : Nat := 118140960795 + 1257740 * 2 ^ 59
def prefixEnd_1257740 : Nat := 4983230072969 + 3 ^ 40 * 1257740 * 2
def baseEnd_1257740 : Nat := 645825158386014320165765

theorem tailTrace_1257740 : CollatzResearch.WordTrace tailWord_1257740 prefixEnd_1257740 645825158386014320165765 := by
  unfold tailWord_1257740
  simp only [CollatzResearch.WordTrace]
  refine ⟨22936773231715129867809337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30582364308953506490412449 22936773231715129867809337)
  ·
    refine ⟨17202579923786347400857003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22936773231715129867809337 17202579923786347400857003)
    ·
      refine ⟨25803869885679521101285505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17202579923786347400857003 25803869885679521101285505)
      ·
        refine ⟨19352902414259640825964129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25803869885679521101285505 19352902414259640825964129)
        ·
          refine ⟨14514676810694730619473097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19352902414259640825964129 14514676810694730619473097)
          ·
            refine ⟨10886007608021047964604823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14514676810694730619473097 10886007608021047964604823)
            ·
              refine ⟨16329011412031571946907235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10886007608021047964604823 16329011412031571946907235)
              ·
                refine ⟨24493517118047357920360853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16329011412031571946907235 24493517118047357920360853)
                ·
                  refine ⟨1148133614908469902516915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24493517118047357920360853 1148133614908469902516915)
                  ·
                    refine ⟨1722200422362704853775373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1148133614908469902516915 1722200422362704853775373)
                    ·
                      refine ⟨645825158386014320165765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1722200422362704853775373 645825158386014320165765)
                      ·
                        rfl

theorem cell23_1257740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_1257740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257740 prefixEnd_1257740 := by exact prefixLift 1257740
  have htrace : WordTrace (prefixWord ++ tailWord_1257740) baseStart_1257740 baseEnd_1257740 := by
    simpa [prefixWord, tailWord_1257740, baseEnd_1257740] using wordTrace_append hprefix tailTrace_1257740
  have hstable : (prefixWord ++ tailWord_1257740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257740).length < 2 ^ (prefixWord ++ tailWord_1257740).sum := by decide
  have hdescent : baseEnd_1257740 < baseStart_1257740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257758 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1257758 : Nat := 118140960795 + 1257758 * 2 ^ 59
def prefixEnd_1257758 : Nat := 4983230072969 + 3 ^ 40 * 1257758 * 2
def baseEnd_1257758 : Nat := 645834401037795249740683

theorem tailTrace_1257758 : CollatzResearch.WordTrace tailWord_1257758 prefixEnd_1257758 645834401037795249740683 := by
  unfold tailWord_1257758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734275372170631101221741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30582801984910032539849285 5734275372170631101221741)
  ·
    refine ⟨2150353264563986662958153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5734275372170631101221741 2150353264563986662958153)
    ·
      refine ⟨1612764948422989997218615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2150353264563986662958153 1612764948422989997218615)
      ·
        refine ⟨2419147422634484995827923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612764948422989997218615 2419147422634484995827923)
        ·
          refine ⟨3628721133951727493741885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419147422634484995827923 3628721133951727493741885)
          ·
            refine ⟨1360770425231897810153207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3628721133951727493741885 1360770425231897810153207)
            ·
              refine ⟨2041155637847846715229811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360770425231897810153207 2041155637847846715229811)
              ·
                refine ⟨3061733456771770072844717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041155637847846715229811 3061733456771770072844717)
                ·
                  refine ⟨1148150046289413777316769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3061733456771770072844717 1148150046289413777316769)
                  ·
                    refine ⟨861112534717060332987577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1148150046289413777316769 861112534717060332987577)
                    ·
                      refine ⟨645834401037795249740683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861112534717060332987577 645834401037795249740683)
                      ·
                        rfl

theorem cell23_1257758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1257758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257758 prefixEnd_1257758 := by exact prefixLift 1257758
  have htrace : WordTrace (prefixWord ++ tailWord_1257758) baseStart_1257758 baseEnd_1257758 := by
    simpa [prefixWord, tailWord_1257758, baseEnd_1257758] using wordTrace_append hprefix tailTrace_1257758
  have hstable : (prefixWord ++ tailWord_1257758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257758).length < 2 ^ (prefixWord ++ tailWord_1257758).sum := by decide
  have hdescent : baseEnd_1257758 < baseStart_1257758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257763 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 4]
def baseStart_1257763 : Nat := 118140960795 + 1257763 * 2 ^ 59
def prefixEnd_1257763 : Nat := 4983230072969 + 3 ^ 40 * 1257763 * 2
def baseEnd_1257763 : Nat := 645836968441067730178159

theorem tailTrace_1257763 : CollatzResearch.WordTrace tailWord_1257763 prefixEnd_1257763 645836968441067730178159 := by
  unfold tailWord_1257763
  simp only [CollatzResearch.WordTrace]
  refine ⟨45874385342346934663705943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30582923561564623109137295 45874385342346934663705943)
  ·
    refine ⟨68811578013520401995558915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45874385342346934663705943 68811578013520401995558915)
    ·
      refine ⟨103217367020280602993338373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68811578013520401995558915 103217367020280602993338373)
      ·
        refine ⟨19353256316302613061250945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103217367020280602993338373 19353256316302613061250945)
        ·
          refine ⟨14514942237226959795938209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19353256316302613061250945 14514942237226959795938209)
          ·
            refine ⟨10886206677920219846953657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14514942237226959795938209 10886206677920219846953657)
            ·
              refine ⟨8164655008440164885215243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10886206677920219846953657 8164655008440164885215243)
              ·
                refine ⟨12246982512660247327822865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8164655008440164885215243 12246982512660247327822865)
                ·
                  refine ⟨9185236884495185495867149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12246982512660247327822865 9185236884495185495867149)
                  ·
                    refine ⟨3444463831685694560950181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9185236884495185495867149 3444463831685694560950181)
                    ·
                      refine ⟨645836968441067730178159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3444463831685694560950181 645836968441067730178159)
                      ·
                        rfl

theorem cell23_1257763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_1257763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257763 prefixEnd_1257763 := by exact prefixLift 1257763
  have htrace : WordTrace (prefixWord ++ tailWord_1257763) baseStart_1257763 baseEnd_1257763 := by
    simpa [prefixWord, tailWord_1257763, baseEnd_1257763] using wordTrace_append hprefix tailTrace_1257763
  have hstable : (prefixWord ++ tailWord_1257763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257763).length < 2 ^ (prefixWord ++ tailWord_1257763).sum := by decide
  have hdescent : baseEnd_1257763 < baseStart_1257763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257833 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 1, 7]
def baseStart_1257833 : Nat := 118140960795 + 1257833 * 2 ^ 59
def prefixEnd_1257833 : Nat := 4983230072969 + 3 ^ 40 * 1257833 * 2
def baseEnd_1257833 : Nat := 215290970695627485434279

theorem tailTrace_1257833 : CollatzResearch.WordTrace tailWord_1257833 prefixEnd_1257833 215290970695627485434279 := by
  unfold tailWord_1257833
  simp only [CollatzResearch.WordTrace]
  refine ⟨45876938452093336618754153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30584625634728891079169435 45876938452093336618754153)
  ·
    refine ⟨34407703839070002464065615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45876938452093336618754153 34407703839070002464065615)
    ·
      refine ⟨51611555758605003696098423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34407703839070002464065615 51611555758605003696098423)
      ·
        refine ⟨77417333637907505544147635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51611555758605003696098423 77417333637907505544147635)
        ·
          refine ⟨116126000456861258316221453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77417333637907505544147635 116126000456861258316221453)
          ·
            refine ⟨43547250171322971868583045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116126000456861258316221453 43547250171322971868583045)
            ·
              refine ⟨8165109407123057225359321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43547250171322971868583045 8165109407123057225359321)
              ·
                refine ⟨6123832055342292919019491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8165109407123057225359321 6123832055342292919019491)
                ·
                  refine ⟨9185748083013439378529237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6123832055342292919019491 9185748083013439378529237)
                  ·
                    refine ⟨215290970695627485434279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9185748083013439378529237 215290970695627485434279)
                    ·
                      rfl

theorem cell23_1257833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_1257833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257833 prefixEnd_1257833 := by exact prefixLift 1257833
  have htrace : WordTrace (prefixWord ++ tailWord_1257833) baseStart_1257833 baseEnd_1257833 := by
    simpa [prefixWord, tailWord_1257833, baseEnd_1257833] using wordTrace_append hprefix tailTrace_1257833
  have hstable : (prefixWord ++ tailWord_1257833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257833).length < 2 ^ (prefixWord ++ tailWord_1257833).sum := by decide
  have hdescent : baseEnd_1257833 < baseStart_1257833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257887 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 2, 4, 2]
def baseStart_1257887 : Nat := 118140960795 + 1257887 * 2 ^ 59
def prefixEnd_1257887 : Nat := 4983230072969 + 3 ^ 40 * 1257887 * 2
def baseEnd_1257887 : Nat := 645900640042225245027589

theorem tailTrace_1257887 : CollatzResearch.WordTrace tailWord_1257887 prefixEnd_1257887 645900640042225245027589 := by
  unfold tailWord_1257887
  simp only [CollatzResearch.WordTrace]
  refine ⟨45878907993897703841219915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30585938662598469227479943 45878907993897703841219915)
  ·
    refine ⟨68818361990846555761829873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45878907993897703841219915 68818361990846555761829873)
    ·
      refine ⟨51613771493134916821372405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68818361990846555761829873 51613771493134916821372405)
      ·
        refine ⟨4838791077481398452003663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51613771493134916821372405 4838791077481398452003663)
        ·
          refine ⟨7258186616222097678005495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4838791077481398452003663 7258186616222097678005495)
          ·
            refine ⟨10887279924333146517008243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7258186616222097678005495 10887279924333146517008243)
            ·
              refine ⟨16330919886499719775512365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10887279924333146517008243 16330919886499719775512365)
              ·
                refine ⟨6124094957437394915817137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16330919886499719775512365 6124094957437394915817137)
                ·
                  refine ⟨4593071218078046186862853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6124094957437394915817137 4593071218078046186862853)
                  ·
                    refine ⟨861200853389633660036785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593071218078046186862853 861200853389633660036785)
                    ·
                      refine ⟨645900640042225245027589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861200853389633660036785 645900640042225245027589)
                      ·
                        rfl

theorem cell23_1257887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_1257887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257887 prefixEnd_1257887 := by exact prefixLift 1257887
  have htrace : WordTrace (prefixWord ++ tailWord_1257887) baseStart_1257887 baseEnd_1257887 := by
    simpa [prefixWord, tailWord_1257887, baseEnd_1257887] using wordTrace_append hprefix tailTrace_1257887
  have hstable : (prefixWord ++ tailWord_1257887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257887).length < 2 ^ (prefixWord ++ tailWord_1257887).sum := by decide
  have hdescent : baseEnd_1257887 < baseStart_1257887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257903 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_1257903 : Nat := 118140960795 + 1257903 * 2 ^ 59
def prefixEnd_1257903 : Nat := 4983230072969 + 3 ^ 40 * 1257903 * 2
def baseEnd_1257903 : Nat := 645908855732697182427515

theorem tailTrace_1257903 : CollatzResearch.WordTrace tailWord_1257903 prefixEnd_1257903 645908855732697182427515 := by
  unfold tailWord_1257903
  simp only [CollatzResearch.WordTrace]
  refine ⟨45879491561839738573802363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30586327707893159049201575 45879491561839738573802363)
  ·
    refine ⟨68819237342759607860703545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45879491561839738573802363 68819237342759607860703545)
    ·
      refine ⟨51614428007069705895527659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68819237342759607860703545 51614428007069705895527659)
      ·
        refine ⟨77421642010604558843291489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51614428007069705895527659 77421642010604558843291489)
        ·
          refine ⟨58066231507953419132468617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77421642010604558843291489 58066231507953419132468617)
          ·
            refine ⟨43549673630965064349351463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58066231507953419132468617 43549673630965064349351463)
            ·
              refine ⟨65324510446447596524027195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43549673630965064349351463 65324510446447596524027195)
              ·
                refine ⟨97986765669671394786040793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65324510446447596524027195 97986765669671394786040793)
                ·
                  refine ⟨73490074252253546089530595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97986765669671394786040793 73490074252253546089530595)
                  ·
                    refine ⟨110235111378380319134295893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73490074252253546089530595 110235111378380319134295893)
                    ·
                      refine ⟨645908855732697182427515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 110235111378380319134295893 645908855732697182427515)
                      ·
                        rfl

theorem cell23_1257903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_1257903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257903 prefixEnd_1257903 := by exact prefixLift 1257903
  have htrace : WordTrace (prefixWord ++ tailWord_1257903) baseStart_1257903 baseEnd_1257903 := by
    simpa [prefixWord, tailWord_1257903, baseEnd_1257903] using wordTrace_append hprefix tailTrace_1257903
  have hstable : (prefixWord ++ tailWord_1257903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257903).length < 2 ^ (prefixWord ++ tailWord_1257903).sum := by decide
  have hdescent : baseEnd_1257903 < baseStart_1257903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257964 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 2, 3, 2]
def baseStart_1257964 : Nat := 118140960795 + 1257964 * 2 ^ 59
def prefixEnd_1257964 : Nat := 4983230072969 + 3 ^ 40 * 1257964 * 2
def baseEnd_1257964 : Nat := 645940178052621443764735

theorem tailTrace_1257964 : CollatzResearch.WordTrace tailWord_1257964 prefixEnd_1257964 645940178052621443764735 := by
  unfold tailWord_1257964
  simp only [CollatzResearch.WordTrace]
  refine ⟨22940858207309372995886473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30587810943079163994515297 22940858207309372995886473)
  ·
    refine ⟨17205643655482029746914855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22940858207309372995886473 17205643655482029746914855)
    ·
      refine ⟨25808465483223044620372283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17205643655482029746914855 25808465483223044620372283)
      ·
        refine ⟨38712698224834566930558425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25808465483223044620372283 38712698224834566930558425)
        ·
          refine ⟨29034523668625925197918819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38712698224834566930558425 29034523668625925197918819)
          ·
            refine ⟨43551785502938887796878229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29034523668625925197918819 43551785502938887796878229)
            ·
              refine ⟨2041489945450260365478667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43551785502938887796878229 2041489945450260365478667)
              ·
                refine ⟨3062234918175390548218001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041489945450260365478667 3062234918175390548218001)
                ·
                  refine ⟨2296676188631542911163501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3062234918175390548218001 2296676188631542911163501)
                  ·
                    refine ⟨861253570736828591686313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296676188631542911163501 861253570736828591686313)
                    ·
                      refine ⟨645940178052621443764735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861253570736828591686313 645940178052621443764735)
                      ·
                        rfl

theorem cell23_1257964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_1257964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257964 prefixEnd_1257964 := by exact prefixLift 1257964
  have htrace : WordTrace (prefixWord ++ tailWord_1257964) baseStart_1257964 baseEnd_1257964 := by
    simpa [prefixWord, tailWord_1257964, baseEnd_1257964] using wordTrace_append hprefix tailTrace_1257964
  have hstable : (prefixWord ++ tailWord_1257964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257964).length < 2 ^ (prefixWord ++ tailWord_1257964).sum := by decide
  have hdescent : baseEnd_1257964 < baseStart_1257964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257977 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 4]
def baseStart_1257977 : Nat := 118140960795 + 1257977 * 2 ^ 59
def prefixEnd_1257977 : Nat := 4983230072969 + 3 ^ 40 * 1257977 * 2
def baseEnd_1257977 : Nat := 645946853301129892902175

theorem tailTrace_1257977 : CollatzResearch.WordTrace tailWord_1257977 prefixEnd_1257977 645946853301129892902175 := by
  unfold tailWord_1257977
  simp only [CollatzResearch.WordTrace]
  refine ⟨45882190563571649211996185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30588127042381099474664123 45882190563571649211996185)
  ·
    refine ⟨34411642922678736908997139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45882190563571649211996185 34411642922678736908997139)
    ·
      refine ⟨51617464384018105363495709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34411642922678736908997139 51617464384018105363495709)
      ·
        refine ⟨19356549144006789511310891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51617464384018105363495709 19356549144006789511310891)
        ·
          refine ⟨29034823716010184266966337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19356549144006789511310891 29034823716010184266966337)
          ·
            refine ⟨21776117787007638200224753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29034823716010184266966337 21776117787007638200224753)
            ·
              refine ⟨16332088340255728650168565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21776117787007638200224753 16332088340255728650168565)
              ·
                refine ⟨1531133281898974560953303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16332088340255728650168565 1531133281898974560953303)
                ·
                  refine ⟨2296699922848461841429955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531133281898974560953303 2296699922848461841429955)
                  ·
                    refine ⟨3445049884272692762144933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2296699922848461841429955 3445049884272692762144933)
                    ·
                      refine ⟨645946853301129892902175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3445049884272692762144933 645946853301129892902175)
                      ·
                        rfl

theorem cell23_1257977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_1257977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257977 prefixEnd_1257977 := by exact prefixLift 1257977
  have htrace : WordTrace (prefixWord ++ tailWord_1257977) baseStart_1257977 baseEnd_1257977 := by
    simpa [prefixWord, tailWord_1257977, baseEnd_1257977] using wordTrace_append hprefix tailTrace_1257977
  have hstable : (prefixWord ++ tailWord_1257977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257977).length < 2 ^ (prefixWord ++ tailWord_1257977).sum := by decide
  have hdescent : baseEnd_1257977 < baseStart_1257977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257988 : List Nat := [2, 3, 2, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_1257988 : Nat := 118140960795 + 1257988 * 2 ^ 59
def prefixEnd_1257988 : Nat := 4983230072969 + 3 ^ 40 * 1257988 * 2
def baseEnd_1257988 : Nat := 645952501588329349864625

theorem tailTrace_1257988 : CollatzResearch.WordTrace tailWord_1257988 prefixEnd_1257988 645952501588329349864625 := by
  unfold tailWord_1257988
  simp only [CollatzResearch.WordTrace]
  refine ⟨22941295883265899045323309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30588394511021198727097745 22941295883265899045323309)
  ·
    refine ⟨8602985956224712141996241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22941295883265899045323309 8602985956224712141996241)
    ·
      refine ⟨6452239467168534106497181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8602985956224712141996241 6452239467168534106497181)
      ·
        refine ⟨2419589800188200289936443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6452239467168534106497181 2419589800188200289936443)
        ·
          refine ⟨3629384700282300434904665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419589800188200289936443 3629384700282300434904665)
          ·
            refine ⟨2722038525211725326178499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3629384700282300434904665 2722038525211725326178499)
            ·
              refine ⟨4083057787817587989267749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2722038525211725326178499 4083057787817587989267749)
              ·
                refine ⟨765573335215797747987703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4083057787817587989267749 765573335215797747987703)
                ·
                  refine ⟨1148360002823696621981555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765573335215797747987703 1148360002823696621981555)
                  ·
                    refine ⟨1722540004235544932972333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1148360002823696621981555 1722540004235544932972333)
                    ·
                      refine ⟨645952501588329349864625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1722540004235544932972333 645952501588329349864625)
                      ·
                        rfl

theorem cell23_1257988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_1257988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1257988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1257988 prefixEnd_1257988 := by exact prefixLift 1257988
  have htrace : WordTrace (prefixWord ++ tailWord_1257988) baseStart_1257988 baseEnd_1257988 := by
    simpa [prefixWord, tailWord_1257988, baseEnd_1257988] using wordTrace_append hprefix tailTrace_1257988
  have hstable : (prefixWord ++ tailWord_1257988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257988).length < 2 ^ (prefixWord ++ tailWord_1257988).sum := by decide
  have hdescent : baseEnd_1257988 < baseStart_1257988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258004 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1258004 : Nat := 118140960795 + 1258004 * 2 ^ 59
def prefixEnd_1258004 : Nat := 4983230072969 + 3 ^ 40 * 1258004 * 2
def baseEnd_1258004 : Nat := 215320239092933762421517

theorem tailTrace_1258004 : CollatzResearch.WordTrace tailWord_1258004 prefixEnd_1258004 215320239092933762421517 := by
  unfold tailWord_1258004
  simp only [CollatzResearch.WordTrace]
  refine ⟨22941587667236916411614533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30588783556315888548819377 22941587667236916411614533)
  ·
    refine ⟨4301547687606921827177725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22941587667236916411614533 4301547687606921827177725)
    ·
      refine ⟨1613080382852595685191647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4301547687606921827177725 1613080382852595685191647)
      ·
        refine ⟨2419620574278893527787471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613080382852595685191647 2419620574278893527787471)
        ·
          refine ⟨3629430861418340291681207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419620574278893527787471 3629430861418340291681207)
          ·
            refine ⟨5444146292127510437521811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629430861418340291681207 5444146292127510437521811)
            ·
              refine ⟨8166219438191265656282717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444146292127510437521811 8166219438191265656282717)
              ·
                refine ⟨3062332289321724621106019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8166219438191265656282717 3062332289321724621106019)
                ·
                  refine ⟨4593498433982586931659029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062332289321724621106019 4593498433982586931659029)
                  ·
                    refine ⟨215320239092933762421517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4593498433982586931659029 215320239092933762421517)
                    ·
                      rfl

theorem cell23_1258004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1258004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258004 prefixEnd_1258004 := by exact prefixLift 1258004
  have htrace : WordTrace (prefixWord ++ tailWord_1258004) baseStart_1258004 baseEnd_1258004 := by
    simpa [prefixWord, tailWord_1258004, baseEnd_1258004] using wordTrace_append hprefix tailTrace_1258004
  have hstable : (prefixWord ++ tailWord_1258004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258004).length < 2 ^ (prefixWord ++ tailWord_1258004).sum := by decide
  have hdescent : baseEnd_1258004 < baseStart_1258004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258017 : List Nat := [1, 2, 3, 2, 2, 1, 5, 7]
def baseStart_1258017 : Nat := 118140960795 + 1258017 * 2 ^ 59
def prefixEnd_1258017 : Nat := 4983230072969 + 3 ^ 40 * 1258017 * 2
def baseEnd_1258017 : Nat := 23924718241752212459333

theorem tailTrace_1258017 : CollatzResearch.WordTrace tailWord_1258017 prefixEnd_1258017 23924718241752212459333 := by
  unfold tailWord_1258017
  simp only [CollatzResearch.WordTrace]
  refine ⟨45883649483426736043452305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30589099655617824028968203 45883649483426736043452305)
  ·
    refine ⟨34412737112570052032589229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45883649483426736043452305 34412737112570052032589229)
    ·
      refine ⟨12904776417213769512220961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34412737112570052032589229 12904776417213769512220961)
      ·
        refine ⟨9678582312910327134165721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12904776417213769512220961 9678582312910327134165721)
        ·
          refine ⟨7258936734682745350624291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9678582312910327134165721 7258936734682745350624291)
          ·
            refine ⟨10888405102024118025936437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7258936734682745350624291 10888405102024118025936437)
            ·
              refine ⟨1020787978314761064931541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10888405102024118025936437 1020787978314761064931541)
              ·
                refine ⟨23924718241752212459333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1020787978314761064931541 23924718241752212459333)
                ·
                  rfl

theorem cell23_1258017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 7].length) (baseStart_1258017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258017 prefixEnd_1258017 := by exact prefixLift 1258017
  have htrace : WordTrace (prefixWord ++ tailWord_1258017) baseStart_1258017 baseEnd_1258017 := by
    simpa [prefixWord, tailWord_1258017, baseEnd_1258017] using wordTrace_append hprefix tailTrace_1258017
  have hstable : (prefixWord ++ tailWord_1258017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258017).length < 2 ^ (prefixWord ++ tailWord_1258017).sum := by decide
  have hdescent : baseEnd_1258017 < baseStart_1258017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258024 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1258024 : Nat := 118140960795 + 1258024 * 2 ^ 59
def prefixEnd_1258024 : Nat := 4983230072969 + 3 ^ 40 * 1258024 * 2
def baseEnd_1258024 : Nat := 645970986891891209014459

theorem tailTrace_1258024 : CollatzResearch.WordTrace tailWord_1258024 prefixEnd_1258024 645970986891891209014459 := by
  unfold tailWord_1258024
  simp only [CollatzResearch.WordTrace]
  refine ⟨22941952397200688119478563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30589269862934250825971417 22941952397200688119478563)
  ·
    refine ⟨34412928595801032179217845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22941952397200688119478563 34412928595801032179217845)
    ·
      refine ⟨3226212055856346766801673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34412928595801032179217845 3226212055856346766801673)
      ·
        refine ⟨2419659041892260075101255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3226212055856346766801673 2419659041892260075101255)
        ·
          refine ⟨3629488562838390112651883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419659041892260075101255 3629488562838390112651883)
          ·
            refine ⟨5444232844257585168977825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629488562838390112651883 5444232844257585168977825)
            ·
              refine ⟨4083174633193188876733369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5444232844257585168977825 4083174633193188876733369)
              ·
                refine ⟨3062380974894891657550027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4083174633193188876733369 3062380974894891657550027)
                ·
                  refine ⟨4593571462342337486325041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062380974894891657550027 4593571462342337486325041)
                  ·
                    refine ⟨3445178596756753114743781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4593571462342337486325041 3445178596756753114743781)
                    ·
                      refine ⟨645970986891891209014459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3445178596756753114743781 645970986891891209014459)
                      ·
                        rfl

theorem cell23_1258024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1258024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258024 prefixEnd_1258024 := by exact prefixLift 1258024
  have htrace : WordTrace (prefixWord ++ tailWord_1258024) baseStart_1258024 baseEnd_1258024 := by
    simpa [prefixWord, tailWord_1258024, baseEnd_1258024] using wordTrace_append hprefix tailTrace_1258024
  have hstable : (prefixWord ++ tailWord_1258024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258024).length < 2 ^ (prefixWord ++ tailWord_1258024).sum := by decide
  have hdescent : baseEnd_1258024 < baseStart_1258024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258038 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1258038 : Nat := 118140960795 + 1258038 * 2 ^ 59
def prefixEnd_1258038 : Nat := 4983230072969 + 3 ^ 40 * 1258038 * 2
def baseEnd_1258038 : Nat := 215326058540351384746465

theorem tailTrace_1258038 : CollatzResearch.WordTrace tailWord_1258038 prefixEnd_1258038 215326058540351384746465 := by
  unfold tailWord_1258038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2867775963521916039372923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30589610277567104419977845 2867775963521916039372923)
  ·
    refine ⟨4301663945282874059059385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2867775963521916039372923 4301663945282874059059385)
    ·
      refine ⟨3226247958962155544294539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4301663945282874059059385 3226247958962155544294539)
      ·
        refine ⟨4839371938443233316441809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3226247958962155544294539 4839371938443233316441809)
        ·
          refine ⟨3629528953832424987331357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4839371938443233316441809 3629528953832424987331357)
          ·
            refine ⟨1361073357687159370249259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3629528953832424987331357 1361073357687159370249259)
            ·
              refine ⟨2041610036530739055373889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361073357687159370249259 2041610036530739055373889)
              ·
                refine ⟨1531207527398054291530417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041610036530739055373889 1531207527398054291530417)
                ·
                  refine ⟨1148405645548540718647813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1531207527398054291530417 1148405645548540718647813)
                  ·
                    refine ⟨215326058540351384746465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1148405645548540718647813 215326058540351384746465)
                    ·
                      rfl

theorem cell23_1258038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1258038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258038 prefixEnd_1258038 := by exact prefixLift 1258038
  have htrace : WordTrace (prefixWord ++ tailWord_1258038) baseStart_1258038 baseEnd_1258038 := by
    simpa [prefixWord, tailWord_1258038, baseEnd_1258038] using wordTrace_append hprefix tailTrace_1258038
  have hstable : (prefixWord ++ tailWord_1258038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258038).length < 2 ^ (prefixWord ++ tailWord_1258038).sum := by decide
  have hdescent : baseEnd_1258038 < baseStart_1258038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258061 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1258061 : Nat := 118140960795 + 1258061 * 2 ^ 59
def prefixEnd_1258061 : Nat := 4983230072969 + 3 ^ 40 * 1258061 * 2
def baseEnd_1258061 : Nat := 645989985676107564251789

theorem tailTrace_1258061 : CollatzResearch.WordTrace tailWord_1258061 prefixEnd_1258061 645989985676107564251789 := by
  unfold tailWord_1258061
  simp only [CollatzResearch.WordTrace]
  refine ⟨45885254295267331558054037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30590169530178221038702691 45885254295267331558054037)
  ·
    refine ⟨2150871295090656166783783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45885254295267331558054037 2150871295090656166783783)
    ·
      refine ⟨3226306942635984250175675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2150871295090656166783783 3226306942635984250175675)
      ·
        refine ⟨4839460413953976375263513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3226306942635984250175675 4839460413953976375263513)
        ·
          refine ⟨3629595310465482281447635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4839460413953976375263513 3629595310465482281447635)
          ·
            refine ⟨5444392965698223422171453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629595310465482281447635 5444392965698223422171453)
            ·
              refine ⟨2041647362136833783314295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5444392965698223422171453 2041647362136833783314295)
              ·
                refine ⟨3062471043205250674971443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041647362136833783314295 3062471043205250674971443)
                ·
                  refine ⟨4593706564807876012457165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062471043205250674971443 4593706564807876012457165)
                  ·
                    refine ⟨1722639961802953504671437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4593706564807876012457165 1722639961802953504671437)
                    ·
                      refine ⟨645989985676107564251789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1722639961802953504671437 645989985676107564251789)
                      ·
                        rfl

theorem cell23_1258061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1258061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258061 prefixEnd_1258061 := by exact prefixLift 1258061
  have htrace : WordTrace (prefixWord ++ tailWord_1258061) baseStart_1258061 baseEnd_1258061 := by
    simpa [prefixWord, tailWord_1258061, baseEnd_1258061] using wordTrace_append hprefix tailTrace_1258061
  have hstable : (prefixWord ++ tailWord_1258061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258061).length < 2 ^ (prefixWord ++ tailWord_1258061).sum := by decide
  have hdescent : baseEnd_1258061 < baseStart_1258061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258071 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 1, 3, 2]
def baseStart_1258071 : Nat := 118140960795 + 1258071 * 2 ^ 59
def prefixEnd_1258071 : Nat := 4983230072969 + 3 ^ 40 * 1258071 * 2
def baseEnd_1258071 : Nat := 645995120482652525126743

theorem tailTrace_1258071 : CollatzResearch.WordTrace tailWord_1258071 prefixEnd_1258071 645995120482652525126743 := by
  unfold tailWord_1258071
  simp only [CollatzResearch.WordTrace]
  refine ⟨45885619025231103265918067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30590412683487402177278711 45885619025231103265918067)
  ·
    refine ⟨68828428537846654898877101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45885619025231103265918067 68828428537846654898877101)
    ·
      refine ⟨25810660701692495587078913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68828428537846654898877101 25810660701692495587078913)
      ·
        refine ⟨19357995526269371690309185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25810660701692495587078913 19357995526269371690309185)
        ·
          refine ⟨14518496644702028767731889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19357995526269371690309185 14518496644702028767731889)
          ·
            refine ⟨10888872483526521575798917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14518496644702028767731889 10888872483526521575798917)
            ·
              refine ⟨2041663590661222795462297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10888872483526521575798917 2041663590661222795462297)
              ·
                refine ⟨1531247692995917096596723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041663590661222795462297 1531247692995917096596723)
                ·
                  refine ⟨2296871539493875644895085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531247692995917096596723 2296871539493875644895085)
                  ·
                    refine ⟨861326827310203366835657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296871539493875644895085 861326827310203366835657)
                    ·
                      refine ⟨645995120482652525126743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861326827310203366835657 645995120482652525126743)
                      ·
                        rfl

theorem cell23_1258071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_1258071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258071 prefixEnd_1258071 := by exact prefixLift 1258071
  have htrace : WordTrace (prefixWord ++ tailWord_1258071) baseStart_1258071 baseEnd_1258071 := by
    simpa [prefixWord, tailWord_1258071, baseEnd_1258071] using wordTrace_append hprefix tailTrace_1258071
  have hstable : (prefixWord ++ tailWord_1258071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258071).length < 2 ^ (prefixWord ++ tailWord_1258071).sum := by decide
  have hdescent : baseEnd_1258071 < baseStart_1258071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258084 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_1258084 : Nat := 118140960795 + 1258084 * 2 ^ 59
def prefixEnd_1258084 : Nat := 4983230072969 + 3 ^ 40 * 1258084 * 2
def baseEnd_1258084 : Nat := 646001795731160974264183

theorem tailTrace_1258084 : CollatzResearch.WordTrace tailWord_1258084 prefixEnd_1258084 646001795731160974264183 := by
  unfold tailWord_1258084
  simp only [CollatzResearch.WordTrace]
  refine ⟨22943046587092003243070653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30590728782789337657427537 22943046587092003243070653)
  ·
    refine ⟨8603642470159501216151495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22943046587092003243070653 8603642470159501216151495)
    ·
      refine ⟨12905463705239251824227243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8603642470159501216151495 12905463705239251824227243)
      ·
        refine ⟨19358195557858877736340865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12905463705239251824227243 19358195557858877736340865)
        ·
          refine ⟨14518646668394158302255649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19358195557858877736340865 14518646668394158302255649)
          ·
            refine ⟨10888985001295618726691737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14518646668394158302255649 10888985001295618726691737)
            ·
              refine ⟨8166738750971714045018803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10888985001295618726691737 8166738750971714045018803)
              ·
                refine ⟨12250108126457571067528205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8166738750971714045018803 12250108126457571067528205)
                ·
                  refine ⟨4593790547421589150323077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12250108126457571067528205 4593790547421589150323077)
                  ·
                    refine ⟨861335727641547965685577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593790547421589150323077 861335727641547965685577)
                    ·
                      refine ⟨646001795731160974264183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861335727641547965685577 646001795731160974264183)
                      ·
                        rfl

theorem cell23_1258084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_1258084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258084 prefixEnd_1258084 := by exact prefixLift 1258084
  have htrace : WordTrace (prefixWord ++ tailWord_1258084) baseStart_1258084 baseEnd_1258084 := by
    simpa [prefixWord, tailWord_1258084, baseEnd_1258084] using wordTrace_append hprefix tailTrace_1258084
  have hstable : (prefixWord ++ tailWord_1258084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258084).length < 2 ^ (prefixWord ++ tailWord_1258084).sum := by decide
  have hdescent : baseEnd_1258084 < baseStart_1258084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258087 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_1258087 : Nat := 118140960795 + 1258087 * 2 ^ 59
def prefixEnd_1258087 : Nat := 4983230072969 + 3 ^ 40 * 1258087 * 2
def baseEnd_1258087 : Nat := 646003336173124462526669

theorem tailTrace_1258087 : CollatzResearch.WordTrace tailWord_1258087 prefixEnd_1258087 646003336173124462526669 := by
  unfold tailWord_1258087
  simp only [CollatzResearch.WordTrace]
  refine ⟨45886202593173137998500515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30590801728782091999000343 45886202593173137998500515)
  ·
    refine ⟨68829303889759706997750773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45886202593173137998500515 68829303889759706997750773)
    ·
      refine ⟨6452747239664972531039135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68829303889759706997750773 6452747239664972531039135)
      ·
        refine ⟨9679120859497458796558703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6452747239664972531039135 9679120859497458796558703)
        ·
          refine ⟨14518681289246188194838055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9679120859497458796558703 14518681289246188194838055)
          ·
            refine ⟨21778021933869282292257083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14518681289246188194838055 21778021933869282292257083)
            ·
              refine ⟨32667032900803923438385625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21778021933869282292257083 32667032900803923438385625)
              ·
                refine ⟨24500274675602942578789219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32667032900803923438385625 24500274675602942578789219)
                ·
                  refine ⟨36750412013404413868183829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24500274675602942578789219 36750412013404413868183829)
                  ·
                    refine ⟨1722675563128331900071117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36750412013404413868183829 1722675563128331900071117)
                    ·
                      refine ⟨646003336173124462526669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1722675563128331900071117 646003336173124462526669)
                      ·
                        rfl

theorem cell23_1258087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_1258087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258087 prefixEnd_1258087 := by exact prefixLift 1258087
  have htrace : WordTrace (prefixWord ++ tailWord_1258087) baseStart_1258087 baseEnd_1258087 := by
    simpa [prefixWord, tailWord_1258087, baseEnd_1258087] using wordTrace_append hprefix tailTrace_1258087
  have hstable : (prefixWord ++ tailWord_1258087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258087).length < 2 ^ (prefixWord ++ tailWord_1258087).sum := by decide
  have hdescent : baseEnd_1258087 < baseStart_1258087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258158 : List Nat := [4, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_1258158 : Nat := 118140960795 + 1258158 * 2 ^ 59
def prefixEnd_1258158 : Nat := 4983230072969 + 3 ^ 40 * 1258158 * 2
def baseEnd_1258158 : Nat := 71782199255510409415427

theorem tailTrace_1258158 : CollatzResearch.WordTrace tailWord_1258158 prefixEnd_1258158 71782199255510409415427 := by
  unfold tailWord_1258158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736099021989489640541891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30592528117277278082890085 5736099021989489640541891)
  ·
    refine ⟨8604148532984234460812837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5736099021989489640541891 8604148532984234460812837)
    ·
      refine ⟨1613277849934543961402407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8604148532984234460812837 1613277849934543961402407)
      ·
        refine ⟨2419916774901815942103611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613277849934543961402407 2419916774901815942103611)
        ·
          refine ⟨3629875162352723913155417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419916774901815942103611 3629875162352723913155417)
          ·
            refine ⟨2722406371764542934866563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3629875162352723913155417 2722406371764542934866563)
            ·
              refine ⟨4083609557646814402299845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2722406371764542934866563 4083609557646814402299845)
              ·
                refine ⟨765676792058777700431221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4083609557646814402299845 765676792058777700431221)
                ·
                  refine ⟨71782199255510409415427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 765676792058777700431221 71782199255510409415427)
                  ·
                    rfl

theorem cell23_1258158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_1258158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258158 prefixEnd_1258158 := by exact prefixLift 1258158
  have htrace : WordTrace (prefixWord ++ tailWord_1258158) baseStart_1258158 baseEnd_1258158 := by
    simpa [prefixWord, tailWord_1258158, baseEnd_1258158] using wordTrace_append hprefix tailTrace_1258158
  have hstable : (prefixWord ++ tailWord_1258158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258158).length < 2 ^ (prefixWord ++ tailWord_1258158).sum := by decide
  have hdescent : baseEnd_1258158 < baseStart_1258158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258174 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1258174 : Nat := 118140960795 + 1258174 * 2 ^ 59
def prefixEnd_1258174 : Nat := 4983230072969 + 3 ^ 40 * 1258174 * 2
def baseEnd_1258174 : Nat := 646048008990065622138769

theorem tailTrace_1258174 : CollatzResearch.WordTrace tailWord_1258174 prefixEnd_1258174 646048008990065622138769 := by
  unfold tailWord_1258174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736171967982243982114697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30592917162571967904611717 5736171967982243982114697)
  ·
    refine ⟨4302128975986682986586023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5736171967982243982114697 4302128975986682986586023)
    ·
      refine ⟨6453193463980024479879035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4302128975986682986586023 6453193463980024479879035)
      ·
        refine ⟨9679790195970036719818553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6453193463980024479879035 9679790195970036719818553)
        ·
          refine ⟨7259842646977527539863915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9679790195970036719818553 7259842646977527539863915)
          ·
            refine ⟨10889763970466291309795873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7259842646977527539863915 10889763970466291309795873)
            ·
              refine ⟨8167322977849718482346905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10889763970466291309795873 8167322977849718482346905)
              ·
                refine ⟨6125492233387288861760179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8167322977849718482346905 6125492233387288861760179)
                ·
                  refine ⟨9188238350080933292640269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6125492233387288861760179 9188238350080933292640269)
                  ·
                    refine ⟨3445589381280349984740101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9188238350080933292640269 3445589381280349984740101)
                    ·
                      refine ⟨646048008990065622138769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3445589381280349984740101 646048008990065622138769)
                      ·
                        rfl

theorem cell23_1258174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1258174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258174 prefixEnd_1258174 := by exact prefixLift 1258174
  have htrace : WordTrace (prefixWord ++ tailWord_1258174) baseStart_1258174 baseEnd_1258174 := by
    simpa [prefixWord, tailWord_1258174, baseEnd_1258174] using wordTrace_append hprefix tailTrace_1258174
  have hstable : (prefixWord ++ tailWord_1258174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258174).length < 2 ^ (prefixWord ++ tailWord_1258174).sum := by decide
  have hdescent : baseEnd_1258174 < baseStart_1258174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258184 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 5, 4]
def baseStart_1258184 : Nat := 118140960795 + 1258184 * 2 ^ 59
def prefixEnd_1258184 : Nat := 4983230072969 + 3 ^ 40 * 1258184 * 2
def baseEnd_1258184 : Nat := 215351047932203527671241

theorem tailTrace_1258184 : CollatzResearch.WordTrace tailWord_1258184 prefixEnd_1258184 215351047932203527671241 := by
  unfold tailWord_1258184
  simp only [CollatzResearch.WordTrace]
  refine ⟨22944870236910861782390803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30593160315881149043187737 22944870236910861782390803)
  ·
    refine ⟨34417305355366292673586205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22944870236910861782390803 34417305355366292673586205)
    ·
      refine ⟨12906489508262359752594827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34417305355366292673586205 12906489508262359752594827)
      ·
        refine ⟨19359734262393539628892241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12906489508262359752594827 19359734262393539628892241)
        ·
          refine ⟨14519800696795154721669181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19359734262393539628892241 14519800696795154721669181)
          ·
            refine ⟨5444925261298183020625943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14519800696795154721669181 5444925261298183020625943)
            ·
              refine ⟨8167387891947274530938915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444925261298183020625943 8167387891947274530938915)
              ·
                refine ⟨12251081837920911796408373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8167387891947274530938915 12251081837920911796408373)
                ·
                  refine ⟨1148538922305085480913285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12251081837920911796408373 1148538922305085480913285)
                  ·
                    refine ⟨215351047932203527671241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1148538922305085480913285 215351047932203527671241)
                    ·
                      rfl

theorem cell23_1258184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_1258184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258184 prefixEnd_1258184 := by exact prefixLift 1258184
  have htrace : WordTrace (prefixWord ++ tailWord_1258184) baseStart_1258184 baseEnd_1258184 := by
    simpa [prefixWord, tailWord_1258184, baseEnd_1258184] using wordTrace_append hprefix tailTrace_1258184
  have hstable : (prefixWord ++ tailWord_1258184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258184).length < 2 ^ (prefixWord ++ tailWord_1258184).sum := by decide
  have hdescent : baseEnd_1258184 < baseStart_1258184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258217 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_1258217 : Nat := 118140960795 + 1258217 * 2 ^ 59
def prefixEnd_1258217 : Nat := 4983230072969 + 3 ^ 40 * 1258217 * 2
def baseEnd_1258217 : Nat := 646070088658208953901071

theorem tailTrace_1258217 : CollatzResearch.WordTrace tailWord_1258217 prefixEnd_1258217 646070088658208953901071 := by
  unfold tailWord_1258217
  simp only [CollatzResearch.WordTrace]
  refine ⟨45890944082702170200732905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30593962721801446800488603 45890944082702170200732905)
  ·
    refine ⟨34418208062026627650549679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45890944082702170200732905 34418208062026627650549679)
    ·
      refine ⟨51627312093039941475824519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34418208062026627650549679 51627312093039941475824519)
      ·
        refine ⟨77440968139559912213736779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51627312093039941475824519 77440968139559912213736779)
        ·
          refine ⟨116161452209339868320605169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77440968139559912213736779 116161452209339868320605169)
          ·
            refine ⟨87121089157004901240453877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116161452209339868320605169 87121089157004901240453877)
            ·
              refine ⟨8167602108469209491292551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87121089157004901240453877 8167602108469209491292551)
              ·
                refine ⟨12251403162703814236938827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8167602108469209491292551 12251403162703814236938827)
                ·
                  refine ⟨18377104744055721355408241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12251403162703814236938827 18377104744055721355408241)
                  ·
                    refine ⟨13782828558041791016556181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18377104744055721355408241 13782828558041791016556181)
                    ·
                      refine ⟨646070088658208953901071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13782828558041791016556181 646070088658208953901071)
                      ·
                        rfl

theorem cell23_1258217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_1258217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258217 prefixEnd_1258217 := by exact prefixLift 1258217
  have htrace : WordTrace (prefixWord ++ tailWord_1258217) baseStart_1258217 baseEnd_1258217 := by
    simpa [prefixWord, tailWord_1258217, baseEnd_1258217] using wordTrace_append hprefix tailTrace_1258217
  have hstable : (prefixWord ++ tailWord_1258217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258217).length < 2 ^ (prefixWord ++ tailWord_1258217).sum := by decide
  have hdescent : baseEnd_1258217 < baseStart_1258217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258251 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 2, 3, 2]
def baseStart_1258251 : Nat := 118140960795 + 1258251 * 2 ^ 59
def prefixEnd_1258251 : Nat := 4983230072969 + 3 ^ 40 * 1258251 * 2
def baseEnd_1258251 : Nat := 646087547000461820875915

theorem tailTrace_1258251 : CollatzResearch.WordTrace tailWord_1258251 prefixEnd_1258251 646087547000461820875915 := by
  unfold tailWord_1258251
  simp only [CollatzResearch.WordTrace]
  refine ⟨45892184164578994007470607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30594789443052662671647071 45892184164578994007470607)
  ·
    refine ⟨68838276246868491011205911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45892184164578994007470607 68838276246868491011205911)
    ·
      refine ⟨103257414370302736516808867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68838276246868491011205911 103257414370302736516808867)
      ·
        refine ⟨154886121555454104775213301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103257414370302736516808867 154886121555454104775213301)
        ·
          refine ⟨14520573895823822322676247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154886121555454104775213301 14520573895823822322676247)
          ·
            refine ⟨21780860843735733484014371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14520573895823822322676247 21780860843735733484014371)
            ·
              refine ⟨32671291265603600226021557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21780860843735733484014371 32671291265603600226021557)
              ·
                refine ⟨3062933556150337521189521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32671291265603600226021557 3062933556150337521189521)
                ·
                  refine ⟨2297200167112753140892141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3062933556150337521189521 2297200167112753140892141)
                  ·
                    refine ⟨861450062667282427834553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297200167112753140892141 861450062667282427834553)
                    ·
                      refine ⟨646087547000461820875915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861450062667282427834553 646087547000461820875915)
                      ·
                        rfl

theorem cell23_1258251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 3, 2].length) (baseStart_1258251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258251 prefixEnd_1258251 := by exact prefixLift 1258251
  have htrace : WordTrace (prefixWord ++ tailWord_1258251) baseStart_1258251 baseEnd_1258251 := by
    simpa [prefixWord, tailWord_1258251, baseEnd_1258251] using wordTrace_append hprefix tailTrace_1258251
  have hstable : (prefixWord ++ tailWord_1258251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258251).length < 2 ^ (prefixWord ++ tailWord_1258251).sum := by decide
  have hdescent : baseEnd_1258251 < baseStart_1258251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258264 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1258264 : Nat := 118140960795 + 1258264 * 2 ^ 59
def prefixEnd_1258264 : Nat := 4983230072969 + 3 ^ 40 * 1258264 * 2
def baseEnd_1258264 : Nat := 646094222248970270013355

theorem tailTrace_1258264 : CollatzResearch.WordTrace tailWord_1258264 prefixEnd_1258264 646094222248970270013355 := by
  unfold tailWord_1258264
  simp only [CollatzResearch.WordTrace]
  refine ⟨22946329156765948613846923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30595105542354598151795897 22946329156765948613846923)
  ·
    refine ⟨34419493735148922920770385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22946329156765948613846923 34419493735148922920770385)
    ·
      refine ⟨25814620301361692190577789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34419493735148922920770385 25814620301361692190577789)
      ·
        refine ⟨9680482613010634571466671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25814620301361692190577789 9680482613010634571466671)
        ·
          refine ⟨14520723919515951857200007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9680482613010634571466671 14520723919515951857200007)
          ·
            refine ⟨21781085879273927785800011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14520723919515951857200007 21781085879273927785800011)
            ·
              refine ⟨32671628818910891678700017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21781085879273927785800011 32671628818910891678700017)
              ·
                refine ⟨24503721614183168759025013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32671628818910891678700017 24503721614183168759025013)
                ·
                  refine ⟨2297223901329672071158595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24503721614183168759025013 2297223901329672071158595)
                  ·
                    refine ⟨3445835851994508106737893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2297223901329672071158595 3445835851994508106737893)
                    ·
                      refine ⟨646094222248970270013355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3445835851994508106737893 646094222248970270013355)
                      ·
                        rfl

theorem cell23_1258264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1258264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258264 prefixEnd_1258264 := by exact prefixLift 1258264
  have htrace : WordTrace (prefixWord ++ tailWord_1258264) baseStart_1258264 baseEnd_1258264 := by
    simpa [prefixWord, tailWord_1258264, baseEnd_1258264] using wordTrace_append hprefix tailTrace_1258264
  have hstable : (prefixWord ++ tailWord_1258264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258264).length < 2 ^ (prefixWord ++ tailWord_1258264).sum := by decide
  have hdescent : baseEnd_1258264 < baseStart_1258264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258268 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_1258268 : Nat := 118140960795 + 1258268 * 2 ^ 59
def prefixEnd_1258268 : Nat := 4983230072969 + 3 ^ 40 * 1258268 * 2
def baseEnd_1258268 : Nat := 646096276171588254363337

theorem tailTrace_1258268 : CollatzResearch.WordTrace tailWord_1258268 prefixEnd_1258268 646096276171588254363337 := by
  unfold tailWord_1258268
  simp only [CollatzResearch.WordTrace]
  refine ⟨22946402102758702955419729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30595202803678270607226305 22946402102758702955419729)
  ·
    refine ⟨17209801577069027216564797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22946402102758702955419729 17209801577069027216564797)
    ·
      refine ⟨6453675591400885206211799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17209801577069027216564797 6453675591400885206211799)
      ·
        refine ⟨9680513387101327809317699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6453675591400885206211799 9680513387101327809317699)
        ·
          refine ⟨14520770080651991713976549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9680513387101327809317699 14520770080651991713976549)
          ·
            refine ⟨2722644390122248446370603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14520770080651991713976549 2722644390122248446370603)
            ·
              refine ⟨4083966585183372669555905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2722644390122248446370603 4083966585183372669555905)
              ·
                refine ⟨3062974938887529502166929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4083966585183372669555905 3062974938887529502166929)
                ·
                  refine ⟨2297231204165647126625197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3062974938887529502166929 2297231204165647126625197)
                  ·
                    refine ⟨861461701562117672484449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297231204165647126625197 861461701562117672484449)
                    ·
                      refine ⟨646096276171588254363337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861461701562117672484449 646096276171588254363337)
                      ·
                        rfl

theorem cell23_1258268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_1258268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258268 prefixEnd_1258268 := by exact prefixLift 1258268
  have htrace : WordTrace (prefixWord ++ tailWord_1258268) baseStart_1258268 baseEnd_1258268 := by
    simpa [prefixWord, tailWord_1258268, baseEnd_1258268] using wordTrace_append hprefix tailTrace_1258268
  have hstable : (prefixWord ++ tailWord_1258268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258268).length < 2 ^ (prefixWord ++ tailWord_1258268).sum := by decide
  have hdescent : baseEnd_1258268 < baseStart_1258268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258282 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 6]
def baseStart_1258282 : Nat := 118140960795 + 1258282 * 2 ^ 59
def prefixEnd_1258282 : Nat := 4983230072969 + 3 ^ 40 * 1258282 * 2
def baseEnd_1258282 : Nat := 71789273877861244398697

theorem tailTrace_1258282 : CollatzResearch.WordTrace tailWord_1258282 prefixEnd_1258282 71789273877861244398697 := by
  unfold tailWord_1258282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11473328706866671575462275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30595543218311124201232733 11473328706866671575462275)
  ·
    refine ⟨17209993060300007363193413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11473328706866671575462275 17209993060300007363193413)
    ·
      refine ⟨3226873698806251380598765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17209993060300007363193413 3226873698806251380598765)
      ·
        refine ⟨1210077637052344267724537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3226873698806251380598765 1210077637052344267724537)
        ·
          refine ⟨907558227789258200793403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1210077637052344267724537 907558227789258200793403)
          ·
            refine ⟨1361337341683887301190105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907558227789258200793403 1361337341683887301190105)
            ·
              refine ⟨1021003006262915475892579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361337341683887301190105 1021003006262915475892579)
              ·
                refine ⟨1531504509394373213838869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021003006262915475892579 1531504509394373213838869)
                ·
                  refine ⟨71789273877861244398697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1531504509394373213838869 71789273877861244398697)
                  ·
                    rfl

theorem cell23_1258282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_1258282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258282 prefixEnd_1258282 := by exact prefixLift 1258282
  have htrace : WordTrace (prefixWord ++ tailWord_1258282) baseStart_1258282 baseEnd_1258282 := by
    simpa [prefixWord, tailWord_1258282, baseEnd_1258282] using wordTrace_append hprefix tailTrace_1258282
  have hstable : (prefixWord ++ tailWord_1258282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258282).length < 2 ^ (prefixWord ++ tailWord_1258282).sum := by decide
  have hdescent : baseEnd_1258282 < baseStart_1258282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258284 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_1258284 : Nat := 118140960795 + 1258284 * 2 ^ 59
def prefixEnd_1258284 : Nat := 4983230072969 + 3 ^ 40 * 1258284 * 2
def baseEnd_1258284 : Nat := 646104491862060191763263

theorem tailTrace_1258284 : CollatzResearch.WordTrace tailWord_1258284 prefixEnd_1258284 646104491862060191763263 := by
  unfold tailWord_1258284
  simp only [CollatzResearch.WordTrace]
  refine ⟨22946693886729720321710953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30595591848972960428947937 22946693886729720321710953)
  ·
    refine ⟨17210020415047290241283215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22946693886729720321710953 17210020415047290241283215)
    ·
      refine ⟨25815030622570935361924823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17210020415047290241283215 25815030622570935361924823)
      ·
        refine ⟨38722545933856403042887235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25815030622570935361924823 38722545933856403042887235)
        ·
          refine ⟨58083818900784604564330853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38722545933856403042887235 58083818900784604564330853)
          ·
            refine ⟨10890716043897113355812035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58083818900784604564330853 10890716043897113355812035)
            ·
              refine ⟨16336074065845670033718053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10890716043897113355812035 16336074065845670033718053)
              ·
                refine ⟨3063013887346063131322135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16336074065845670033718053 3063013887346063131322135)
                ·
                  refine ⟨4594520831019094696983203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063013887346063131322135 4594520831019094696983203)
                  ·
                    refine ⟨6891781246528642045474805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4594520831019094696983203 6891781246528642045474805)
                    ·
                      refine ⟨646104491862060191763263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6891781246528642045474805 646104491862060191763263)
                      ·
                        rfl

theorem cell23_1258284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_1258284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258284 prefixEnd_1258284 := by exact prefixLift 1258284
  have htrace : WordTrace (prefixWord ++ tailWord_1258284) baseStart_1258284 baseEnd_1258284 := by
    simpa [prefixWord, tailWord_1258284, baseEnd_1258284] using wordTrace_append hprefix tailTrace_1258284
  have hstable : (prefixWord ++ tailWord_1258284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258284).length < 2 ^ (prefixWord ++ tailWord_1258284).sum := by decide
  have hdescent : baseEnd_1258284 < baseStart_1258284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258338 : List Nat := [3, 3, 2, 1, 3, 2, 1, 8]
def baseStart_1258338 : Nat := 118140960795 + 1258338 * 2 ^ 59
def prefixEnd_1258338 : Nat := 4983230072969 + 3 ^ 40 * 1258338 * 2
def baseEnd_1258338 : Nat := 23930822956200110388445

theorem tailTrace_1258338 : CollatzResearch.WordTrace tailWord_1258338 prefixEnd_1258338 23930822956200110388445 := by
  unfold tailWord_1258338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11473839328815951966471917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30596904876842538577258445 11473839328815951966471917)
  ·
    refine ⟨4302689748305981987426969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11473839328815951966471917 4302689748305981987426969)
    ·
      refine ⟨3227017311229486490570227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4302689748305981987426969 3227017311229486490570227)
      ·
        refine ⟨4840525966844229735855341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3227017311229486490570227 4840525966844229735855341)
        ·
          refine ⟨1815197237566586150945753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4840525966844229735855341 1815197237566586150945753)
          ·
            refine ⟨1361397928174939613209315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1815197237566586150945753 1361397928174939613209315)
            ·
              refine ⟨2042096892262409419813973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361397928174939613209315 2042096892262409419813973)
              ·
                refine ⟨23930822956200110388445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2042096892262409419813973 23930822956200110388445)
                ·
                  rfl

theorem cell23_1258338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 8].length) (baseStart_1258338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258338 prefixEnd_1258338 := by exact prefixLift 1258338
  have htrace : WordTrace (prefixWord ++ tailWord_1258338) baseStart_1258338 baseEnd_1258338 := by
    simpa [prefixWord, tailWord_1258338, baseEnd_1258338] using wordTrace_append hprefix tailTrace_1258338
  have hstable : (prefixWord ++ tailWord_1258338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258338).length < 2 ^ (prefixWord ++ tailWord_1258338).sum := by decide
  have hdescent : baseEnd_1258338 < baseStart_1258338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258348 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 3]
def baseStart_1258348 : Nat := 118140960795 + 1258348 * 2 ^ 59
def prefixEnd_1258348 : Nat := 4983230072969 + 3 ^ 40 * 1258348 * 2
def baseEnd_1258348 : Nat := 646137354623947941362969

theorem tailTrace_1258348 : CollatzResearch.WordTrace tailWord_1258348 prefixEnd_1258348 646137354623947941362969 := by
  unfold tailWord_1258348
  simp only [CollatzResearch.WordTrace]
  refine ⟨22947861022613789786875849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30597148030151719715834465 22947861022613789786875849)
  ·
    refine ⟨17210895766960342340156887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22947861022613789786875849 17210895766960342340156887)
    ·
      refine ⟨25816343650440513510235331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17210895766960342340156887 25816343650440513510235331)
      ·
        refine ⟨38724515475660770265352997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25816343650440513510235331 38724515475660770265352997)
        ·
          refine ⟨7260846651686394424753687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38724515475660770265352997 7260846651686394424753687)
          ·
            refine ⟨10891269977529591637130531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7260846651686394424753687 10891269977529591637130531)
            ·
              refine ⟨16336904966294387455695797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10891269977529591637130531 16336904966294387455695797)
              ·
                refine ⟨1531584840590098823971481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16336904966294387455695797 1531584840590098823971481)
                ·
                  refine ⟨1148688630442574117978611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1531584840590098823971481 1148688630442574117978611)
                  ·
                    refine ⟨1723032945663861176967917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1148688630442574117978611 1723032945663861176967917)
                    ·
                      refine ⟨646137354623947941362969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1723032945663861176967917 646137354623947941362969)
                      ·
                        rfl

theorem cell23_1258348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_1258348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258348 prefixEnd_1258348 := by exact prefixLift 1258348
  have htrace : WordTrace (prefixWord ++ tailWord_1258348) baseStart_1258348 baseEnd_1258348 := by
    simpa [prefixWord, tailWord_1258348, baseEnd_1258348] using wordTrace_append hprefix tailTrace_1258348
  have hstable : (prefixWord ++ tailWord_1258348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258348).length < 2 ^ (prefixWord ++ tailWord_1258348).sum := by decide
  have hdescent : baseEnd_1258348 < baseStart_1258348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258366 : List Nat := [4, 2, 3, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1258366 : Nat := 118140960795 + 1258366 * 2 ^ 59
def prefixEnd_1258366 : Nat := 4983230072969 + 3 ^ 40 * 1258366 * 2
def baseEnd_1258366 : Nat := 646146597275728870937887

theorem tailTrace_1258366 : CollatzResearch.WordTrace tailWord_1258366 prefixEnd_1258366 646146597275728870937887 := by
  unfold tailWord_1258366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5737047319895296080988369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30597585706108245765271301 5737047319895296080988369)
  ·
    refine ⟨4302785489921472060741277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5737047319895296080988369 4302785489921472060741277)
    ·
      refine ⟨1613544558720552022777979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4302785489921472060741277 1613544558720552022777979)
      ·
        refine ⟨2420316838080828034166969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613544558720552022777979 2420316838080828034166969)
        ·
          refine ⟨1815237628560621025625227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2420316838080828034166969 1815237628560621025625227)
          ·
            refine ⟨2722856442840931538437841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815237628560621025625227 2722856442840931538437841)
            ·
              refine ⟨2042142332130698653828381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722856442840931538437841 2042142332130698653828381)
              ·
                refine ⟨765803374549011995185643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2042142332130698653828381 765803374549011995185643)
                ·
                  refine ⟨1148705061823517992778465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765803374549011995185643 1148705061823517992778465)
                  ·
                    refine ⟨861528796367638494583849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1148705061823517992778465 861528796367638494583849)
                    ·
                      refine ⟨646146597275728870937887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861528796367638494583849 646146597275728870937887)
                      ·
                        rfl

theorem cell23_1258366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1258366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258366 prefixEnd_1258366 := by exact prefixLift 1258366
  have htrace : WordTrace (prefixWord ++ tailWord_1258366) baseStart_1258366 baseEnd_1258366 := by
    simpa [prefixWord, tailWord_1258366, baseEnd_1258366] using wordTrace_append hprefix tailTrace_1258366
  have hstable : (prefixWord ++ tailWord_1258366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258366).length < 2 ^ (prefixWord ++ tailWord_1258366).sum := by decide
  have hdescent : baseEnd_1258366 < baseStart_1258366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258375 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_1258375 : Nat := 118140960795 + 1258375 * 2 ^ 59
def prefixEnd_1258375 : Nat := 4983230072969 + 3 ^ 40 * 1258375 * 2
def baseEnd_1258375 : Nat := 646151218601619335725345

theorem tailTrace_1258375 : CollatzResearch.WordTrace tailWord_1258375 prefixEnd_1258375 646151218601619335725345 := by
  unfold tailWord_1258375
  simp only [CollatzResearch.WordTrace]
  refine ⟨45896706816129763184984579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30597804544086508789989719 45896706816129763184984579)
  ·
    refine ⟨68845060224194644777476869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45896706816129763184984579 68845060224194644777476869)
    ·
      refine ⟨12908448792036495895776913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68845060224194644777476869 12908448792036495895776913)
      ·
        refine ⟨9681336594027371921832685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12908448792036495895776913 9681336594027371921832685)
        ·
          refine ⟨3630501222760264470687257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9681336594027371921832685 3630501222760264470687257)
          ·
            refine ⟨2722875917070198353015443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3630501222760264470687257 2722875917070198353015443)
            ·
              refine ⟨4084313875605297529523165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2722875917070198353015443 4084313875605297529523165)
              ·
                refine ⟨1531617703351986573571187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4084313875605297529523165 1531617703351986573571187)
                ·
                  refine ⟨2297426555027979860356781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531617703351986573571187 2297426555027979860356781)
                  ·
                    refine ⟨861534958135492447633793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297426555027979860356781 861534958135492447633793)
                    ·
                      refine ⟨646151218601619335725345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861534958135492447633793 646151218601619335725345)
                      ·
                        rfl

theorem cell23_1258375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_1258375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258375 prefixEnd_1258375 := by exact prefixLift 1258375
  have htrace : WordTrace (prefixWord ++ tailWord_1258375) baseStart_1258375 baseEnd_1258375 := by
    simpa [prefixWord, tailWord_1258375, baseEnd_1258375] using wordTrace_append hprefix tailTrace_1258375
  have hstable : (prefixWord ++ tailWord_1258375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258375).length < 2 ^ (prefixWord ++ tailWord_1258375).sum := by decide
  have hdescent : baseEnd_1258375 < baseStart_1258375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258532 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1258532 : Nat := 118140960795 + 1258532 * 2 ^ 59
def prefixEnd_1258532 : Nat := 4983230072969 + 3 ^ 40 * 1258532 * 2
def baseEnd_1258532 : Nat := 646231835064375221462123

theorem tailTrace_1258532 : CollatzResearch.WordTrace tailWord_1258532 prefixEnd_1258532 646231835064375221462123 := by
  unfold tailWord_1258532
  simp only [CollatzResearch.WordTrace]
  refine ⟨22951216538280489499224925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30601622051040652665633233 22951216538280489499224925)
  ·
    refine ⟨8606706201855183562209347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22951216538280489499224925 8606706201855183562209347)
    ·
      refine ⟨12910059302782775343314021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8606706201855183562209347 12910059302782775343314021)
      ·
        refine ⟨2420636119271770376871379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12910059302782775343314021 2420636119271770376871379)
        ·
          refine ⟨3630954178907655565307069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420636119271770376871379 3630954178907655565307069)
          ·
            refine ⟨1361607817090370836990151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3630954178907655565307069 1361607817090370836990151)
            ·
              refine ⟨2042411725635556255485227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361607817090370836990151 2042411725635556255485227)
              ·
                refine ⟨3063617588453334383227841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042411725635556255485227 3063617588453334383227841)
                ·
                  refine ⟨2297713191340000787420881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3063617588453334383227841 2297713191340000787420881)
                  ·
                    refine ⟨1723284893505000590565661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2297713191340000787420881 1723284893505000590565661)
                    ·
                      refine ⟨646231835064375221462123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1723284893505000590565661 646231835064375221462123)
                      ·
                        rfl

theorem cell23_1258532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1258532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258532 prefixEnd_1258532 := by exact prefixLift 1258532
  have htrace : WordTrace (prefixWord ++ tailWord_1258532) baseStart_1258532 baseEnd_1258532 := by
    simpa [prefixWord, tailWord_1258532, baseEnd_1258532] using wordTrace_append hprefix tailTrace_1258532
  have hstable : (prefixWord ++ tailWord_1258532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258532).length < 2 ^ (prefixWord ++ tailWord_1258532).sum := by decide
  have hdescent : baseEnd_1258532 < baseStart_1258532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258585 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 5, 2, 2]
def baseStart_1258585 : Nat := 118140960795 + 1258585 * 2 ^ 59
def prefixEnd_1258585 : Nat := 4983230072969 + 3 ^ 40 * 1258585 * 2
def baseEnd_1258585 : Nat := 646259049539063514099379

theorem tailTrace_1258585 : CollatzResearch.WordTrace tailWord_1258585 prefixEnd_1258585 646259049539063514099379 := by
  unfold tailWord_1258585
  simp only [CollatzResearch.WordTrace]
  refine ⟨45904366145368969050129209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30602910763579312700086139 45904366145368969050129209)
  ·
    refine ⟨34428274609026726787596907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45904366145368969050129209 34428274609026726787596907)
    ·
      refine ⟨51642411913540090181395361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34428274609026726787596907 51642411913540090181395361)
      ·
        refine ⟨38731808935155067636046521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51642411913540090181395361 38731808935155067636046521)
        ·
          refine ⟨29048856701366300727034891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38731808935155067636046521 29048856701366300727034891)
          ·
            refine ⟨43573285052049451090552337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29048856701366300727034891 43573285052049451090552337)
            ·
              refine ⟨32679963789037088317914253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43573285052049451090552337 32679963789037088317914253)
              ·
                refine ⟨12254986420888908119217845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32679963789037088317914253 12254986420888908119217845)
                ·
                  refine ⟨1148904976958335136176673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12254986420888908119217845 1148904976958335136176673)
                  ·
                    refine ⟨861678732718751352132505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1148904976958335136176673 861678732718751352132505)
                    ·
                      refine ⟨646259049539063514099379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861678732718751352132505 646259049539063514099379)
                      ·
                        rfl

theorem cell23_1258585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_1258585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258585 prefixEnd_1258585 := by exact prefixLift 1258585
  have htrace : WordTrace (prefixWord ++ tailWord_1258585) baseStart_1258585 baseEnd_1258585 := by
    simpa [prefixWord, tailWord_1258585, baseEnd_1258585] using wordTrace_append hprefix tailTrace_1258585
  have hstable : (prefixWord ++ tailWord_1258585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258585).length < 2 ^ (prefixWord ++ tailWord_1258585).sum := by decide
  have hdescent : baseEnd_1258585 < baseStart_1258585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258588 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1258588 : Nat := 118140960795 + 1258588 * 2 ^ 59
def prefixEnd_1258588 : Nat := 4983230072969 + 3 ^ 40 * 1258588 * 2
def baseEnd_1258588 : Nat := 646260589981027002361865

theorem tailTrace_1258588 : CollatzResearch.WordTrace tailWord_1258588 prefixEnd_1258588 646260589981027002361865 := by
  unfold tailWord_1258588
  simp only [CollatzResearch.WordTrace]
  refine ⟨22952237782179050281244209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30602983709572067041658945 22952237782179050281244209)
  ·
    refine ⟨17214178336634287710933157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22952237782179050281244209 17214178336634287710933157)
    ·
      refine ⟨3227658438118928945799967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17214178336634287710933157 3227658438118928945799967)
      ·
        refine ⟨4841487657178393418699951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3227658438118928945799967 4841487657178393418699951)
        ·
          refine ⟨7262231485767590128049927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4841487657178393418699951 7262231485767590128049927)
          ·
            refine ⟨10893347228651385192074891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7262231485767590128049927 10893347228651385192074891)
            ·
              refine ⟨16340020842977077788112337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10893347228651385192074891 16340020842977077788112337)
              ·
                refine ⟨12255015632232808341084253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16340020842977077788112337 12255015632232808341084253)
                ·
                  refine ⟨4595630862087303127906595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12255015632232808341084253 4595630862087303127906595)
                  ·
                    refine ⟨6893446293130954691859893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4595630862087303127906595 6893446293130954691859893)
                    ·
                      refine ⟨646260589981027002361865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6893446293130954691859893 646260589981027002361865)
                      ·
                        rfl

theorem cell23_1258588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1258588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258588 prefixEnd_1258588 := by exact prefixLift 1258588
  have htrace : WordTrace (prefixWord ++ tailWord_1258588) baseStart_1258588 baseEnd_1258588 := by
    simpa [prefixWord, tailWord_1258588, baseEnd_1258588] using wordTrace_append hprefix tailTrace_1258588
  have hstable : (prefixWord ++ tailWord_1258588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258588).length < 2 ^ (prefixWord ++ tailWord_1258588).sum := by decide
  have hdescent : baseEnd_1258588 < baseStart_1258588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258591 : List Nat := [1, 1, 2, 3, 1, 1, 5, 9]
def baseStart_1258591 : Nat := 118140960795 + 1258591 * 2 ^ 59
def prefixEnd_1258591 : Nat := 4983230072969 + 3 ^ 40 * 1258591 * 2
def baseEnd_1258591 : Nat := 23935634460110758912013

theorem tailTrace_1258591 : CollatzResearch.WordTrace tailWord_1258591 prefixEnd_1258591 23935634460110758912013 := by
  unfold tailWord_1258591
  simp only [CollatzResearch.WordTrace]
  refine ⟨45904584983347232074847627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30603056655564821383231751 45904584983347232074847627)
  ·
    refine ⟨68856877475020848112271441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45904584983347232074847627 68856877475020848112271441)
    ·
      refine ⟨51642658106265636084203581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68856877475020848112271441 51642658106265636084203581)
      ·
        refine ⟨19365996789849613531576343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51642658106265636084203581 19365996789849613531576343)
        ·
          refine ⟨29048995184774420297364515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19365996789849613531576343 29048995184774420297364515)
          ·
            refine ⟨43573492777161630446046773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29048995184774420297364515 43573492777161630446046773)
            ·
              refine ⟨4085014947858902854316885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43573492777161630446046773 4085014947858902854316885)
              ·
                refine ⟨23935634460110758912013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4085014947858902854316885 23935634460110758912013)
                ·
                  rfl

theorem cell23_1258591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 9].length) (baseStart_1258591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258591 prefixEnd_1258591 := by exact prefixLift 1258591
  have htrace : WordTrace (prefixWord ++ tailWord_1258591) baseStart_1258591 baseEnd_1258591 := by
    simpa [prefixWord, tailWord_1258591, baseEnd_1258591] using wordTrace_append hprefix tailTrace_1258591
  have hstable : (prefixWord ++ tailWord_1258591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258591).length < 2 ^ (prefixWord ++ tailWord_1258591).sum := by decide
  have hdescent : baseEnd_1258591 < baseStart_1258591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258605 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1258605 : Nat := 118140960795 + 1258605 * 2 ^ 59
def prefixEnd_1258605 : Nat := 4983230072969 + 3 ^ 40 * 1258605 * 2
def baseEnd_1258605 : Nat := 646269319152153435849287

theorem tailTrace_1258605 : CollatzResearch.WordTrace tailWord_1258605 prefixEnd_1258605 646269319152153435849287 := by
  unfold tailWord_1258605
  simp only [CollatzResearch.WordTrace]
  refine ⟨45905095605296512465857269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30603397070197674977238179 45905095605296512465857269)
  ·
    refine ⟨4303602712996548043674119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45905095605296512465857269 4303602712996548043674119)
    ·
      refine ⟨6455404069494822065511179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4303602712996548043674119 6455404069494822065511179)
      ·
        refine ⟨9683106104242233098266769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6455404069494822065511179 9683106104242233098266769)
        ·
          refine ⟨7262329578181674823700077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9683106104242233098266769 7262329578181674823700077)
          ·
            refine ⟨2723373591818128058887529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7262329578181674823700077 2723373591818128058887529)
            ·
              refine ⟨2042530193863596044165647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2723373591818128058887529 2042530193863596044165647)
              ·
                refine ⟨3063795290795394066248471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042530193863596044165647 3063795290795394066248471)
                ·
                  refine ⟨4595692936193091099372707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063795290795394066248471 4595692936193091099372707)
                  ·
                    refine ⟨6893539404289636649059061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4595692936193091099372707 6893539404289636649059061)
                    ·
                      refine ⟨646269319152153435849287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6893539404289636649059061 646269319152153435849287)
                      ·
                        rfl

theorem cell23_1258605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1258605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258605 prefixEnd_1258605 := by exact prefixLift 1258605
  have htrace : WordTrace (prefixWord ++ tailWord_1258605) baseStart_1258605 baseEnd_1258605 := by
    simpa [prefixWord, tailWord_1258605, baseEnd_1258605] using wordTrace_append hprefix tailTrace_1258605
  have hstable : (prefixWord ++ tailWord_1258605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258605).length < 2 ^ (prefixWord ++ tailWord_1258605).sum := by decide
  have hdescent : baseEnd_1258605 < baseStart_1258605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258613 : List Nat := [1, 3, 4, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1258613 : Nat := 118140960795 + 1258613 * 2 ^ 59
def prefixEnd_1258613 : Nat := 4983230072969 + 3 ^ 40 * 1258613 * 2
def baseEnd_1258613 : Nat := 646273426997389404549251

theorem tailTrace_1258613 : CollatzResearch.WordTrace tailWord_1258613 prefixEnd_1258613 646273426997389404549251 := by
  unfold tailWord_1258613
  simp only [CollatzResearch.WordTrace]
  refine ⟨45905387389267529832148493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30603591592845019888098995 45905387389267529832148493)
  ·
    refine ⟨17214520270975323687055685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45905387389267529832148493 17214520270975323687055685)
    ·
      refine ⟨3227722550807873191322941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17214520270975323687055685 3227722550807873191322941)
      ·
        refine ⟨1210395956552952446746103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3227722550807873191322941 1210395956552952446746103)
        ·
          refine ⟨1815593934829428670119155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210395956552952446746103 1815593934829428670119155)
          ·
            refine ⟨2723390902244143005178733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815593934829428670119155 2723390902244143005178733)
            ·
              refine ⟨1021271588341553626942025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2723390902244143005178733 1021271588341553626942025)
              ·
                refine ⟨765953691256165220206519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021271588341553626942025 765953691256165220206519)
                ·
                  refine ⟨1148930536884247830309779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765953691256165220206519 1148930536884247830309779)
                  ·
                    refine ⟨1723395805326371745464669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1148930536884247830309779 1723395805326371745464669)
                    ·
                      refine ⟨646273426997389404549251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1723395805326371745464669 646273426997389404549251)
                      ·
                        rfl

theorem cell23_1258613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1258613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258613 prefixEnd_1258613 := by exact prefixLift 1258613
  have htrace : WordTrace (prefixWord ++ tailWord_1258613) baseStart_1258613 baseEnd_1258613 := by
    simpa [prefixWord, tailWord_1258613, baseEnd_1258613] using wordTrace_append hprefix tailTrace_1258613
  have hstable : (prefixWord ++ tailWord_1258613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258613).length < 2 ^ (prefixWord ++ tailWord_1258613).sum := by decide
  have hdescent : baseEnd_1258613 < baseStart_1258613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258629 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_1258629 : Nat := 118140960795 + 1258629 * 2 ^ 59
def prefixEnd_1258629 : Nat := 4983230072969 + 3 ^ 40 * 1258629 * 2
def baseEnd_1258629 : Nat := 215427214229287113983059

theorem tailTrace_1258629 : CollatzResearch.WordTrace tailWord_1258629 prefixEnd_1258629 215427214229287113983059 := by
  unfold tailWord_1258629
  simp only [CollatzResearch.WordTrace]
  refine ⟨45905970957209564564730941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30603980638139709709820627 45905970957209564564730941)
  ·
    refine ⟨17214739108953586711774103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45905970957209564564730941 17214739108953586711774103)
    ·
      refine ⟨25822108663430380067661155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17214739108953586711774103 25822108663430380067661155)
      ·
        refine ⟨38733162995145570101491733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25822108663430380067661155 38733162995145570101491733)
        ·
          refine ⟨1815617015397448598507425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38733162995145570101491733 1815617015397448598507425)
          ·
            refine ⟨1361712761548086448880569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1815617015397448598507425 1361712761548086448880569)
            ·
              refine ⟨1021284571161064836660427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361712761548086448880569 1021284571161064836660427)
              ·
                refine ⟨1531926856741597254990641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021284571161064836660427 1531926856741597254990641)
                ·
                  refine ⟨1148945142556197941242981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1531926856741597254990641 1148945142556197941242981)
                  ·
                    refine ⟨215427214229287113983059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1148945142556197941242981 215427214229287113983059)
                    ·
                      rfl

theorem cell23_1258629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_1258629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258629 prefixEnd_1258629 := by exact prefixLift 1258629
  have htrace : WordTrace (prefixWord ++ tailWord_1258629) baseStart_1258629 baseEnd_1258629 := by
    simpa [prefixWord, tailWord_1258629, baseEnd_1258629] using wordTrace_append hprefix tailTrace_1258629
  have hstable : (prefixWord ++ tailWord_1258629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258629).length < 2 ^ (prefixWord ++ tailWord_1258629).sum := by decide
  have hdescent : baseEnd_1258629 < baseStart_1258629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258698 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 9]
def baseStart_1258698 : Nat := 118140960795 + 1258698 * 2 ^ 59
def prefixEnd_1258698 : Nat := 4983230072969 + 3 ^ 40 * 1258698 * 2
def baseEnd_1258698 : Nat := 71813008094780174665151

theorem tailTrace_1258698 : CollatzResearch.WordTrace tailWord_1258698 prefixEnd_1258698 71813008094780174665151 := by
  unfold tailWord_1258698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11477121898489897337248187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30605658395973059565995165 11477121898489897337248187)
  ·
    refine ⟨17215682847734846005872281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11477121898489897337248187 17215682847734846005872281)
    ·
      refine ⟨12911762135801134504404211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17215682847734846005872281 12911762135801134504404211)
      ·
        refine ⟨19367643203701701756606317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12911762135801134504404211 19367643203701701756606317)
        ·
          refine ⟨7262866201388138158727369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19367643203701701756606317 7262866201388138158727369)
          ·
            refine ⟨5447149651041103619045527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7262866201388138158727369 5447149651041103619045527)
            ·
              refine ⟨8170724476561655428568291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5447149651041103619045527 8170724476561655428568291)
              ·
                refine ⟨12256086714842483142852437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8170724476561655428568291 12256086714842483142852437)
                ·
                  refine ⟨71813008094780174665151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12256086714842483142852437 71813008094780174665151)
                  ·
                    rfl

theorem cell23_1258698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_1258698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258698 prefixEnd_1258698 := by exact prefixLift 1258698
  have htrace : WordTrace (prefixWord ++ tailWord_1258698) baseStart_1258698 baseEnd_1258698 := by
    simpa [prefixWord, tailWord_1258698, baseEnd_1258698] using wordTrace_append hprefix tailTrace_1258698
  have hstable : (prefixWord ++ tailWord_1258698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258698).length < 2 ^ (prefixWord ++ tailWord_1258698).sum := by decide
  have hdescent : baseEnd_1258698 < baseStart_1258698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258865 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 1, 6]
def baseStart_1258865 : Nat := 118140960795 + 1258865 * 2 ^ 59
def prefixEnd_1258865 : Nat := 4983230072969 + 3 ^ 40 * 1258865 * 2
def baseEnd_1258865 : Nat := 215467608040774139532697

theorem tailTrace_1258865 : CollatzResearch.WordTrace tailWord_1258865 prefixEnd_1258865 215467608040774139532697 := by
  unfold tailWord_1258865
  simp only [CollatzResearch.WordTrace]
  refine ⟨45914578584354576870322049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30609719056236384580214699 45914578584354576870322049)
  ·
    refine ⟨34435933938265932652741537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45914578584354576870322049 34435933938265932652741537)
    ·
      refine ⟨25826950453699449489556153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34435933938265932652741537 25826950453699449489556153)
      ·
        refine ⟨19370212840274587117167115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25826950453699449489556153 19370212840274587117167115)
        ·
          refine ⟨29055319260411880675750673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19370212840274587117167115 29055319260411880675750673)
          ·
            refine ⟨21791489445308910506813005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29055319260411880675750673 21791489445308910506813005)
            ·
              refine ⟨8171808541990841440054877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21791489445308910506813005 8171808541990841440054877)
              ·
                refine ⟨3064428203246565540020579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8171808541990841440054877 3064428203246565540020579)
                ·
                  refine ⟨4596642304869848310030869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064428203246565540020579 4596642304869848310030869)
                  ·
                    refine ⟨215467608040774139532697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4596642304869848310030869 215467608040774139532697)
                    ·
                      rfl

theorem cell23_1258865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_1258865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258865 prefixEnd_1258865 := by exact prefixLift 1258865
  have htrace : WordTrace (prefixWord ++ tailWord_1258865) baseStart_1258865 baseEnd_1258865 := by
    simpa [prefixWord, tailWord_1258865, baseEnd_1258865] using wordTrace_append hprefix tailTrace_1258865
  have hstable : (prefixWord ++ tailWord_1258865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258865).length < 2 ^ (prefixWord ++ tailWord_1258865).sum := by decide
  have hdescent : baseEnd_1258865 < baseStart_1258865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258889 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 4]
def baseStart_1258889 : Nat := 118140960795 + 1258889 * 2 ^ 59
def prefixEnd_1258889 : Nat := 4983230072969 + 3 ^ 40 * 1258889 * 2
def baseEnd_1258889 : Nat := 646415147658030324697981

theorem tailTrace_1258889 : CollatzResearch.WordTrace tailWord_1258889 prefixEnd_1258889 646415147658030324697981 := by
  unfold tailWord_1258889
  simp only [CollatzResearch.WordTrace]
  refine ⟨45915453936267628969195721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30610302624178419312797147 45915453936267628969195721)
  ·
    refine ⟨34436590452200721726896791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45915453936267628969195721 34436590452200721726896791)
    ·
      refine ⟨51654885678301082590345187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34436590452200721726896791 51654885678301082590345187)
      ·
        refine ⟨77482328517451623885517781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51654885678301082590345187 77482328517451623885517781)
        ·
          refine ⟨1815992074627772434816823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 77482328517451623885517781 1815992074627772434816823)
          ·
            refine ⟨2723988111941658652225235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815992074627772434816823 2723988111941658652225235)
            ·
              refine ⟨4085982167912487978337853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723988111941658652225235 4085982167912487978337853)
              ·
                refine ⟨1532243312967182991876695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4085982167912487978337853 1532243312967182991876695)
                ·
                  refine ⟨2298364969450774487815043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532243312967182991876695 2298364969450774487815043)
                  ·
                    refine ⟨3447547454176161731722565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2298364969450774487815043 3447547454176161731722565)
                    ·
                      refine ⟨646415147658030324697981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3447547454176161731722565 646415147658030324697981)
                      ·
                        rfl

theorem cell23_1258889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 4].length) (baseStart_1258889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258889 prefixEnd_1258889 := by exact prefixLift 1258889
  have htrace : WordTrace (prefixWord ++ tailWord_1258889) baseStart_1258889 baseEnd_1258889 := by
    simpa [prefixWord, tailWord_1258889, baseEnd_1258889] using wordTrace_append hprefix tailTrace_1258889
  have hstable : (prefixWord ++ tailWord_1258889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258889).length < 2 ^ (prefixWord ++ tailWord_1258889).sum := by decide
  have hdescent : baseEnd_1258889 < baseStart_1258889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258906 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2]
def baseStart_1258906 : Nat := 118140960795 + 1258906 * 2 ^ 59
def prefixEnd_1258906 : Nat := 4983230072969 + 3 ^ 40 * 1258906 * 2
def baseEnd_1258906 : Nat := 646423876829156758185403

theorem tailTrace_1258906 : CollatzResearch.WordTrace tailWord_1258906 prefixEnd_1258906 646423876829156758185403 := by
  unfold tailWord_1258906
  simp only [CollatzResearch.WordTrace]
  refine ⟨11479018494301510218141143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30610715984804027248376381 11479018494301510218141143)
  ·
    refine ⟨17218527741452265327211715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11479018494301510218141143 17218527741452265327211715)
    ·
      refine ⟨25827791612178397990817573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17218527741452265327211715 25827791612178397990817573)
      ·
        refine ⟨4842710927283449623278295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25827791612178397990817573 4842710927283449623278295)
        ·
          refine ⟨7264066390925174434917443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4842710927283449623278295 7264066390925174434917443)
          ·
            refine ⟨10896099586387761652376165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7264066390925174434917443 10896099586387761652376165)
            ·
              refine ⟨2043018672447705309820531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10896099586387761652376165 2043018672447705309820531)
              ·
                refine ⟨3064528008671557964730797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043018672447705309820531 3064528008671557964730797)
                ·
                  refine ⟨1149198003251834236774049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3064528008671557964730797 1149198003251834236774049)
                  ·
                    refine ⟨861898502438875677580537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1149198003251834236774049 861898502438875677580537)
                    ·
                      refine ⟨646423876829156758185403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861898502438875677580537 646423876829156758185403)
                      ·
                        rfl

theorem cell23_1258906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_1258906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258906 prefixEnd_1258906 := by exact prefixLift 1258906
  have htrace : WordTrace (prefixWord ++ tailWord_1258906) baseStart_1258906 baseEnd_1258906 := by
    simpa [prefixWord, tailWord_1258906, baseEnd_1258906] using wordTrace_append hprefix tailTrace_1258906
  have hstable : (prefixWord ++ tailWord_1258906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258906).length < 2 ^ (prefixWord ++ tailWord_1258906).sum := by decide
  have hdescent : baseEnd_1258906 < baseStart_1258906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258935 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_1258935 : Nat := 118140960795 + 1258935 * 2 ^ 59
def prefixEnd_1258935 : Nat := 4983230072969 + 3 ^ 40 * 1258935 * 2
def baseEnd_1258935 : Nat := 646438767768137144722769

theorem tailTrace_1258935 : CollatzResearch.WordTrace tailWord_1258935 prefixEnd_1258935 646438767768137144722769 := by
  unfold tailWord_1258935
  simp only [CollatzResearch.WordTrace]
  refine ⟨45917131694100978825370259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30611421129400652550246839 45917131694100978825370259)
  ·
    refine ⟨68875697541151468238055389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45917131694100978825370259 68875697541151468238055389)
    ·
      refine ⟨25828386577931800589270771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68875697541151468238055389 25828386577931800589270771)
      ·
        refine ⟨38742579866897700883906157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25828386577931800589270771 38742579866897700883906157)
        ·
          refine ⟨14528467450086637831464809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38742579866897700883906157 14528467450086637831464809)
          ·
            refine ⟨10896350587564978373598607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14528467450086637831464809 10896350587564978373598607)
            ·
              refine ⟨16344525881347467560397911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10896350587564978373598607 16344525881347467560397911)
              ·
                refine ⟨24516788822021201340596867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16344525881347467560397911 24516788822021201340596867)
                ·
                  refine ⟨36775183233031802010895301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24516788822021201340596867 36775183233031802010895301)
                  ·
                    refine ⟨6895346856193462877042869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36775183233031802010895301 6895346856193462877042869)
                    ·
                      refine ⟨646438767768137144722769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6895346856193462877042869 646438767768137144722769)
                      ·
                        rfl

theorem cell23_1258935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_1258935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258935 prefixEnd_1258935 := by exact prefixLift 1258935
  have htrace : WordTrace (prefixWord ++ tailWord_1258935) baseStart_1258935 baseEnd_1258935 := by
    simpa [prefixWord, tailWord_1258935, baseEnd_1258935] using wordTrace_append hprefix tailTrace_1258935
  have hstable : (prefixWord ++ tailWord_1258935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258935).length < 2 ^ (prefixWord ++ tailWord_1258935).sum := by decide
  have hdescent : baseEnd_1258935 < baseStart_1258935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258955 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 4, 6]
def baseStart_1258955 : Nat := 118140960795 + 1258955 * 2 ^ 59
def prefixEnd_1258955 : Nat := 4983230072969 + 3 ^ 40 * 1258955 * 2
def baseEnd_1258955 : Nat := 215483012460409022157559

theorem tailTrace_1258955 : CollatzResearch.WordTrace tailWord_1258955 prefixEnd_1258955 215483012460409022157559 := by
  unfold tailWord_1258955
  simp only [CollatzResearch.WordTrace]
  refine ⟨45917861154028522241098319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30611907436019014827398879 45917861154028522241098319)
  ·
    refine ⟨68876791731042783361647479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45917861154028522241098319 68876791731042783361647479)
    ·
      refine ⟨103315187596564175042471219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68876791731042783361647479 103315187596564175042471219)
      ·
        refine ⟨154972781394846262563706829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103315187596564175042471219 154972781394846262563706829)
        ·
          refine ⟨58114793023067348461390061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154972781394846262563706829 58114793023067348461390061)
          ·
            refine ⟨21793047383650255673021273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58114793023067348461390061 21793047383650255673021273)
            ·
              refine ⟨16344785537737691754765955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21793047383650255673021273 16344785537737691754765955)
              ·
                refine ⟨24517178306606537632148933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16344785537737691754765955 24517178306606537632148933)
                ·
                  refine ⟨4596970932488725806027925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24517178306606537632148933 4596970932488725806027925)
                  ·
                    refine ⟨215483012460409022157559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4596970932488725806027925 215483012460409022157559)
                    ·
                      rfl

theorem cell23_1258955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 6].length) (baseStart_1258955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258955 prefixEnd_1258955 := by exact prefixLift 1258955
  have htrace : WordTrace (prefixWord ++ tailWord_1258955) baseStart_1258955 baseEnd_1258955 := by
    simpa [prefixWord, tailWord_1258955, baseEnd_1258955] using wordTrace_append hprefix tailTrace_1258955
  have hstable : (prefixWord ++ tailWord_1258955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258955).length < 2 ^ (prefixWord ++ tailWord_1258955).sum := by decide
  have hdescent : baseEnd_1258955 < baseStart_1258955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258973 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_1258973 : Nat := 118140960795 + 1258973 * 2 ^ 59
def prefixEnd_1258973 : Nat := 4983230072969 + 3 ^ 40 * 1258973 * 2
def baseEnd_1258973 : Nat := 646458280033007996047595

theorem tailTrace_1258973 : CollatzResearch.WordTrace tailWord_1258973 prefixEnd_1258973 646458280033007996047595 := by
  unfold tailWord_1258973
  simp only [CollatzResearch.WordTrace]
  refine ⟨45918517667963311315253573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30612345111975540876835715 45918517667963311315253573)
  ·
    refine ⟨8609722062743120871610045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45918517667963311315253573 8609722062743120871610045)
    ·
      refine ⟨3228645773528670326853767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8609722062743120871610045 3228645773528670326853767)
      ·
        refine ⟨4842968660293005490280651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3228645773528670326853767 4842968660293005490280651)
        ·
          refine ⟨7264452990439508235420977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4842968660293005490280651 7264452990439508235420977)
          ·
            refine ⟨5448339742829631176565733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7264452990439508235420977 5448339742829631176565733)
            ·
              refine ⟨1021563701780555845606075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5448339742829631176565733 1021563701780555845606075)
              ·
                refine ⟨1532345552670833768409113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021563701780555845606075 1532345552670833768409113)
                ·
                  refine ⟨1149259164503125326306835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1532345552670833768409113 1149259164503125326306835)
                  ·
                    refine ⟨1723888746754687989460253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1149259164503125326306835 1723888746754687989460253)
                    ·
                      refine ⟨646458280033007996047595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1723888746754687989460253 646458280033007996047595)
                      ·
                        rfl

theorem cell23_1258973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_1258973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258973 prefixEnd_1258973 := by exact prefixLift 1258973
  have htrace : WordTrace (prefixWord ++ tailWord_1258973) baseStart_1258973 baseEnd_1258973 := by
    simpa [prefixWord, tailWord_1258973, baseEnd_1258973] using wordTrace_append hprefix tailTrace_1258973
  have hstable : (prefixWord ++ tailWord_1258973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258973).length < 2 ^ (prefixWord ++ tailWord_1258973).sum := by decide
  have hdescent : baseEnd_1258973 < baseStart_1258973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258983 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_1258983 : Nat := 118140960795 + 1258983 * 2 ^ 59
def prefixEnd_1258983 : Nat := 4983230072969 + 3 ^ 40 * 1258983 * 2
def baseEnd_1258983 : Nat := 646463414839552956922549

theorem tailTrace_1258983 : CollatzResearch.WordTrace tailWord_1258983 prefixEnd_1258983 646463414839552956922549 := by
  unfold tailWord_1258983
  simp only [CollatzResearch.WordTrace]
  refine ⟨45918882397927083023117603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30612588265284722015411735 45918882397927083023117603)
  ·
    refine ⟨68878323596890624534676405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45918882397927083023117603 68878323596890624534676405)
    ·
      refine ⟨6457342837208496050125913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68878323596890624534676405 6457342837208496050125913)
      ·
        refine ⟨4843007127906372037594435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6457342837208496050125913 4843007127906372037594435)
        ·
          refine ⟨7264510691859558056391653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4843007127906372037594435 7264510691859558056391653)
          ·
            refine ⟨1362095754723667135573435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7264510691859558056391653 1362095754723667135573435)
            ·
              refine ⟨2043143632085500703360153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362095754723667135573435 2043143632085500703360153)
              ·
                refine ⟨1532357724064125527520115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043143632085500703360153 1532357724064125527520115)
                ·
                  refine ⟨2298536586096188291280173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532357724064125527520115 2298536586096188291280173)
                  ·
                    refine ⟨861951219786070609230065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2298536586096188291280173 861951219786070609230065)
                    ·
                      refine ⟨646463414839552956922549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 861951219786070609230065 646463414839552956922549)
                      ·
                        rfl

theorem cell23_1258983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_1258983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258983 prefixEnd_1258983 := by exact prefixLift 1258983
  have htrace : WordTrace (prefixWord ++ tailWord_1258983) baseStart_1258983 baseEnd_1258983 := by
    simpa [prefixWord, tailWord_1258983, baseEnd_1258983] using wordTrace_append hprefix tailTrace_1258983
  have hstable : (prefixWord ++ tailWord_1258983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258983).length < 2 ^ (prefixWord ++ tailWord_1258983).sum := by decide
  have hdescent : baseEnd_1258983 < baseStart_1258983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258995 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 7]
def baseStart_1258995 : Nat := 118140960795 + 1258995 * 2 ^ 59
def prefixEnd_1258995 : Nat := 4983230072969 + 3 ^ 40 * 1258995 * 2
def baseEnd_1258995 : Nat := 646469576607406909972493

theorem tailTrace_1258995 : CollatzResearch.WordTrace tailWord_1258995 prefixEnd_1258995 646469576607406909972493 := by
  unfold tailWord_1258995
  simp only [CollatzResearch.WordTrace]
  refine ⟨45919320073883609072554439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30612880049255739381702959 45919320073883609072554439)
  ·
    refine ⟨68878980110825413608831659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45919320073883609072554439 68878980110825413608831659)
    ·
      refine ⟨103318470166238120413247489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68878980110825413608831659 103318470166238120413247489)
      ·
        refine ⟨77488852624678590309935617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103318470166238120413247489 77488852624678590309935617)
        ·
          refine ⟨58116639468508942732451713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77488852624678590309935617 58116639468508942732451713)
          ·
            refine ⟨43587479601381707049338785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58116639468508942732451713 43587479601381707049338785)
            ·
              refine ⟨32690609701036280287004089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43587479601381707049338785 32690609701036280287004089)
              ·
                refine ⟨24517957275777210215253067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32690609701036280287004089 24517957275777210215253067)
                ·
                  refine ⟨36776935913665815322879601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24517957275777210215253067 36776935913665815322879601)
                  ·
                    refine ⟨27582701935249361492159701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36776935913665815322879601 27582701935249361492159701)
                    ·
                      refine ⟨646469576607406909972493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27582701935249361492159701 646469576607406909972493)
                      ·
                        rfl

theorem cell23_1258995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_1258995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1258995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1258995 prefixEnd_1258995 := by exact prefixLift 1258995
  have htrace : WordTrace (prefixWord ++ tailWord_1258995) baseStart_1258995 baseEnd_1258995 := by
    simpa [prefixWord, tailWord_1258995, baseEnd_1258995] using wordTrace_append hprefix tailTrace_1258995
  have hstable : (prefixWord ++ tailWord_1258995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258995).length < 2 ^ (prefixWord ++ tailWord_1258995).sum := by decide
  have hdescent : baseEnd_1258995 < baseStart_1258995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259029 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_1259029 : Nat := 118140960795 + 1259029 * 2 ^ 59
def prefixEnd_1259029 : Nat := 4983230072969 + 3 ^ 40 * 1259029 * 2
def baseEnd_1259029 : Nat := 646487034949659776947337

theorem tailTrace_1259029 : CollatzResearch.WordTrace tailWord_1259029 prefixEnd_1259029 646487034949659776947337 := by
  unfold tailWord_1259029
  simp only [CollatzResearch.WordTrace]
  refine ⟨45920560155760432879292141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30613706770506955252861427 45920560155760432879292141)
  ·
    refine ⟨17220210058410162329734553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45920560155760432879292141 17220210058410162329734553)
    ·
      refine ⟨12915157543807621747300915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17220210058410162329734553 12915157543807621747300915)
      ·
        refine ⟨19372736315711432620951373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12915157543807621747300915 19372736315711432620951373)
        ·
          refine ⟨7264776118391787232856765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19372736315711432620951373 7264776118391787232856765)
          ·
            refine ⟨2724291044396920212321287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7264776118391787232856765 2724291044396920212321287)
            ·
              refine ⟨4086436566595380318481931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724291044396920212321287 4086436566595380318481931)
              ·
                refine ⟨6129654849893070477722897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086436566595380318481931 6129654849893070477722897)
                ·
                  refine ⟨4597241137419802858292173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6129654849893070477722897 4597241137419802858292173)
                  ·
                    refine ⟨1723965426532426071859565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4597241137419802858292173 1723965426532426071859565)
                    ·
                      refine ⟨646487034949659776947337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1723965426532426071859565 646487034949659776947337)
                      ·
                        rfl

theorem cell23_1259029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_1259029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259029 prefixEnd_1259029 := by exact prefixLift 1259029
  have htrace : WordTrace (prefixWord ++ tailWord_1259029) baseStart_1259029 baseEnd_1259029 := by
    simpa [prefixWord, tailWord_1259029, baseEnd_1259029] using wordTrace_append hprefix tailTrace_1259029
  have hstable : (prefixWord ++ tailWord_1259029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259029).length < 2 ^ (prefixWord ++ tailWord_1259029).sum := by decide
  have hdescent : baseEnd_1259029 < baseStart_1259029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259042 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1259042 : Nat := 118140960795 + 1259042 * 2 ^ 59
def prefixEnd_1259042 : Nat := 4983230072969 + 3 ^ 40 * 1259042 * 2
def baseEnd_1259042 : Nat := 646493710198168226084777

theorem tailTrace_1259042 : CollatzResearch.WordTrace tailWord_1259042 prefixEnd_1259042 646493710198168226084777 := by
  unfold tailWord_1259042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11480258576178334024878845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30614022869808890733010253 11480258576178334024878845)
  ·
    refine ⟨4305096966066875259329567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11480258576178334024878845 4305096966066875259329567)
    ·
      refine ⟨6457645449100312888994351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4305096966066875259329567 6457645449100312888994351)
      ·
        refine ⟨9686468173650469333491527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6457645449100312888994351 9686468173650469333491527)
        ·
          refine ⟨14529702260475704000237291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9686468173650469333491527 14529702260475704000237291)
          ·
            refine ⟨21794553390713556000355937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14529702260475704000237291 21794553390713556000355937)
            ·
              refine ⟨16345915043035167000266953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21794553390713556000355937 16345915043035167000266953)
              ·
                refine ⟨12259436282276375250200215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16345915043035167000266953 12259436282276375250200215)
                ·
                  refine ⟨18389154423414562875300323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12259436282276375250200215 18389154423414562875300323)
                  ·
                    refine ⟨27583731635121844312950485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18389154423414562875300323 27583731635121844312950485)
                    ·
                      refine ⟨646493710198168226084777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27583731635121844312950485 646493710198168226084777)
                      ·
                        rfl

theorem cell23_1259042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1259042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259042 prefixEnd_1259042 := by exact prefixLift 1259042
  have htrace : WordTrace (prefixWord ++ tailWord_1259042) baseStart_1259042 baseEnd_1259042 := by
    simpa [prefixWord, tailWord_1259042, baseEnd_1259042] using wordTrace_append hprefix tailTrace_1259042
  have hstable : (prefixWord ++ tailWord_1259042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259042).length < 2 ^ (prefixWord ++ tailWord_1259042).sum := by decide
  have hdescent : baseEnd_1259042 < baseStart_1259042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259082 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1259082 : Nat := 118140960795 + 1259082 * 2 ^ 59
def prefixEnd_1259082 : Nat := 4983230072969 + 3 ^ 40 * 1259082 * 2
def baseEnd_1259082 : Nat := 646514249424348069584593

theorem tailTrace_1259082 : CollatzResearch.WordTrace tailWord_1259082 prefixEnd_1259082 646514249424348069584593 := by
  unfold tailWord_1259082
  simp only [CollatzResearch.WordTrace]
  refine ⟨11480623306142105732742875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30614995483045615287314333 11480623306142105732742875)
  ·
    refine ⟨17220934959213158599114313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11480623306142105732742875 17220934959213158599114313)
    ·
      refine ⟨12915701219409868949335735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17220934959213158599114313 12915701219409868949335735)
      ·
        refine ⟨19373551829114803424003603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12915701219409868949335735 19373551829114803424003603)
        ·
          refine ⟨29060327743672205136005405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19373551829114803424003603 29060327743672205136005405)
          ·
            refine ⟨10897622903877076926002027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29060327743672205136005405 10897622903877076926002027)
            ·
              refine ⟨16346434355815615389003041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10897622903877076926002027 16346434355815615389003041)
              ·
                refine ⟨12259825766861711541752281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16346434355815615389003041 12259825766861711541752281)
                ·
                  refine ⟨9194869325146283656314211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12259825766861711541752281 9194869325146283656314211)
                  ·
                    refine ⟨13792303987719425484471317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9194869325146283656314211 13792303987719425484471317)
                    ·
                      refine ⟨646514249424348069584593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13792303987719425484471317 646514249424348069584593)
                      ·
                        rfl

theorem cell23_1259082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1259082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259082 prefixEnd_1259082 := by exact prefixLift 1259082
  have htrace : WordTrace (prefixWord ++ tailWord_1259082) baseStart_1259082 baseEnd_1259082 := by
    simpa [prefixWord, tailWord_1259082, baseEnd_1259082] using wordTrace_append hprefix tailTrace_1259082
  have hstable : (prefixWord ++ tailWord_1259082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259082).length < 2 ^ (prefixWord ++ tailWord_1259082).sum := by decide
  have hdescent : baseEnd_1259082 < baseStart_1259082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259132 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1259132 : Nat := 118140960795 + 1259132 * 2 ^ 59
def prefixEnd_1259132 : Nat := 4983230072969 + 3 ^ 40 * 1259132 * 2
def baseEnd_1259132 : Nat := 646539923457072873959363

theorem tailTrace_1259132 : CollatzResearch.WordTrace tailWord_1259132 prefixEnd_1259132 646539923457072873959363 := by
  unfold tailWord_1259132
  simp only [CollatzResearch.WordTrace]
  refine ⟨22962158437193640735145825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30616211249591520980194433 22962158437193640735145825)
  ·
    refine ⟨17221618827895230551359369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22962158437193640735145825 17221618827895230551359369)
    ·
      refine ⟨12916214120921422913519527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17221618827895230551359369 12916214120921422913519527)
      ·
        refine ⟨19374321181382134370279291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12916214120921422913519527 19374321181382134370279291)
        ·
          refine ⟨29061481772073201555418937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19374321181382134370279291 29061481772073201555418937)
          ·
            refine ⟨21796111329054901166564203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29061481772073201555418937 21796111329054901166564203)
            ·
              refine ⟨32694166993582351749846305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21796111329054901166564203 32694166993582351749846305)
              ·
                refine ⟨24520625245186763812384729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32694166993582351749846305 24520625245186763812384729)
                ·
                  refine ⟨18390468933890072859288547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24520625245186763812384729 18390468933890072859288547)
                  ·
                    refine ⟨27585703400835109288932821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18390468933890072859288547 27585703400835109288932821)
                    ·
                      refine ⟨646539923457072873959363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27585703400835109288932821 646539923457072873959363)
                      ·
                        rfl

theorem cell23_1259132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1259132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259132 prefixEnd_1259132 := by exact prefixLift 1259132
  have htrace : WordTrace (prefixWord ++ tailWord_1259132) baseStart_1259132 baseEnd_1259132 := by
    simpa [prefixWord, tailWord_1259132, baseEnd_1259132] using wordTrace_append hprefix tailTrace_1259132
  have hstable : (prefixWord ++ tailWord_1259132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259132).length < 2 ^ (prefixWord ++ tailWord_1259132).sum := by decide
  have hdescent : baseEnd_1259132 < baseStart_1259132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259152 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 5, 6]
def baseStart_1259152 : Nat := 118140960795 + 1259152 * 2 ^ 59
def prefixEnd_1259152 : Nat := 4983230072969 + 3 ^ 40 * 1259152 * 2
def baseEnd_1259152 : Nat := 215516731023387598569757

theorem tailTrace_1259152 : CollatzResearch.WordTrace tailWord_1259152 prefixEnd_1259152 215516731023387598569757 := by
  unfold tailWord_1259152
  simp only [CollatzResearch.WordTrace]
  refine ⟨22962523167157412443009855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30616697556209883257346473 22962523167157412443009855)
  ·
    refine ⟨34443784750736118664514783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22962523167157412443009855 34443784750736118664514783)
    ·
      refine ⟨51665677126104177996772175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34443784750736118664514783 51665677126104177996772175)
      ·
        refine ⟨77498515689156266995158263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51665677126104177996772175 77498515689156266995158263)
        ·
          refine ⟨116247773533734400492737395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77498515689156266995158263 116247773533734400492737395)
          ·
            refine ⟨174371660300601600739106093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116247773533734400492737395 174371660300601600739106093)
            ·
              refine ⟨65389372612725600277164785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174371660300601600739106093 65389372612725600277164785)
              ·
                refine ⟨49042029459544200207873589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65389372612725600277164785 49042029459544200207873589)
                ·
                  refine ⟨4597690261832268769488149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49042029459544200207873589 4597690261832268769488149)
                  ·
                    refine ⟨215516731023387598569757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4597690261832268769488149 215516731023387598569757)
                    ·
                      rfl

theorem cell23_1259152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_1259152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259152 prefixEnd_1259152 := by exact prefixLift 1259152
  have htrace : WordTrace (prefixWord ++ tailWord_1259152) baseStart_1259152 baseEnd_1259152 := by
    simpa [prefixWord, tailWord_1259152, baseEnd_1259152] using wordTrace_append hprefix tailTrace_1259152
  have hstable : (prefixWord ++ tailWord_1259152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259152).length < 2 ^ (prefixWord ++ tailWord_1259152).sum := by decide
  have hdescent : baseEnd_1259152 < baseStart_1259152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259169 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 3, 6]
def baseStart_1259169 : Nat := 118140960795 + 1259169 * 2 ^ 59
def prefixEnd_1259169 : Nat := 4983230072969 + 3 ^ 40 * 1259169 * 2
def baseEnd_1259169 : Nat := 215519640747096409732231

theorem tailTrace_1259169 : CollatzResearch.WordTrace tailWord_1259169 prefixEnd_1259169 215519640747096409732231 := by
  unfold tailWord_1259169
  simp only [CollatzResearch.WordTrace]
  refine ⟨45925666375253236789388561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30617110916835491192925707 45925666375253236789388561)
  ·
    refine ⟨34444249781439927592041421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45925666375253236789388561 34444249781439927592041421)
    ·
      refine ⟨12916593668039972847015533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34444249781439927592041421 12916593668039972847015533)
      ·
        refine ⟨4843722625514989817630825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12916593668039972847015533 4843722625514989817630825)
        ·
          refine ⟨3632791969136242363223119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4843722625514989817630825 3632791969136242363223119)
          ·
            refine ⟨5449187953704363544834679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632791969136242363223119 5449187953704363544834679)
            ·
              refine ⟨8173781930556545317252019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449187953704363544834679 8173781930556545317252019)
              ·
                refine ⟨12260672895834817975878029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8173781930556545317252019 12260672895834817975878029)
                ·
                  refine ⟨4597752335938056740954261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12260672895834817975878029 4597752335938056740954261)
                  ·
                    refine ⟨215519640747096409732231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4597752335938056740954261 215519640747096409732231)
                    ·
                      rfl

theorem cell23_1259169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_1259169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259169 prefixEnd_1259169 := by exact prefixLift 1259169
  have htrace : WordTrace (prefixWord ++ tailWord_1259169) baseStart_1259169 baseEnd_1259169 := by
    simpa [prefixWord, tailWord_1259169, baseEnd_1259169] using wordTrace_append hprefix tailTrace_1259169
  have hstable : (prefixWord ++ tailWord_1259169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259169).length < 2 ^ (prefixWord ++ tailWord_1259169).sum := by decide
  have hdescent : baseEnd_1259169 < baseStart_1259169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259186 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_1259186 : Nat := 118140960795 + 1259186 * 2 ^ 59
def prefixEnd_1259186 : Nat := 4983230072969 + 3 ^ 40 * 1259186 * 2
def baseEnd_1259186 : Nat := 215522550470805220894705

theorem tailTrace_1259186 : CollatzResearch.WordTrace tailWord_1259186 prefixEnd_1259186 215522550470805220894705 := by
  unfold tailWord_1259186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11481571604047912173189353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30617524277461099128504941 11481571604047912173189353)
  ·
    refine ⟨8611178703035934129892015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11481571604047912173189353 8611178703035934129892015)
    ·
      refine ⟨12916768054553901194838023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8611178703035934129892015 12916768054553901194838023)
      ·
        refine ⟨19375152081830851792257035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12916768054553901194838023 19375152081830851792257035)
        ·
          refine ⟨29062728122746277688385553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19375152081830851792257035 29062728122746277688385553)
          ·
            refine ⟨21797046092059708266289165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29062728122746277688385553 21797046092059708266289165)
            ·
              refine ⟨8173892284522390599858437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21797046092059708266289165 8173892284522390599858437)
              ·
                refine ⟨1532604803347948237473457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8173892284522390599858437 1532604803347948237473457)
                ·
                  refine ⟨1149453602510961178105093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1532604803347948237473457 1149453602510961178105093)
                  ·
                    refine ⟨215522550470805220894705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1149453602510961178105093 215522550470805220894705)
                    ·
                      rfl

theorem cell23_1259186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_1259186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259186 prefixEnd_1259186 := by exact prefixLift 1259186
  have htrace : WordTrace (prefixWord ++ tailWord_1259186) baseStart_1259186 baseEnd_1259186 := by
    simpa [prefixWord, tailWord_1259186, baseEnd_1259186] using wordTrace_append hprefix tailTrace_1259186
  have hstable : (prefixWord ++ tailWord_1259186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259186).length < 2 ^ (prefixWord ++ tailWord_1259186).sum := by decide
  have hdescent : baseEnd_1259186 < baseStart_1259186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259196 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1259196 : Nat := 118140960795 + 1259196 * 2 ^ 59
def prefixEnd_1259196 : Nat := 4983230072969 + 3 ^ 40 * 1259196 * 2
def baseEnd_1259196 : Nat := 646572786218960623559069

theorem tailTrace_1259196 : CollatzResearch.WordTrace tailWord_1259196 prefixEnd_1259196 646572786218960623559069 := by
  unfold tailWord_1259196
  simp only [CollatzResearch.WordTrace]
  refine ⟨22963325573077710200310721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30617767430770280267080961 22963325573077710200310721)
  ·
    refine ⟨17222494179808282650233041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22963325573077710200310721 17222494179808282650233041)
    ·
      refine ⟨12916870634856211987674781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17222494179808282650233041 12916870634856211987674781)
      ·
        refine ⟨4843826488071079495378043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12916870634856211987674781 4843826488071079495378043)
        ·
          refine ⟨7265739732106619243067065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4843826488071079495378043 7265739732106619243067065)
          ·
            refine ⟨5449304799079964432300299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7265739732106619243067065 5449304799079964432300299)
            ·
              refine ⟨8173957198619946648450449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449304799079964432300299 8173957198619946648450449)
              ·
                refine ⟨6130467898964959986337837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8173957198619946648450449 6130467898964959986337837)
                ·
                  refine ⟨2298925462111859994876689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6130467898964959986337837 2298925462111859994876689)
                  ·
                    refine ⟨1724194096583894996157517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2298925462111859994876689 1724194096583894996157517)
                    ·
                      refine ⟨646572786218960623559069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1724194096583894996157517 646572786218960623559069)
                      ·
                        rfl

theorem cell23_1259196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1259196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259196 prefixEnd_1259196 := by exact prefixLift 1259196
  have htrace : WordTrace (prefixWord ++ tailWord_1259196) baseStart_1259196 baseEnd_1259196 := by
    simpa [prefixWord, tailWord_1259196, baseEnd_1259196] using wordTrace_append hprefix tailTrace_1259196
  have hstable : (prefixWord ++ tailWord_1259196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259196).length < 2 ^ (prefixWord ++ tailWord_1259196).sum := by decide
  have hdescent : baseEnd_1259196 < baseStart_1259196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259210 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_1259210 : Nat := 118140960795 + 1259210 * 2 ^ 59
def prefixEnd_1259210 : Nat := 4983230072969 + 3 ^ 40 * 1259210 * 2
def baseEnd_1259210 : Nat := 646579974948123568784005

theorem tailTrace_1259210 : CollatzResearch.WordTrace tailWord_1259210 prefixEnd_1259210 646579974948123568784005 := by
  unfold tailWord_1259210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11481790442026175197907771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30618107845403133861087389 11481790442026175197907771)
  ·
    refine ⟨17222685663039262796861657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11481790442026175197907771 17222685663039262796861657)
    ·
      refine ⟨12917014247279447097646243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17222685663039262796861657 12917014247279447097646243)
      ·
        refine ⟨19375521370919170646469365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12917014247279447097646243 19375521370919170646469365)
        ·
          refine ⟨1816455128523672248106503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19375521370919170646469365 1816455128523672248106503)
          ·
            refine ⟨2724682692785508372159755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816455128523672248106503 2724682692785508372159755)
            ·
              refine ⟨4087024039178262558239633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724682692785508372159755 4087024039178262558239633)
              ·
                refine ⟨3065268029383696918679725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4087024039178262558239633 3065268029383696918679725)
                ·
                  refine ⟨1149475511018886344504897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3065268029383696918679725 1149475511018886344504897)
                  ·
                    refine ⟨862106633264164758378673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1149475511018886344504897 862106633264164758378673)
                    ·
                      refine ⟨646579974948123568784005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 862106633264164758378673 646579974948123568784005)
                      ·
                        rfl

theorem cell23_1259210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_1259210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259210 prefixEnd_1259210 := by exact prefixLift 1259210
  have htrace : WordTrace (prefixWord ++ tailWord_1259210) baseStart_1259210 baseEnd_1259210 := by
    simpa [prefixWord, tailWord_1259210, baseEnd_1259210] using wordTrace_append hprefix tailTrace_1259210
  have hstable : (prefixWord ++ tailWord_1259210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259210).length < 2 ^ (prefixWord ++ tailWord_1259210).sum := by decide
  have hdescent : baseEnd_1259210 < baseStart_1259210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259226 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_1259226 : Nat := 118140960795 + 1259226 * 2 ^ 59
def prefixEnd_1259226 : Nat := 4983230072969 + 3 ^ 40 * 1259226 * 2
def baseEnd_1259226 : Nat := 646588190638595506183931

theorem tailTrace_1259226 : CollatzResearch.WordTrace tailWord_1259226 prefixEnd_1259226 646588190638595506183931 := by
  unfold tailWord_1259226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11481936334011683881053383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30618496890697823682809021 11481936334011683881053383)
  ·
    refine ⟨17222904501017525821580075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11481936334011683881053383 17222904501017525821580075)
    ·
      refine ⟨25834356751526288732370113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17222904501017525821580075 25834356751526288732370113)
      ·
        refine ⟨19375767563644716549277585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25834356751526288732370113 19375767563644716549277585)
        ·
          refine ⟨14531825672733537411958189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19375767563644716549277585 14531825672733537411958189)
          ·
            refine ⟨5449434627275076529484321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14531825672733537411958189 5449434627275076529484321)
            ·
              refine ⟨4087075970456307397113241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449434627275076529484321 4087075970456307397113241)
              ·
                refine ⟨3065306977842230547834931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4087075970456307397113241 3065306977842230547834931)
                ·
                  refine ⟨4597960466763345821752397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065306977842230547834931 4597960466763345821752397)
                  ·
                    refine ⟨1724235175036254683157149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4597960466763345821752397 1724235175036254683157149)
                    ·
                      refine ⟨646588190638595506183931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1724235175036254683157149 646588190638595506183931)
                      ·
                        rfl

theorem cell23_1259226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_1259226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259226 prefixEnd_1259226 := by exact prefixLift 1259226
  have htrace : WordTrace (prefixWord ++ tailWord_1259226) baseStart_1259226 baseEnd_1259226 := by
    simpa [prefixWord, tailWord_1259226, baseEnd_1259226] using wordTrace_append hprefix tailTrace_1259226
  have hstable : (prefixWord ++ tailWord_1259226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259226).length < 2 ^ (prefixWord ++ tailWord_1259226).sum := by decide
  have hdescent : baseEnd_1259226 < baseStart_1259226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259243 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 3]
def baseStart_1259243 : Nat := 118140960795 + 1259243 * 2 ^ 59
def prefixEnd_1259243 : Nat := 4983230072969 + 3 ^ 40 * 1259243 * 2
def baseEnd_1259243 : Nat := 646596919809721939671353

theorem tailTrace_1259243 : CollatzResearch.WordTrace tailWord_1259243 prefixEnd_1259243 646596919809721939671353 := by
  unfold tailWord_1259243
  simp only [CollatzResearch.WordTrace]
  refine ⟨45928365376985147427582383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30618910251323431618388255 45928365376985147427582383)
  ·
    refine ⟨68892548065477721141373575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45928365376985147427582383 68892548065477721141373575)
    ·
      refine ⟨103338822098216581712060363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68892548065477721141373575 103338822098216581712060363)
      ·
        refine ⟨155008233147324872568090545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103338822098216581712060363 155008233147324872568090545)
        ·
          refine ⟨116256174860493654426067909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155008233147324872568090545 116256174860493654426067909)
          ·
            refine ⟨21798032786342560204887733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116256174860493654426067909 21798032786342560204887733)
            ·
              refine ⟨2043565573719615019208225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21798032786342560204887733 2043565573719615019208225)
              ·
                refine ⟨1532674180289711264406169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043565573719615019208225 1532674180289711264406169)
                ·
                  refine ⟨1149505635217283448304627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1532674180289711264406169 1149505635217283448304627)
                  ·
                    refine ⟨1724258452825925172456941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1149505635217283448304627 1724258452825925172456941)
                    ·
                      refine ⟨646596919809721939671353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1724258452825925172456941 646596919809721939671353)
                      ·
                        rfl

theorem cell23_1259243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 3].length) (baseStart_1259243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259243 prefixEnd_1259243 := by exact prefixLift 1259243
  have htrace : WordTrace (prefixWord ++ tailWord_1259243) baseStart_1259243 baseEnd_1259243 := by
    simpa [prefixWord, tailWord_1259243, baseEnd_1259243] using wordTrace_append hprefix tailTrace_1259243
  have hstable : (prefixWord ++ tailWord_1259243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259243).length < 2 ^ (prefixWord ++ tailWord_1259243).sum := by decide
  have hdescent : baseEnd_1259243 < baseStart_1259243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259260 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_1259260 : Nat := 118140960795 + 1259260 * 2 ^ 59
def prefixEnd_1259260 : Nat := 4983230072969 + 3 ^ 40 * 1259260 * 2
def baseEnd_1259260 : Nat := 646605648980848373158775

theorem tailTrace_1259260 : CollatzResearch.WordTrace tailWord_1259260 prefixEnd_1259260 646605648980848373158775 := by
  unfold tailWord_1259260
  simp only [CollatzResearch.WordTrace]
  refine ⟨22964492708961779665475617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30619323611949039553967489 22964492708961779665475617)
  ·
    refine ⟨17223369531721334749106713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22964492708961779665475617 17223369531721334749106713)
    ·
      refine ⟨12917527148791001061830035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17223369531721334749106713 12917527148791001061830035)
      ·
        refine ⟨19376290723186501592745053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12917527148791001061830035 19376290723186501592745053)
        ·
          refine ⟨7266109021194938097279395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19376290723186501592745053 7266109021194938097279395)
          ·
            refine ⟨10899163531792407145919093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7266109021194938097279395 10899163531792407145919093)
            ·
              refine ⟨1021796581105538169929915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10899163531792407145919093 1021796581105538169929915)
              ·
                refine ⟨1532694871658307254894873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021796581105538169929915 1532694871658307254894873)
                ·
                  refine ⟨1149521153743730441171155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1532694871658307254894873 1149521153743730441171155)
                  ·
                    refine ⟨1724281730615595661756733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1149521153743730441171155 1724281730615595661756733)
                    ·
                      refine ⟨646605648980848373158775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1724281730615595661756733 646605648980848373158775)
                      ·
                        rfl

theorem cell23_1259260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_1259260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259260 prefixEnd_1259260 := by exact prefixLift 1259260
  have htrace : WordTrace (prefixWord ++ tailWord_1259260) baseStart_1259260 baseEnd_1259260 := by
    simpa [prefixWord, tailWord_1259260, baseEnd_1259260] using wordTrace_append hprefix tailTrace_1259260
  have hstable : (prefixWord ++ tailWord_1259260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259260).length < 2 ^ (prefixWord ++ tailWord_1259260).sum := by decide
  have hdescent : baseEnd_1259260 < baseStart_1259260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259279 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_1259279 : Nat := 118140960795 + 1259279 * 2 ^ 59
def prefixEnd_1259279 : Nat := 4983230072969 + 3 ^ 40 * 1259279 * 2
def baseEnd_1259279 : Nat := 646615405113283798821187

theorem tailTrace_1259279 : CollatzResearch.WordTrace tailWord_1259279 prefixEnd_1259279 646615405113283798821187 := by
  unfold tailWord_1259279
  simp only [CollatzResearch.WordTrace]
  refine ⟨45929678404854725575892891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30619785603236483717261927 45929678404854725575892891)
  ·
    refine ⟨68894517607282088363839337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45929678404854725575892891 68894517607282088363839337)
    ·
      refine ⟨51670888205461566272879503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68894517607282088363839337 51670888205461566272879503)
      ·
        refine ⟨77506332308192349409319255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51670888205461566272879503 77506332308192349409319255)
        ·
          refine ⟨116259498462288524113978883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77506332308192349409319255 116259498462288524113978883)
          ·
            refine ⟨174389247693432786170968325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116259498462288524113978883 174389247693432786170968325)
            ·
              refine ⟨32697983942518647407056561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174389247693432786170968325 32697983942518647407056561)
              ·
                refine ⟨24523487956888985555292421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32697983942518647407056561 24523487956888985555292421)
                ·
                  refine ⟨4598153991916684791617329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24523487956888985555292421 4598153991916684791617329)
                  ·
                    refine ⟨3448615493937513593712997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4598153991916684791617329 3448615493937513593712997)
                    ·
                      refine ⟨646615405113283798821187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3448615493937513593712997 646615405113283798821187)
                      ·
                        rfl

theorem cell23_1259279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_1259279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259279 prefixEnd_1259279 := by exact prefixLift 1259279
  have htrace : WordTrace (prefixWord ++ tailWord_1259279) baseStart_1259279 baseEnd_1259279 := by
    simpa [prefixWord, tailWord_1259279, baseEnd_1259279] using wordTrace_append hprefix tailTrace_1259279
  have hstable : (prefixWord ++ tailWord_1259279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259279).length < 2 ^ (prefixWord ++ tailWord_1259279).sum := by decide
  have hdescent : baseEnd_1259279 < baseStart_1259279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259300 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_1259300 : Nat := 118140960795 + 1259300 * 2 ^ 59
def prefixEnd_1259300 : Nat := 4983230072969 + 3 ^ 40 * 1259300 * 2
def baseEnd_1259300 : Nat := 646626188207028216658591

theorem tailTrace_1259300 : CollatzResearch.WordTrace tailWord_1259300 prefixEnd_1259300 646626188207028216658591 := by
  unfold tailWord_1259300
  simp only [CollatzResearch.WordTrace]
  refine ⟨22965222168889323081203677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30620296225185764108271569 22965222168889323081203677)
  ·
    refine ⟨8611958313333496155451379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22965222168889323081203677 8611958313333496155451379)
    ·
      refine ⟨12917937470000244233177069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8611958313333496155451379 12917937470000244233177069)
      ·
        refine ⟨4844226551250091587441401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12917937470000244233177069 4844226551250091587441401)
        ·
          refine ⟨3633169913437568690581051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4844226551250091587441401 3633169913437568690581051)
          ·
            refine ⟨5449754870156353035871577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633169913437568690581051 5449754870156353035871577)
            ·
              refine ⟨4087316152617264776903683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449754870156353035871577 4087316152617264776903683)
              ·
                refine ⟨6130974228925897165355525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087316152617264776903683 6130974228925897165355525)
                ·
                  refine ⟨1149557667923605718504161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6130974228925897165355525 1149557667923605718504161)
                  ·
                    refine ⟨862168250942704288878121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1149557667923605718504161 862168250942704288878121)
                    ·
                      refine ⟨646626188207028216658591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 862168250942704288878121 646626188207028216658591)
                      ·
                        rfl

theorem cell23_1259300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_1259300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259300 prefixEnd_1259300 := by exact prefixLift 1259300
  have htrace : WordTrace (prefixWord ++ tailWord_1259300) baseStart_1259300 baseEnd_1259300 := by
    simpa [prefixWord, tailWord_1259300, baseEnd_1259300] using wordTrace_append hprefix tailTrace_1259300
  have hstable : (prefixWord ++ tailWord_1259300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259300).length < 2 ^ (prefixWord ++ tailWord_1259300).sum := by decide
  have hdescent : baseEnd_1259300 < baseStart_1259300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259317 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_1259317 : Nat := 118140960795 + 1259317 * 2 ^ 59
def prefixEnd_1259317 : Nat := 4983230072969 + 3 ^ 40 * 1259317 * 2
def baseEnd_1259317 : Nat := 646634917378154650146013

theorem tailTrace_1259317 : CollatzResearch.WordTrace tailWord_1259317 prefixEnd_1259317 646634917378154650146013 := by
  unfold tailWord_1259317
  simp only [CollatzResearch.WordTrace]
  refine ⟨45931064378717058065776205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30620709585811372043850803 45931064378717058065776205)
  ·
    refine ⟨17224149142018896774666077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45931064378717058065776205 17224149142018896774666077)
    ·
      refine ⟨6459055928257086290499779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17224149142018896774666077 6459055928257086290499779)
      ·
        refine ⟨9688583892385629435749669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6459055928257086290499779 9688583892385629435749669)
        ·
          refine ⟨1816609479822305519203063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9688583892385629435749669 1816609479822305519203063)
          ·
            refine ⟨2724914219733458278804595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816609479822305519203063 2724914219733458278804595)
            ·
              refine ⟨4087371329600187418206893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724914219733458278804595 4087371329600187418206893)
              ·
                refine ⟨1532764248600070281827585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4087371329600187418206893 1532764248600070281827585)
                ·
                  refine ⟨1149573186450052711370689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1532764248600070281827585 1149573186450052711370689)
                  ·
                    refine ⟨862179889837539533528017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1149573186450052711370689 862179889837539533528017)
                    ·
                      refine ⟨646634917378154650146013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 862179889837539533528017 646634917378154650146013)
                      ·
                        rfl

theorem cell23_1259317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_1259317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259317 prefixEnd_1259317 := by exact prefixLift 1259317
  have htrace : WordTrace (prefixWord ++ tailWord_1259317) baseStart_1259317 baseEnd_1259317 := by
    simpa [prefixWord, tailWord_1259317, baseEnd_1259317] using wordTrace_append hprefix tailTrace_1259317
  have hstable : (prefixWord ++ tailWord_1259317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259317).length < 2 ^ (prefixWord ++ tailWord_1259317).sum := by decide
  have hdescent : baseEnd_1259317 < baseStart_1259317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259319 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 1, 7]
def baseStart_1259319 : Nat := 118140960795 + 1259319 * 2 ^ 59
def prefixEnd_1259319 : Nat := 4983230072969 + 3 ^ 40 * 1259319 * 2
def baseEnd_1259319 : Nat := 215545314779821214107001

theorem tailTrace_1259319 : CollatzResearch.WordTrace tailWord_1259319 prefixEnd_1259319 215545314779821214107001 := by
  unfold tailWord_1259319
  simp only [CollatzResearch.WordTrace]
  refine ⟨45931137324709812407349011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30620758216473208271566007 45931137324709812407349011)
  ·
    refine ⟨68896705987064718611023517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45931137324709812407349011 68896705987064718611023517)
    ·
      refine ⟨25836264745149269479133819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68896705987064718611023517 25836264745149269479133819)
      ·
        refine ⟨38754397117723904218700729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25836264745149269479133819 38754397117723904218700729)
        ·
          refine ⟨29065797838292928164025547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38754397117723904218700729 29065797838292928164025547)
          ·
            refine ⟨43598696757439392246038321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29065797838292928164025547 43598696757439392246038321)
            ·
              refine ⟨32699022568079544184528741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43598696757439392246038321 32699022568079544184528741)
              ·
                refine ⟨6131066731514914534599139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32699022568079544184528741 6131066731514914534599139)
                ·
                  refine ⟨9196600097272371801898709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6131066731514914534599139 9196600097272371801898709)
                  ·
                    refine ⟨215545314779821214107001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9196600097272371801898709 215545314779821214107001)
                    ·
                      rfl

theorem cell23_1259319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_1259319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259319 prefixEnd_1259319 := by exact prefixLift 1259319
  have htrace : WordTrace (prefixWord ++ tailWord_1259319) baseStart_1259319 baseEnd_1259319 := by
    simpa [prefixWord, tailWord_1259319, baseEnd_1259319] using wordTrace_append hprefix tailTrace_1259319
  have hstable : (prefixWord ++ tailWord_1259319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259319).length < 2 ^ (prefixWord ++ tailWord_1259319).sum := by decide
  have hdescent : baseEnd_1259319 < baseStart_1259319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259336 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 2, 5]
def baseStart_1259336 : Nat := 118140960795 + 1259336 * 2 ^ 59
def prefixEnd_1259336 : Nat := 4983230072969 + 3 ^ 40 * 1259336 * 2
def baseEnd_1259336 : Nat := 215548224503530025269475

theorem tailTrace_1259336 : CollatzResearch.WordTrace tailWord_1259336 prefixEnd_1259336 215548224503530025269475 := by
  unfold tailWord_1259336
  simp only [CollatzResearch.WordTrace]
  refine ⟨22965878682824112155358931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30621171577098816207145241 22965878682824112155358931)
  ·
    refine ⟨34448818024236168233038397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22965878682824112155358931 34448818024236168233038397)
    ·
      refine ⟨12918306759088563087389399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34448818024236168233038397 12918306759088563087389399)
      ·
        refine ⟨19377460138632844631084099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12918306759088563087389399 19377460138632844631084099)
        ·
          refine ⟨29066190207949266946626149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19377460138632844631084099 29066190207949266946626149)
          ·
            refine ⟨5449910663990487552492403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29066190207949266946626149 5449910663990487552492403)
            ·
              refine ⟨8174865995985731328738605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449910663990487552492403 8174865995985731328738605)
              ·
                refine ⟨3065574748494649248276977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8174865995985731328738605 3065574748494649248276977)
                ·
                  refine ⟨2299181061370986936207733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3065574748494649248276977 2299181061370986936207733)
                  ·
                    refine ⟨215548224503530025269475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2299181061370986936207733 215548224503530025269475)
                    ·
                      rfl

theorem cell23_1259336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_1259336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259336 prefixEnd_1259336 := by exact prefixLift 1259336
  have htrace : WordTrace (prefixWord ++ tailWord_1259336) baseStart_1259336 baseEnd_1259336 := by
    simpa [prefixWord, tailWord_1259336, baseEnd_1259336] using wordTrace_append hprefix tailTrace_1259336
  have hstable : (prefixWord ++ tailWord_1259336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259336).length < 2 ^ (prefixWord ++ tailWord_1259336).sum := by decide
  have hdescent : baseEnd_1259336 < baseStart_1259336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259346 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1259346 : Nat := 118140960795 + 1259346 * 2 ^ 59
def prefixEnd_1259346 : Nat := 4983230072969 + 3 ^ 40 * 1259346 * 2
def baseEnd_1259346 : Nat := 646649808317135036683379

theorem tailTrace_1259346 : CollatzResearch.WordTrace tailWord_1259346 prefixEnd_1259346 646649808317135036683379 := by
  unfold tailWord_1259346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11483030523902999004645473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30621414730407997345721261 11483030523902999004645473)
  ·
    refine ⟨8612272892927249253484105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11483030523902999004645473 8612272892927249253484105)
    ·
      refine ⟨6459204669695436940113079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8612272892927249253484105 6459204669695436940113079)
      ·
        refine ⟨9688807004543155410169619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6459204669695436940113079 9688807004543155410169619)
        ·
          refine ⟨14533210506814733115254429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9688807004543155410169619 14533210506814733115254429)
          ·
            refine ⟨5449953940055524918220411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14533210506814733115254429 5449953940055524918220411)
            ·
              refine ⟨8174930910083287377330617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449953940055524918220411 8174930910083287377330617)
              ·
                refine ⟨6131198182562465532997963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8174930910083287377330617 6131198182562465532997963)
                ·
                  refine ⟨9196797273843698299496945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6131198182562465532997963 9196797273843698299496945)
                  ·
                    refine ⟨6897597955382773724622709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9196797273843698299496945 6897597955382773724622709)
                    ·
                      refine ⟨646649808317135036683379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6897597955382773724622709 646649808317135036683379)
                      ·
                        rfl

theorem cell23_1259346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1259346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259346 prefixEnd_1259346 := by exact prefixLift 1259346
  have htrace : WordTrace (prefixWord ++ tailWord_1259346) baseStart_1259346 baseEnd_1259346 := by
    simpa [prefixWord, tailWord_1259346, baseEnd_1259346] using wordTrace_append hprefix tailTrace_1259346
  have hstable : (prefixWord ++ tailWord_1259346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259346).length < 2 ^ (prefixWord ++ tailWord_1259346).sum := by decide
  have hdescent : baseEnd_1259346 < baseStart_1259346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259373 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_1259373 : Nat := 118140960795 + 1259373 * 2 ^ 59
def prefixEnd_1259373 : Nat := 4983230072969 + 3 ^ 40 * 1259373 * 2
def baseEnd_1259373 : Nat := 646663672294806431045755

theorem tailTrace_1259373 : CollatzResearch.WordTrace tailWord_1259373 prefixEnd_1259373 646663672294806431045755 := by
  unfold tailWord_1259373
  simp only [CollatzResearch.WordTrace]
  refine ⟨45933106866514179629814773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30622071244342786419876515 45933106866514179629814773)
  ·
    refine ⟨4306228768735704340295135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45933106866514179629814773 4306228768735704340295135)
    ·
      refine ⟨6459343153103556510442703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4306228768735704340295135 6459343153103556510442703)
      ·
        refine ⟨9689014729655334765664055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6459343153103556510442703 9689014729655334765664055)
        ·
          refine ⟨14533522094483002148496083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9689014729655334765664055 14533522094483002148496083)
          ·
            refine ⟨21800283141724503222744125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14533522094483002148496083 21800283141724503222744125)
            ·
              refine ⟨8175106178146688708529047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21800283141724503222744125 8175106178146688708529047)
              ·
                refine ⟨12262659267220033062793571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8175106178146688708529047 12262659267220033062793571)
                ·
                  refine ⟨18393988900830049594190357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12262659267220033062793571 18393988900830049594190357)
                  ·
                    refine ⟨862218229726408574727673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18393988900830049594190357 862218229726408574727673)
                    ·
                      refine ⟨646663672294806431045755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 862218229726408574727673 646663672294806431045755)
                      ·
                        rfl

theorem cell23_1259373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_1259373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259373 prefixEnd_1259373 := by exact prefixLift 1259373
  have htrace : WordTrace (prefixWord ++ tailWord_1259373) baseStart_1259373 baseEnd_1259373 := by
    simpa [prefixWord, tailWord_1259373, baseEnd_1259373] using wordTrace_append hprefix tailTrace_1259373
  have hstable : (prefixWord ++ tailWord_1259373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259373).length < 2 ^ (prefixWord ++ tailWord_1259373).sum := by decide
  have hdescent : baseEnd_1259373 < baseStart_1259373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259376 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 3]
def baseStart_1259376 : Nat := 118140960795 + 1259376 * 2 ^ 59
def prefixEnd_1259376 : Nat := 4983230072969 + 3 ^ 40 * 1259376 * 2
def baseEnd_1259376 : Nat := 646665212736769919308241

theorem tailTrace_1259376 : CollatzResearch.WordTrace tailWord_1259376 prefixEnd_1259376 646665212736769919308241 := by
  unfold tailWord_1259376
  simp only [CollatzResearch.WordTrace]
  refine ⟨22966608142751655571086991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30622144190335540761449321 22966608142751655571086991)
  ·
    refine ⟨34449912214127483356630487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22966608142751655571086991 34449912214127483356630487)
    ·
      refine ⟨51674868321191225034945731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34449912214127483356630487 51674868321191225034945731)
      ·
        refine ⟨77512302481786837552418597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51674868321191225034945731 77512302481786837552418597)
        ·
          refine ⟨14533556715335032041078487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77512302481786837552418597 14533556715335032041078487)
          ·
            refine ⟨21800335073002548061617731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14533556715335032041078487 21800335073002548061617731)
            ·
              refine ⟨32700502609503822092426597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21800335073002548061617731 32700502609503822092426597)
              ·
                refine ⟨6131344239281966642329987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32700502609503822092426597 6131344239281966642329987)
                ·
                  refine ⟨9197016358922949963494981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6131344239281966642329987 9197016358922949963494981)
                  ·
                    refine ⟨1724440567298053118155309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9197016358922949963494981 1724440567298053118155309)
                    ·
                      refine ⟨646665212736769919308241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1724440567298053118155309 646665212736769919308241)
                      ·
                        rfl

theorem cell23_1259376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_1259376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259376 prefixEnd_1259376 := by exact prefixLift 1259376
  have htrace : WordTrace (prefixWord ++ tailWord_1259376) baseStart_1259376 baseEnd_1259376 := by
    simpa [prefixWord, tailWord_1259376, baseEnd_1259376] using wordTrace_append hprefix tailTrace_1259376
  have hstable : (prefixWord ++ tailWord_1259376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259376).length < 2 ^ (prefixWord ++ tailWord_1259376).sum := by decide
  have hdescent : baseEnd_1259376 < baseStart_1259376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259379 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 10]
def baseStart_1259379 : Nat := 118140960795 + 1259379 * 2 ^ 59
def prefixEnd_1259379 : Nat := 4983230072969 + 3 ^ 40 * 1259379 * 2
def baseEnd_1259379 : Nat := 71851861464303711952303

theorem tailTrace_1259379 : CollatzResearch.WordTrace tailWord_1259379 prefixEnd_1259379 71851861464303711952303 := by
  unfold tailWord_1259379
  simp only [CollatzResearch.WordTrace]
  refine ⟨45933325704492442654533191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30622217136328295103022127 45933325704492442654533191)
  ·
    refine ⟨68899988556738663981799787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45933325704492442654533191 68899988556738663981799787)
    ·
      refine ⟨103349982835107995972699681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68899988556738663981799787 103349982835107995972699681)
      ·
        refine ⟨77512487126330996979524761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103349982835107995972699681 77512487126330996979524761)
        ·
          refine ⟨58134365344748247734643571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77512487126330996979524761 58134365344748247734643571)
          ·
            refine ⟨87201548017122371601965357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58134365344748247734643571 87201548017122371601965357)
            ·
              refine ⟨32700580506420889350737009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87201548017122371601965357 32700580506420889350737009)
              ·
                refine ⟨24525435379815667013052757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32700580506420889350737009 24525435379815667013052757)
                ·
                  refine ⟨71851861464303711952303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24525435379815667013052757 71851861464303711952303)
                  ·
                    rfl

theorem cell23_1259379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 10].length) (baseStart_1259379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259379 prefixEnd_1259379 := by exact prefixLift 1259379
  have htrace : WordTrace (prefixWord ++ tailWord_1259379) baseStart_1259379 baseEnd_1259379 := by
    simpa [prefixWord, tailWord_1259379, baseEnd_1259379] using wordTrace_append hprefix tailTrace_1259379
  have hstable : (prefixWord ++ tailWord_1259379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259379).length < 2 ^ (prefixWord ++ tailWord_1259379).sum := by decide
  have hdescent : baseEnd_1259379 < baseStart_1259379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259390 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1259390 : Nat := 118140960795 + 1259390 * 2 ^ 59
def prefixEnd_1259390 : Nat := 4983230072969 + 3 ^ 40 * 1259390 * 2
def baseEnd_1259390 : Nat := 646672401465932864533177

theorem tailTrace_1259390 : CollatzResearch.WordTrace tailWord_1259390 prefixEnd_1259390 646672401465932864533177 := by
  unfold tailWord_1259390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5741715863431573941647953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30622484604968394355455749 5741715863431573941647953)
  ·
    refine ⟨4306286897573680456235965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5741715863431573941647953 4306286897573680456235965)
    ·
      refine ⟨1614857586590130171088487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4306286897573680456235965 1614857586590130171088487)
      ·
        refine ⟨2422286379885195256632731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1614857586590130171088487 2422286379885195256632731)
        ·
          refine ⟨3633429569827792884949097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422286379885195256632731 3633429569827792884949097)
          ·
            refine ⟨2725072177370844663711823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3633429569827792884949097 2725072177370844663711823)
            ·
              refine ⟨4087608266056266995567735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725072177370844663711823 4087608266056266995567735)
              ·
                refine ⟨6131412399084400493351603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087608266056266995567735 6131412399084400493351603)
                ·
                  refine ⟨9197118598626600740027405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6131412399084400493351603 9197118598626600740027405)
                  ·
                    refine ⟨3448919474484975277510277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9197118598626600740027405 3448919474484975277510277)
                    ·
                      refine ⟨646672401465932864533177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3448919474484975277510277 646672401465932864533177)
                      ·
                        rfl

theorem cell23_1259390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1259390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259390 prefixEnd_1259390 := by exact prefixLift 1259390
  have htrace : WordTrace (prefixWord ++ tailWord_1259390) baseStart_1259390 baseEnd_1259390 := by
    simpa [prefixWord, tailWord_1259390, baseEnd_1259390] using wordTrace_append hprefix tailTrace_1259390
  have hstable : (prefixWord ++ tailWord_1259390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259390).length < 2 ^ (prefixWord ++ tailWord_1259390).sum := by decide
  have hdescent : baseEnd_1259390 < baseStart_1259390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259433 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 6, 3, 2]
def baseStart_1259433 : Nat := 118140960795 + 1259433 * 2 ^ 59
def prefixEnd_1259433 : Nat := 4983230072969 + 3 ^ 40 * 1259433 * 2
def baseEnd_1259433 : Nat := 646694481134076196295479

theorem tailTrace_1259433 : CollatzResearch.WordTrace tailWord_1259433 prefixEnd_1259433 646694481134076196295479 := by
  unfold tailWord_1259433
  simp only [CollatzResearch.WordTrace]
  refine ⟨45935295246296809876998953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30623530164197873251332635 45935295246296809876998953)
  ·
    refine ⟨34451471434722607407749215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45935295246296809876998953 34451471434722607407749215)
    ·
      refine ⟨51677207152083911111623823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34451471434722607407749215 51677207152083911111623823)
      ·
        refine ⟨77515810728125866667435735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51677207152083911111623823 77515810728125866667435735)
        ·
          refine ⟨116273716092188800001153603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77515810728125866667435735 116273716092188800001153603)
          ·
            refine ⟨174410574138283200001730405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116273716092188800001153603 174410574138283200001730405)
            ·
              refine ⟨32701982650928100000324451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174410574138283200001730405 32701982650928100000324451)
              ·
                refine ⟨49052973976392150000486677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32701982650928100000324451 49052973976392150000486677)
                ·
                  refine ⟨2299358155143382031272813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49052973976392150000486677 2299358155143382031272813)
                  ·
                    refine ⟨862259308178768261727305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2299358155143382031272813 862259308178768261727305)
                    ·
                      refine ⟨646694481134076196295479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 862259308178768261727305 646694481134076196295479)
                      ·
                        rfl

theorem cell23_1259433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 3, 2].length) (baseStart_1259433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259433 prefixEnd_1259433 := by exact prefixLift 1259433
  have htrace : WordTrace (prefixWord ++ tailWord_1259433) baseStart_1259433 baseEnd_1259433 := by
    simpa [prefixWord, tailWord_1259433, baseEnd_1259433] using wordTrace_append hprefix tailTrace_1259433
  have hstable : (prefixWord ++ tailWord_1259433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259433).length < 2 ^ (prefixWord ++ tailWord_1259433).sum := by decide
  have hdescent : baseEnd_1259433 < baseStart_1259433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259443 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 1, 5]
def baseStart_1259443 : Nat := 118140960795 + 1259443 * 2 ^ 59
def prefixEnd_1259443 : Nat := 4983230072969 + 3 ^ 40 * 1259443 * 2
def baseEnd_1259443 : Nat := 215566538646873719056811

theorem tailTrace_1259443 : CollatzResearch.WordTrace tailWord_1259443 prefixEnd_1259443 215566538646873719056811 := by
  unfold tailWord_1259443
  simp only [CollatzResearch.WordTrace]
  refine ⟨45935659976260581584862983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30623773317507054389908655 45935659976260581584862983)
  ·
    refine ⟨68903489964390872377294475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45935659976260581584862983 68903489964390872377294475)
    ·
      refine ⟨103355234946586308565941713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68903489964390872377294475 103355234946586308565941713)
      ·
        refine ⟨77516426209939731424456285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103355234946586308565941713 77516426209939731424456285)
        ·
          refine ⟨29068659828727399284171107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77516426209939731424456285 29068659828727399284171107)
          ·
            refine ⟨43602989743091098926256661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29068659828727399284171107 43602989743091098926256661)
            ·
              refine ⟨2043890144207395262168281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43602989743091098926256661 2043890144207395262168281)
              ·
                refine ⟨1532917608155546446626211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043890144207395262168281 1532917608155546446626211)
                ·
                  refine ⟨2299376412233319669939317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532917608155546446626211 2299376412233319669939317)
                  ·
                    refine ⟨215566538646873719056811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2299376412233319669939317 215566538646873719056811)
                    ·
                      rfl

theorem cell23_1259443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 5].length) (baseStart_1259443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259443 prefixEnd_1259443 := by exact prefixLift 1259443
  have htrace : WordTrace (prefixWord ++ tailWord_1259443) baseStart_1259443 baseEnd_1259443 := by
    simpa [prefixWord, tailWord_1259443, baseEnd_1259443] using wordTrace_append hprefix tailTrace_1259443
  have hstable : (prefixWord ++ tailWord_1259443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259443).length < 2 ^ (prefixWord ++ tailWord_1259443).sum := by decide
  have hdescent : baseEnd_1259443 < baseStart_1259443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259456 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 3, 6]
def baseStart_1259456 : Nat := 118140960795 + 1259456 * 2 ^ 59
def prefixEnd_1259456 : Nat := 4983230072969 + 3 ^ 40 * 1259456 * 2
def baseEnd_1259456 : Nat := 215568763729709868769291

theorem tailTrace_1259456 : CollatzResearch.WordTrace tailWord_1259456 prefixEnd_1259456 215568763729709868769291 := by
  unfold tailWord_1259456
  simp only [CollatzResearch.WordTrace]
  refine ⟨22968067062606742402543111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30624089416808989870057481 22968067062606742402543111)
  ·
    refine ⟨34452100593910113603814667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22968067062606742402543111 34452100593910113603814667)
    ·
      refine ⟨51678150890865170405722001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34452100593910113603814667 51678150890865170405722001)
      ·
        refine ⟨38758613168148877804291501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51678150890865170405722001 38758613168148877804291501)
        ·
          refine ⟨14534479938055829176609313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38758613168148877804291501 14534479938055829176609313)
          ·
            refine ⟨10900859953541871882456985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14534479938055829176609313 10900859953541871882456985)
            ·
              refine ⟨8175644965156403911842739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10900859953541871882456985 8175644965156403911842739)
              ·
                refine ⟨12263467447734605867764109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8175644965156403911842739 12263467447734605867764109)
                ·
                  refine ⟨4598800292900477200411541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12263467447734605867764109 4598800292900477200411541)
                  ·
                    refine ⟨215568763729709868769291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4598800292900477200411541 215568763729709868769291)
                    ·
                      rfl

theorem cell23_1259456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_1259456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259456 prefixEnd_1259456 := by exact prefixLift 1259456
  have htrace : WordTrace (prefixWord ++ tailWord_1259456) baseStart_1259456 baseEnd_1259456 := by
    simpa [prefixWord, tailWord_1259456, baseEnd_1259456] using wordTrace_append hprefix tailTrace_1259456
  have hstable : (prefixWord ++ tailWord_1259456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259456).length < 2 ^ (prefixWord ++ tailWord_1259456).sum := by decide
  have hdescent : baseEnd_1259456 < baseStart_1259456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259474 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1259474 : Nat := 118140960795 + 1259474 * 2 ^ 59
def prefixEnd_1259474 : Nat := 4983230072969 + 3 ^ 40 * 1259474 * 2
def baseEnd_1259474 : Nat := 646715533840910535882791

theorem tailTrace_1259474 : CollatzResearch.WordTrace tailWord_1259474 prefixEnd_1259474 646715533840910535882791 := by
  unfold tailWord_1259474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11484197659787068469810369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30624527092765515919494317 11484197659787068469810369)
  ·
    refine ⟨8613148244840301352357777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11484197659787068469810369 8613148244840301352357777)
    ·
      refine ⟨6459861183630226014268333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8613148244840301352357777 6459861183630226014268333)
      ·
        refine ⟨2422447943861334755350625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6459861183630226014268333 2422447943861334755350625)
        ·
          refine ⟨1816835957896001066512969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2422447943861334755350625 1816835957896001066512969)
          ·
            refine ⟨1362626968422000799884727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1816835957896001066512969 1362626968422000799884727)
            ·
              refine ⟨2043940452633001199827091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362626968422000799884727 2043940452633001199827091)
              ·
                refine ⟨3065910678949501799740637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043940452633001199827091 3065910678949501799740637)
                ·
                  refine ⟨1149716504606063174902739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3065910678949501799740637 1149716504606063174902739)
                  ·
                    refine ⟨1724574756909094762354109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1149716504606063174902739 1724574756909094762354109)
                    ·
                      refine ⟨646715533840910535882791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1724574756909094762354109 646715533840910535882791)
                      ·
                        rfl

theorem cell23_1259474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1259474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259474 prefixEnd_1259474 := by exact prefixLift 1259474
  have htrace : WordTrace (prefixWord ++ tailWord_1259474) baseStart_1259474 baseEnd_1259474 := by
    simpa [prefixWord, tailWord_1259474, baseEnd_1259474] using wordTrace_append hprefix tailTrace_1259474
  have hstable : (prefixWord ++ tailWord_1259474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259474).length < 2 ^ (prefixWord ++ tailWord_1259474).sum := by decide
  have hdescent : baseEnd_1259474 < baseStart_1259474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259513 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 3]
def baseStart_1259513 : Nat := 118140960795 + 1259513 * 2 ^ 59
def prefixEnd_1259513 : Nat := 4983230072969 + 3 ^ 40 * 1259513 * 2
def baseEnd_1259513 : Nat := 646735559586435883295111

theorem tailTrace_1259513 : CollatzResearch.WordTrace tailWord_1259513 prefixEnd_1259513 646735559586435883295111 := by
  unfold tailWord_1259513
  simp only [CollatzResearch.WordTrace]
  refine ⟨45938213086006983539911193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30625475390671322359940795 45938213086006983539911193)
  ·
    refine ⟨34453659814505237654933395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45938213086006983539911193 34453659814505237654933395)
    ·
      refine ⟨51680489721757856482400093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34453659814505237654933395 51680489721757856482400093)
      ·
        refine ⟨19380183645659196180900035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51680489721757856482400093 19380183645659196180900035)
        ·
          refine ⟨29070275468488794271350053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19380183645659196180900035 29070275468488794271350053)
          ·
            refine ⟨5450676650341648925878135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29070275468488794271350053 5450676650341648925878135)
            ·
              refine ⟨8176014975512473388817203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450676650341648925878135 8176014975512473388817203)
              ·
                refine ⟨12264022463268710083225805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8176014975512473388817203 12264022463268710083225805)
                ·
                  refine ⟨4599008423725766281209677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12264022463268710083225805 4599008423725766281209677)
                  ·
                    refine ⟨1724628158897162355453629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4599008423725766281209677 1724628158897162355453629)
                    ·
                      refine ⟨646735559586435883295111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1724628158897162355453629 646735559586435883295111)
                      ·
                        rfl

theorem cell23_1259513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_1259513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259513 prefixEnd_1259513 := by exact prefixLift 1259513
  have htrace : WordTrace (prefixWord ++ tailWord_1259513) baseStart_1259513 baseEnd_1259513 := by
    simpa [prefixWord, tailWord_1259513, baseEnd_1259513] using wordTrace_append hprefix tailTrace_1259513
  have hstable : (prefixWord ++ tailWord_1259513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259513).length < 2 ^ (prefixWord ++ tailWord_1259513).sum := by decide
  have hdescent : baseEnd_1259513 < baseStart_1259513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259524 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_1259524 : Nat := 118140960795 + 1259524 * 2 ^ 59
def prefixEnd_1259524 : Nat := 4983230072969 + 3 ^ 40 * 1259524 * 2
def baseEnd_1259524 : Nat := 215580402624545113419187

theorem tailTrace_1259524 : CollatzResearch.WordTrace tailWord_1259524 prefixEnd_1259524 215580402624545113419187 := by
  unfold tailWord_1259524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22969307144483566209280813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30625742859311421612374417 22969307144483566209280813)
  ·
    refine ⟨8613490179181337328480305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22969307144483566209280813 8613490179181337328480305)
    ·
      refine ⟨6460117634386002996360229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8613490179181337328480305 6460117634386002996360229)
      ·
        refine ⟨1211272056447375561817543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6460117634386002996360229 1211272056447375561817543)
        ·
          refine ⟨1816908084671063342726315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211272056447375561817543 1816908084671063342726315)
          ·
            refine ⟨2725362127006595014089473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816908084671063342726315 2725362127006595014089473)
            ·
              refine ⟨2044021595254946260567105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2725362127006595014089473 2044021595254946260567105)
              ·
                refine ⟨1533016196441209695425329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044021595254946260567105 1533016196441209695425329)
                ·
                  refine ⟨1149762147330907271568997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1533016196441209695425329 1149762147330907271568997)
                  ·
                    refine ⟨215580402624545113419187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1149762147330907271568997 215580402624545113419187)
                    ·
                      rfl

theorem cell23_1259524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_1259524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259524 prefixEnd_1259524 := by exact prefixLift 1259524
  have htrace : WordTrace (prefixWord ++ tailWord_1259524) baseStart_1259524 baseEnd_1259524 := by
    simpa [prefixWord, tailWord_1259524, baseEnd_1259524] using wordTrace_append hprefix tailTrace_1259524
  have hstable : (prefixWord ++ tailWord_1259524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259524).length < 2 ^ (prefixWord ++ tailWord_1259524).sum := by decide
  have hdescent : baseEnd_1259524 < baseStart_1259524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259573 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1259573 : Nat := 118140960795 + 1259573 * 2 ^ 59
def prefixEnd_1259573 : Nat := 4983230072969 + 3 ^ 40 * 1259573 * 2
def baseEnd_1259573 : Nat := 646766368425705648544835

theorem tailTrace_1259573 : CollatzResearch.WordTrace tailWord_1259573 prefixEnd_1259573 646766368425705648544835 := by
  unfold tailWord_1259573
  simp only [CollatzResearch.WordTrace]
  refine ⟨45940401465789613787095373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30626934310526409191396915 45940401465789613787095373)
  ·
    refine ⟨17227650549671105170160765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45940401465789613787095373 17227650549671105170160765)
    ·
      refine ⟨6460368956126664438810287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17227650549671105170160765 6460368956126664438810287)
      ·
        refine ⟨9690553434189996658215431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6460368956126664438810287 9690553434189996658215431)
        ·
          refine ⟨14535830151284994987323147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9690553434189996658215431 14535830151284994987323147)
          ·
            refine ⟨21803745226927492480984721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14535830151284994987323147 21803745226927492480984721)
            ·
              refine ⟨16352808920195619360738541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21803745226927492480984721 16352808920195619360738541)
              ·
                refine ⟨6132303345073357260276953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16352808920195619360738541 6132303345073357260276953)
                ·
                  refine ⟨4599227508805017945207715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6132303345073357260276953 4599227508805017945207715)
                  ·
                    refine ⟨6898841263207526917811573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4599227508805017945207715 6898841263207526917811573)
                    ·
                      refine ⟨646766368425705648544835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6898841263207526917811573 646766368425705648544835)
                      ·
                        rfl

theorem cell23_1259573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1259573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259573 prefixEnd_1259573 := by exact prefixLift 1259573
  have htrace : WordTrace (prefixWord ++ tailWord_1259573) baseStart_1259573 baseEnd_1259573 := by
    simpa [prefixWord, tailWord_1259573, baseEnd_1259573] using wordTrace_append hprefix tailTrace_1259573
  have hstable : (prefixWord ++ tailWord_1259573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259573).length < 2 ^ (prefixWord ++ tailWord_1259573).sum := by decide
  have hdescent : baseEnd_1259573 < baseStart_1259573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259574 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_1259574 : Nat := 118140960795 + 1259574 * 2 ^ 59
def prefixEnd_1259574 : Nat := 4983230072969 + 3 ^ 40 * 1259574 * 2
def baseEnd_1259574 : Nat := 646766881906360144632331

theorem tailTrace_1259574 : CollatzResearch.WordTrace tailWord_1259574 prefixEnd_1259574 646766881906360144632331 := by
  unfold tailWord_1259574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871277371174124434867611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30626958625857327305254517 2871277371174124434867611)
  ·
    refine ⟨4306916056761186652301417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2871277371174124434867611 4306916056761186652301417)
    ·
      refine ⟨3230187042570889989226063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4306916056761186652301417 3230187042570889989226063)
      ·
        refine ⟨4845280563856334983839095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3230187042570889989226063 4845280563856334983839095)
        ·
          refine ⟨7267920845784502475758643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845280563856334983839095 7267920845784502475758643)
          ·
            refine ⟨10901881268676753713637965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7267920845784502475758643 10901881268676753713637965)
            ·
              refine ⟨4088205475753782642614237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10901881268676753713637965 4088205475753782642614237)
              ·
                refine ⟨1533077053407668490980339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4088205475753782642614237 1533077053407668490980339)
                ·
                  refine ⟨2299615580111502736470509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533077053407668490980339 2299615580111502736470509)
                  ·
                    refine ⟨862355842541813526176441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2299615580111502736470509 862355842541813526176441)
                    ·
                      refine ⟨646766881906360144632331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 862355842541813526176441 646766881906360144632331)
                      ·
                        rfl

theorem cell23_1259574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_1259574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259574 prefixEnd_1259574 := by exact prefixLift 1259574
  have htrace : WordTrace (prefixWord ++ tailWord_1259574) baseStart_1259574 baseEnd_1259574 := by
    simpa [prefixWord, tailWord_1259574, baseEnd_1259574] using wordTrace_append hprefix tailTrace_1259574
  have hstable : (prefixWord ++ tailWord_1259574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259574).length < 2 ^ (prefixWord ++ tailWord_1259574).sum := by decide
  have hdescent : baseEnd_1259574 < baseStart_1259574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259583 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_1259583 : Nat := 118140960795 + 1259583 * 2 ^ 59
def prefixEnd_1259583 : Nat := 4983230072969 + 3 ^ 40 * 1259583 * 2
def baseEnd_1259583 : Nat := 646771503232250609419789

theorem tailTrace_1259583 : CollatzResearch.WordTrace tailWord_1259583 prefixEnd_1259583 646771503232250609419789 := by
  unfold tailWord_1259583
  simp only [CollatzResearch.WordTrace]
  refine ⟨45940766195753385494959403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30627177463835590329972935 45940766195753385494959403)
  ·
    refine ⟨68911149293630078242439105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45940766195753385494959403 68911149293630078242439105)
    ·
      refine ⟨51683361970222558681829329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68911149293630078242439105 51683361970222558681829329)
      ·
        refine ⟨38762521477666919011371997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51683361970222558681829329 38762521477666919011371997)
        ·
          refine ⟨14535945554125094629264499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38762521477666919011371997 14535945554125094629264499)
          ·
            refine ⟨21803918331187641943896749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14535945554125094629264499 21803918331187641943896749)
            ·
              refine ⟨8176469374195365728961281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21803918331187641943896749 8176469374195365728961281)
              ·
                refine ⟨6132352030646524296720961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8176469374195365728961281 6132352030646524296720961)
                ·
                  refine ⟨4599264022984893222540721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6132352030646524296720961 4599264022984893222540721)
                  ·
                    refine ⟨3449448017238669916905541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4599264022984893222540721 3449448017238669916905541)
                    ·
                      refine ⟨646771503232250609419789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3449448017238669916905541 646771503232250609419789)
                      ·
                        rfl

theorem cell23_1259583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_1259583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259583 prefixEnd_1259583 := by exact prefixLift 1259583
  have htrace : WordTrace (prefixWord ++ tailWord_1259583) baseStart_1259583 baseEnd_1259583 := by
    simpa [prefixWord, tailWord_1259583, baseEnd_1259583] using wordTrace_append hprefix tailTrace_1259583
  have hstable : (prefixWord ++ tailWord_1259583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259583).length < 2 ^ (prefixWord ++ tailWord_1259583).sum := by decide
  have hdescent : baseEnd_1259583 < baseStart_1259583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259587 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 2, 2, 2]
def baseStart_1259587 : Nat := 118140960795 + 1259587 * 2 ^ 59
def prefixEnd_1259587 : Nat := 4983230072969 + 3 ^ 40 * 1259587 * 2
def baseEnd_1259587 : Nat := 646773557154868593769771

theorem tailTrace_1259587 : CollatzResearch.WordTrace tailWord_1259587 prefixEnd_1259587 646773557154868593769771 := by
  unfold tailWord_1259587
  simp only [CollatzResearch.WordTrace]
  refine ⟨45940912087738894178105015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30627274725159262785403343 45940912087738894178105015)
  ·
    refine ⟨68911368131608341267157523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45940912087738894178105015 68911368131608341267157523)
    ·
      refine ⟨103367052197412511900736285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68911368131608341267157523 103367052197412511900736285)
      ·
        refine ⟨38762644574029691962776107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103367052197412511900736285 38762644574029691962776107)
        ·
          refine ⟨58143966861044537944164161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38762644574029691962776107 58143966861044537944164161)
          ·
            refine ⟨43607975145783403458123121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58143966861044537944164161 43607975145783403458123121)
            ·
              refine ⟨32705981359337552593592341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43607975145783403458123121 32705981359337552593592341)
              ·
                refine ⟨1533092876218947777824641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32705981359337552593592341 1533092876218947777824641)
                ·
                  refine ⟨1149819657164210833368481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1533092876218947777824641 1149819657164210833368481)
                  ·
                    refine ⟨862364742873158125026361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1149819657164210833368481 862364742873158125026361)
                    ·
                      refine ⟨646773557154868593769771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 862364742873158125026361 646773557154868593769771)
                      ·
                        rfl

theorem cell23_1259587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_1259587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259587 prefixEnd_1259587 := by exact prefixLift 1259587
  have htrace : WordTrace (prefixWord ++ tailWord_1259587) baseStart_1259587 baseEnd_1259587 := by
    simpa [prefixWord, tailWord_1259587, baseEnd_1259587] using wordTrace_append hprefix tailTrace_1259587
  have hstable : (prefixWord ++ tailWord_1259587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259587).length < 2 ^ (prefixWord ++ tailWord_1259587).sum := by decide
  have hdescent : baseEnd_1259587 < baseStart_1259587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259593 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 7]
def baseStart_1259593 : Nat := 118140960795 + 1259593 * 2 ^ 59
def prefixEnd_1259593 : Nat := 4983230072969 + 3 ^ 40 * 1259593 * 2
def baseEnd_1259593 : Nat := 71864070893199507810527

theorem tailTrace_1259593 : CollatzResearch.WordTrace tailWord_1259593 prefixEnd_1259593 71864070893199507810527 := by
  unfold tailWord_1259593
  simp only [CollatzResearch.WordTrace]
  refine ⟨45941130925717157202823433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30627420617144771468548955 45941130925717157202823433)
  ·
    refine ⟨34455848194287867902117575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45941130925717157202823433 34455848194287867902117575)
    ·
      refine ⟨51683772291431801853176363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34455848194287867902117575 51683772291431801853176363)
      ·
        refine ⟨77525658437147702779764545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51683772291431801853176363 77525658437147702779764545)
        ·
          refine ⟨58144243827860777084823409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77525658437147702779764545 58144243827860777084823409)
          ·
            refine ⟨43608182870895582813617557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58144243827860777084823409 43608182870895582813617557)
            ·
              refine ⟨2044133572073230444388323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43608182870895582813617557 2044133572073230444388323)
              ·
                refine ⟨3066200358109845666582485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2044133572073230444388323 3066200358109845666582485)
                ·
                  refine ⟨71864070893199507810527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3066200358109845666582485 71864070893199507810527)
                  ·
                    rfl

theorem cell23_1259593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 7].length) (baseStart_1259593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259593 prefixEnd_1259593 := by exact prefixLift 1259593
  have htrace : WordTrace (prefixWord ++ tailWord_1259593) baseStart_1259593 baseEnd_1259593 := by
    simpa [prefixWord, tailWord_1259593, baseEnd_1259593] using wordTrace_append hprefix tailTrace_1259593
  have hstable : (prefixWord ++ tailWord_1259593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259593).length < 2 ^ (prefixWord ++ tailWord_1259593).sum := by decide
  have hdescent : baseEnd_1259593 < baseStart_1259593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259603 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 3]
def baseStart_1259603 : Nat := 118140960795 + 1259603 * 2 ^ 59
def prefixEnd_1259603 : Nat := 4983230072969 + 3 ^ 40 * 1259603 * 2
def baseEnd_1259603 : Nat := 646781772845340531169697

theorem tailTrace_1259603 : CollatzResearch.WordTrace tailWord_1259603 prefixEnd_1259603 646781772845340531169697 := by
  unfold tailWord_1259603
  simp only [CollatzResearch.WordTrace]
  refine ⟨45941495655680928910687463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30627663770453952607124975 45941495655680928910687463)
  ·
    refine ⟨68912243483521393366031195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45941495655680928910687463 68912243483521393366031195)
    ·
      refine ⟨103368365225282090049046793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68912243483521393366031195 103368365225282090049046793)
      ·
        refine ⟨77526273918961567536785095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103368365225282090049046793 77526273918961567536785095)
        ·
          refine ⟨116289410878442351305177643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77526273918961567536785095 116289410878442351305177643)
          ·
            refine ⟨174434116317663526957766465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116289410878442351305177643 174434116317663526957766465)
            ·
              refine ⟨130825587238247645218324849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174434116317663526957766465 130825587238247645218324849)
              ·
                refine ⟨98119190428685733913743637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130825587238247645218324849 98119190428685733913743637)
                ·
                  refine ⟨4599337051344643777206733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98119190428685733913743637 4599337051344643777206733)
                  ·
                    refine ⟨1724751394254241416452525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4599337051344643777206733 1724751394254241416452525)
                    ·
                      refine ⟨646781772845340531169697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1724751394254241416452525 646781772845340531169697)
                      ·
                        rfl

theorem cell23_1259603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_1259603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259603 prefixEnd_1259603 := by exact prefixLift 1259603
  have htrace : WordTrace (prefixWord ++ tailWord_1259603) baseStart_1259603 baseEnd_1259603 := by
    simpa [prefixWord, tailWord_1259603, baseEnd_1259603] using wordTrace_append hprefix tailTrace_1259603
  have hstable : (prefixWord ++ tailWord_1259603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259603).length < 2 ^ (prefixWord ++ tailWord_1259603).sum := by decide
  have hdescent : baseEnd_1259603 < baseStart_1259603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259623 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 1, 7]
def baseStart_1259623 : Nat := 118140960795 + 1259623 * 2 ^ 59
def prefixEnd_1259623 : Nat := 4983230072969 + 3 ^ 40 * 1259623 * 2
def baseEnd_1259623 : Nat := 215597347486143484306535

theorem tailTrace_1259623 : CollatzResearch.WordTrace tailWord_1259623 prefixEnd_1259623 215597347486143484306535 := by
  unfold tailWord_1259623
  simp only [CollatzResearch.WordTrace]
  refine ⟨45942225115608472326415523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30628150077072314884277015 45942225115608472326415523)
  ·
    refine ⟨68913337673412708489623285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45942225115608472326415523 68913337673412708489623285)
    ·
      refine ⟨6460625406882441420902183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68913337673412708489623285 6460625406882441420902183)
      ·
        refine ⟨9690938110323662131353275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6460625406882441420902183 9690938110323662131353275)
        ·
          refine ⟨14536407165485493197029913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9690938110323662131353275 14536407165485493197029913)
          ·
            refine ⟨10902305374114119897772435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14536407165485493197029913 10902305374114119897772435)
            ·
              refine ⟨16353458061171179846658653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10902305374114119897772435 16353458061171179846658653)
              ·
                refine ⟨6132546772939192442496995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16353458061171179846658653 6132546772939192442496995)
                ·
                  refine ⟨9198820159408788663745493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6132546772939192442496995 9198820159408788663745493)
                  ·
                    refine ⟨215597347486143484306535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9198820159408788663745493 215597347486143484306535)
                    ·
                      rfl

theorem cell23_1259623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_1259623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259623 prefixEnd_1259623 := by exact prefixLift 1259623
  have htrace : WordTrace (prefixWord ++ tailWord_1259623) baseStart_1259623 baseEnd_1259623 := by
    simpa [prefixWord, tailWord_1259623, baseEnd_1259623] using wordTrace_append hprefix tailTrace_1259623
  have hstable : (prefixWord ++ tailWord_1259623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259623).length < 2 ^ (prefixWord ++ tailWord_1259623).sum := by decide
  have hdescent : baseEnd_1259623 < baseStart_1259623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259633 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_1259633 : Nat := 118140960795 + 1259633 * 2 ^ 59
def prefixEnd_1259633 : Nat := 4983230072969 + 3 ^ 40 * 1259633 * 2
def baseEnd_1259633 : Nat := 646797177264975413794559

theorem tailTrace_1259633 : CollatzResearch.WordTrace tailWord_1259633 prefixEnd_1259633 646797177264975413794559 := by
  unfold tailWord_1259633
  simp only [CollatzResearch.WordTrace]
  refine ⟨45942589845572244034279553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30628393230381496022853035 45942589845572244034279553)
  ·
    refine ⟨34456942384179183025709665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45942589845572244034279553 34456942384179183025709665)
    ·
      refine ⟨25842706788134387269282249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34456942384179183025709665 25842706788134387269282249)
      ·
        refine ⟨19382030091100790451961687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25842706788134387269282249 19382030091100790451961687)
        ·
          refine ⟨29073045136651185677942531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19382030091100790451961687 29073045136651185677942531)
          ·
            refine ⟨43609567704976778516913797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29073045136651185677942531 43609567704976778516913797)
            ·
              refine ⟨8176793944683145971921337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43609567704976778516913797 8176793944683145971921337)
              ·
                refine ⟨6132595458512359478941003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8176793944683145971921337 6132595458512359478941003)
                ·
                  refine ⟨9198893187768539218411505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6132595458512359478941003 9198893187768539218411505)
                  ·
                    refine ⟨6899169890826404413808629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9198893187768539218411505 6899169890826404413808629)
                    ·
                      refine ⟨646797177264975413794559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6899169890826404413808629 646797177264975413794559)
                      ·
                        rfl

theorem cell23_1259633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_1259633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259633 prefixEnd_1259633 := by exact prefixLift 1259633
  have htrace : WordTrace (prefixWord ++ tailWord_1259633) baseStart_1259633 baseEnd_1259633 := by
    simpa [prefixWord, tailWord_1259633, baseEnd_1259633] using wordTrace_append hprefix tailTrace_1259633
  have hstable : (prefixWord ++ tailWord_1259633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259633).length < 2 ^ (prefixWord ++ tailWord_1259633).sum := by decide
  have hdescent : baseEnd_1259633 < baseStart_1259633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259673 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_1259673 : Nat := 118140960795 + 1259673 * 2 ^ 59
def prefixEnd_1259673 : Nat := 4983230072969 + 3 ^ 40 * 1259673 * 2
def baseEnd_1259673 : Nat := 646817716491155257294375

theorem tailTrace_1259673 : CollatzResearch.WordTrace tailWord_1259673 prefixEnd_1259673 646817716491155257294375 := by
  unfold tailWord_1259673
  simp only [CollatzResearch.WordTrace]
  refine ⟨45944048765427330865735673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30629365843618220577157115 45944048765427330865735673)
  ·
    refine ⟨34458036574070498149301755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45944048765427330865735673 34458036574070498149301755)
    ·
      refine ⟨51687054861105747223952633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34458036574070498149301755 51687054861105747223952633)
      ·
        refine ⟨38765291145829310417964475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51687054861105747223952633 38765291145829310417964475)
        ·
          refine ⟨58147936718743965626946713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38765291145829310417964475 58147936718743965626946713)
          ·
            refine ⟨43610952539057974220210035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58147936718743965626946713 43610952539057974220210035)
            ·
              refine ⟨65416428808586961330315053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43610952539057974220210035 65416428808586961330315053)
              ·
                refine ⟨24531160803220110498868145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65416428808586961330315053 24531160803220110498868145)
                ·
                  refine ⟨18398370602415082874151109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24531160803220110498868145 18398370602415082874151109)
                  ·
                    refine ⟨3449694487952828038903333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18398370602415082874151109 3449694487952828038903333)
                    ·
                      refine ⟨646817716491155257294375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3449694487952828038903333 646817716491155257294375)
                      ·
                        rfl

theorem cell23_1259673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_1259673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259673 prefixEnd_1259673 := by exact prefixLift 1259673
  have htrace : WordTrace (prefixWord ++ tailWord_1259673) baseStart_1259673 baseEnd_1259673 := by
    simpa [prefixWord, tailWord_1259673, baseEnd_1259673] using wordTrace_append hprefix tailTrace_1259673
  have hstable : (prefixWord ++ tailWord_1259673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259673).length < 2 ^ (prefixWord ++ tailWord_1259673).sum := by decide
  have hdescent : baseEnd_1259673 < baseStart_1259673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259677 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1259677 : Nat := 118140960795 + 1259677 * 2 ^ 59
def prefixEnd_1259677 : Nat := 4983230072969 + 3 ^ 40 * 1259677 * 2
def baseEnd_1259677 : Nat := 646819770413773241644357

theorem tailTrace_1259677 : CollatzResearch.WordTrace tailWord_1259677 prefixEnd_1259677 646819770413773241644357 := by
  unfold tailWord_1259677
  simp only [CollatzResearch.WordTrace]
  refine ⟨45944194657412839548881285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30629463104941893032587523 45944194657412839548881285)
  ·
    refine ⟨8614536498264907415415241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45944194657412839548881285 8614536498264907415415241)
    ·
      refine ⟨6460902373698680561561431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8614536498264907415415241 6460902373698680561561431)
      ·
        refine ⟨9691353560548020842342147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6460902373698680561561431 9691353560548020842342147)
        ·
          refine ⟨14537030340822031263513221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9691353560548020842342147 14537030340822031263513221)
          ·
            refine ⟨2725693188904130861908729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14537030340822031263513221 2725693188904130861908729)
            ·
              refine ⟨2044269891678098146431547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2725693188904130861908729 2044269891678098146431547)
              ·
                refine ⟨3066404837517147219647321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2044269891678098146431547 3066404837517147219647321)
                ·
                  refine ⟨2299803628137860414735491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3066404837517147219647321 2299803628137860414735491)
                  ·
                    refine ⟨3449705442206790622103237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2299803628137860414735491 3449705442206790622103237)
                    ·
                      refine ⟨646819770413773241644357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3449705442206790622103237 646819770413773241644357)
                      ·
                        rfl

theorem cell23_1259677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1259677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259677 prefixEnd_1259677 := by exact prefixLift 1259677
  have htrace : WordTrace (prefixWord ++ tailWord_1259677) baseStart_1259677 baseEnd_1259677 := by
    simpa [prefixWord, tailWord_1259677, baseEnd_1259677] using wordTrace_append hprefix tailTrace_1259677
  have hstable : (prefixWord ++ tailWord_1259677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259677).length < 2 ^ (prefixWord ++ tailWord_1259677).sum := by decide
  have hdescent : baseEnd_1259677 < baseStart_1259677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259723 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 7]
def baseStart_1259723 : Nat := 118140960795 + 1259723 * 2 ^ 59
def prefixEnd_1259723 : Nat := 4983230072969 + 3 ^ 40 * 1259723 * 2
def baseEnd_1259723 : Nat := 646843390523880061669145

theorem tailTrace_1259723 : CollatzResearch.WordTrace tailWord_1259723 prefixEnd_1259723 646843390523880061669145 := by
  unfold tailWord_1259723
  simp only [CollatzResearch.WordTrace]
  refine ⟨45945872415246189405055823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30630581610164126270037215 45945872415246189405055823)
  ·
    refine ⟨68918808622869284107583735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45945872415246189405055823 68918808622869284107583735)
    ·
      refine ⟨103378212934303926161375603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68918808622869284107583735 103378212934303926161375603)
      ·
        refine ⟨155067319401455889242063405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103378212934303926161375603 155067319401455889242063405)
        ·
          refine ⟨58150244775545958465773777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155067319401455889242063405 58150244775545958465773777)
          ·
            refine ⟨43612683581659468849330333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58150244775545958465773777 43612683581659468849330333)
            ·
              refine ⟨16354756343122300818498875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43612683581659468849330333 16354756343122300818498875)
              ·
                refine ⟨24532134514683451227748313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16354756343122300818498875 24532134514683451227748313)
                ·
                  refine ⟨18399100886012588420811235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24532134514683451227748313 18399100886012588420811235)
                  ·
                    refine ⟨27598651329018882631216853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18399100886012588420811235 27598651329018882631216853)
                    ·
                      refine ⟨646843390523880061669145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27598651329018882631216853 646843390523880061669145)
                      ·
                        rfl

theorem cell23_1259723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_1259723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259723 prefixEnd_1259723 := by exact prefixLift 1259723
  have htrace : WordTrace (prefixWord ++ tailWord_1259723) baseStart_1259723 baseEnd_1259723 := by
    simpa [prefixWord, tailWord_1259723, baseEnd_1259723] using wordTrace_append hprefix tailTrace_1259723
  have hstable : (prefixWord ++ tailWord_1259723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259723).length < 2 ^ (prefixWord ++ tailWord_1259723).sum := by decide
  have hdescent : baseEnd_1259723 < baseStart_1259723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259727 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 3]
def baseStart_1259727 : Nat := 118140960795 + 1259727 * 2 ^ 59
def prefixEnd_1259727 : Nat := 4983230072969 + 3 ^ 40 * 1259727 * 2
def baseEnd_1259727 : Nat := 646845444446498046019127

theorem tailTrace_1259727 : CollatzResearch.WordTrace tailWord_1259727 prefixEnd_1259727 646845444446498046019127 := by
  unfold tailWord_1259727
  simp only [CollatzResearch.WordTrace]
  refine ⟨45946018307231698088201435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30630678871487798725467623 45946018307231698088201435)
  ·
    refine ⟨68919027460847547132302153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45946018307231698088201435 68919027460847547132302153)
    ·
      refine ⟨51689270595635660349226615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68919027460847547132302153 51689270595635660349226615)
      ·
        refine ⟨77533905893453490523839923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51689270595635660349226615 77533905893453490523839923)
        ·
          refine ⟨116300858840180235785759885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77533905893453490523839923 116300858840180235785759885)
          ·
            refine ⟨43612822065067588419659957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116300858840180235785759885 43612822065067588419659957)
            ·
              refine ⟨4088702068600086414343121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43612822065067588419659957 4088702068600086414343121)
              ·
                refine ⟨3066526551450064810757341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4088702068600086414343121 3066526551450064810757341)
                ·
                  refine ⟨1149947456793774304034003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3066526551450064810757341 1149947456793774304034003)
                  ·
                    refine ⟨1724921185190661456051005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1149947456793774304034003 1724921185190661456051005)
                    ·
                      refine ⟨646845444446498046019127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1724921185190661456051005 646845444446498046019127)
                      ·
                        rfl

theorem cell23_1259727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 3].length) (baseStart_1259727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259727 prefixEnd_1259727 := by exact prefixLift 1259727
  have htrace : WordTrace (prefixWord ++ tailWord_1259727) baseStart_1259727 baseEnd_1259727 := by
    simpa [prefixWord, tailWord_1259727, baseEnd_1259727] using wordTrace_append hprefix tailTrace_1259727
  have hstable : (prefixWord ++ tailWord_1259727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259727).length < 2 ^ (prefixWord ++ tailWord_1259727).sum := by decide
  have hdescent : baseEnd_1259727 < baseStart_1259727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259770 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_1259770 : Nat := 118140960795 + 1259770 * 2 ^ 59
def prefixEnd_1259770 : Nat := 4983230072969 + 3 ^ 40 * 1259770 * 2
def baseEnd_1259770 : Nat := 646867524114641377781429

theorem tailTrace_1259770 : CollatzResearch.WordTrace tailWord_1259770 prefixEnd_1259770 646867524114641377781429 := by
  unfold tailWord_1259770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11486896661518979108004191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30631724430717277621344509 11486896661518979108004191)
  ·
    refine ⟨17230344992278468662006287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11486896661518979108004191 17230344992278468662006287)
    ·
      refine ⟨25845517488417702993009431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17230344992278468662006287 25845517488417702993009431)
      ·
        refine ⟨38768276232626554489514147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25845517488417702993009431 38768276232626554489514147)
        ·
          refine ⟨58152414348939831734271221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38768276232626554489514147 58152414348939831734271221)
          ·
            refine ⟨5451788845213109225087927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58152414348939831734271221 5451788845213109225087927)
            ·
              refine ⟨8177683267819663837631891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5451788845213109225087927 8177683267819663837631891)
              ·
                refine ⟨12266524901729495756447837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8177683267819663837631891 12266524901729495756447837)
                ·
                  refine ⟨4599946838148560908667939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12266524901729495756447837 4599946838148560908667939)
                  ·
                    refine ⟨6899920257222841363001909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4599946838148560908667939 6899920257222841363001909)
                    ·
                      refine ⟨646867524114641377781429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6899920257222841363001909 646867524114641377781429)
                      ·
                        rfl

theorem cell23_1259770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_1259770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259770 prefixEnd_1259770 := by exact prefixLift 1259770
  have htrace : WordTrace (prefixWord ++ tailWord_1259770) baseStart_1259770 baseEnd_1259770 := by
    simpa [prefixWord, tailWord_1259770, baseEnd_1259770] using wordTrace_append hprefix tailTrace_1259770
  have hstable : (prefixWord ++ tailWord_1259770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259770).length < 2 ^ (prefixWord ++ tailWord_1259770).sum := by decide
  have hdescent : baseEnd_1259770 < baseStart_1259770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259784 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_1259784 : Nat := 118140960795 + 1259784 * 2 ^ 59
def prefixEnd_1259784 : Nat := 4983230072969 + 3 ^ 40 * 1259784 * 2
def baseEnd_1259784 : Nat := 646874712843804323006365

theorem tailTrace_1259784 : CollatzResearch.WordTrace tailWord_1259784 prefixEnd_1259784 646874712843804323006365 := by
  unfold tailWord_1259784
  simp only [CollatzResearch.WordTrace]
  refine ⟨22974048634012598411513203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30632064845350131215350937 22974048634012598411513203)
  ·
    refine ⟨34461072951018897617269805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22974048634012598411513203 34461072951018897617269805)
    ·
      refine ⟨12922902356632086606476177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34461072951018897617269805 12922902356632086606476177)
      ·
        refine ⟨9692176767474064954857133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12922902356632086606476177 9692176767474064954857133)
        ·
          refine ⟨3634566287802774358071425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9692176767474064954857133 3634566287802774358071425)
          ·
            refine ⟨2725924715852080768553569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3634566287802774358071425 2725924715852080768553569)
            ·
              refine ⟨2044443536889060576415177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2725924715852080768553569 2044443536889060576415177)
              ·
                refine ⟨1533332652666795432311383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044443536889060576415177 1533332652666795432311383)
                ·
                  refine ⟨2299998979000193148467075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533332652666795432311383 2299998979000193148467075)
                  ·
                    refine ⟨3449998468500289722700613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2299998979000193148467075 3449998468500289722700613)
                    ·
                      refine ⟨646874712843804323006365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3449998468500289722700613 646874712843804323006365)
                      ·
                        rfl

theorem cell23_1259784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_1259784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259784 prefixEnd_1259784 := by exact prefixLift 1259784
  have htrace : WordTrace (prefixWord ++ tailWord_1259784) baseStart_1259784 baseEnd_1259784 := by
    simpa [prefixWord, tailWord_1259784, baseEnd_1259784] using wordTrace_append hprefix tailTrace_1259784
  have hstable : (prefixWord ++ tailWord_1259784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259784).length < 2 ^ (prefixWord ++ tailWord_1259784).sum := by decide
  have hdescent : baseEnd_1259784 < baseStart_1259784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259790 : List Nat := [4, 1, 1, 2, 1, 2, 3, 9]
def baseStart_1259790 : Nat := 118140960795 + 1259790 * 2 ^ 59
def prefixEnd_1259790 : Nat := 4983230072969 + 3 ^ 40 * 1259790 * 2
def baseEnd_1259790 : Nat := 23958436804730788871531

theorem tailTrace_1259790 : CollatzResearch.WordTrace tailWord_1259790 prefixEnd_1259790 23958436804730788871531 := by
  unfold tailWord_1259790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743539513250432480968103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30632210737335639898496549 5743539513250432480968103)
  ·
    refine ⟨8615309269875648721452155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5743539513250432480968103 8615309269875648721452155)
    ·
      refine ⟨12922963904813473082178233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8615309269875648721452155 12922963904813473082178233)
      ·
        refine ⟨9692222928610104811633675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12922963904813473082178233 9692222928610104811633675)
        ·
          refine ⟨14538334392915157217450513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9692222928610104811633675 14538334392915157217450513)
          ·
            refine ⟨10903750794686367913087885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14538334392915157217450513 10903750794686367913087885)
            ·
              refine ⟨4088906548007387967407957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10903750794686367913087885 4088906548007387967407957)
              ·
                refine ⟨23958436804730788871531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4088906548007387967407957 23958436804730788871531)
                ·
                  rfl

theorem cell23_1259790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_1259790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259790 prefixEnd_1259790 := by exact prefixLift 1259790
  have htrace : WordTrace (prefixWord ++ tailWord_1259790) baseStart_1259790 baseEnd_1259790 := by
    simpa [prefixWord, tailWord_1259790, baseEnd_1259790] using wordTrace_append hprefix tailTrace_1259790
  have hstable : (prefixWord ++ tailWord_1259790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259790).length < 2 ^ (prefixWord ++ tailWord_1259790).sum := by decide
  have hdescent : baseEnd_1259790 < baseStart_1259790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259828 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1259828 : Nat := 118140960795 + 1259828 * 2 ^ 59
def prefixEnd_1259828 : Nat := 4983230072969 + 3 ^ 40 * 1259828 * 2
def baseEnd_1259828 : Nat := 215632435330867383618721

theorem tailTrace_1259828 : CollatzResearch.WordTrace tailWord_1259828 prefixEnd_1259828 215632435330867383618721 := by
  unfold tailWord_1259828
  simp only [CollatzResearch.WordTrace]
  refine ⟨22974851039932896168814069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30633134719910528225085425 22974851039932896168814069)
  ·
    refine ⟨2153892284993709015826319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22974851039932896168814069 2153892284993709015826319)
    ·
      refine ⟨3230838427490563523739479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2153892284993709015826319 3230838427490563523739479)
      ·
        refine ⟨4846257641235845285609219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3230838427490563523739479 4846257641235845285609219)
        ·
          refine ⟨7269386461853767928413829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4846257641235845285609219 7269386461853767928413829)
          ·
            refine ⟨1363009961597581486577593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7269386461853767928413829 1363009961597581486577593)
            ·
              refine ⟨1022257471198186114933195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1363009961597581486577593 1022257471198186114933195)
              ·
                refine ⟨1533386206797279172399793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022257471198186114933195 1533386206797279172399793)
                ·
                  refine ⟨1150039655097959379299845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1533386206797279172399793 1150039655097959379299845)
                  ·
                    refine ⟨215632435330867383618721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1150039655097959379299845 215632435330867383618721)
                    ·
                      rfl

theorem cell23_1259828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1259828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259828 prefixEnd_1259828 := by exact prefixLift 1259828
  have htrace : WordTrace (prefixWord ++ tailWord_1259828) baseStart_1259828 baseEnd_1259828 := by
    simpa [prefixWord, tailWord_1259828, baseEnd_1259828] using wordTrace_append hprefix tailTrace_1259828
  have hstable : (prefixWord ++ tailWord_1259828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259828).length < 2 ^ (prefixWord ++ tailWord_1259828).sum := by decide
  have hdescent : baseEnd_1259828 < baseStart_1259828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259840 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_1259840 : Nat := 118140960795 + 1259840 * 2 ^ 59
def prefixEnd_1259840 : Nat := 4983230072969 + 3 ^ 40 * 1259840 * 2
def baseEnd_1259840 : Nat := 646903467760456103906107

theorem tailTrace_1259840 : CollatzResearch.WordTrace tailWord_1259840 prefixEnd_1259840 646903467760456103906107 := by
  unfold tailWord_1259840
  simp only [CollatzResearch.WordTrace]
  refine ⟨22975069877911159193532487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30633426503881545591376649 22975069877911159193532487)
  ·
    refine ⟨34462604816866738790298731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22975069877911159193532487 34462604816866738790298731)
    ·
      refine ⟨51693907225300108185448097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34462604816866738790298731 51693907225300108185448097)
      ·
        refine ⟨38770430418975081139086073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51693907225300108185448097 38770430418975081139086073)
        ·
          refine ⟨29077822814231310854314555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38770430418975081139086073 29077822814231310854314555)
          ·
            refine ⟨43616734221346966281471833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29077822814231310854314555 43616734221346966281471833)
            ·
              refine ⟨32712550666010224711103875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43616734221346966281471833 32712550666010224711103875)
              ·
                refine ⟨49068825999015337066655813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32712550666010224711103875 49068825999015337066655813)
                ·
                  refine ⟨9200404874815375699997965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49068825999015337066655813 9200404874815375699997965)
                  ·
                    refine ⟨3450151828055765887499237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9200404874815375699997965 3450151828055765887499237)
                    ·
                      refine ⟨646903467760456103906107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3450151828055765887499237 646903467760456103906107)
                      ·
                        rfl

theorem cell23_1259840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_1259840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259840 prefixEnd_1259840 := by exact prefixLift 1259840
  have htrace : WordTrace (prefixWord ++ tailWord_1259840) baseStart_1259840 baseEnd_1259840 := by
    simpa [prefixWord, tailWord_1259840, baseEnd_1259840] using wordTrace_append hprefix tailTrace_1259840
  have hstable : (prefixWord ++ tailWord_1259840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259840).length < 2 ^ (prefixWord ++ tailWord_1259840).sum := by decide
  have hdescent : baseEnd_1259840 < baseStart_1259840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259850 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_1259850 : Nat := 118140960795 + 1259850 * 2 ^ 59
def prefixEnd_1259850 : Nat := 4983230072969 + 3 ^ 40 * 1259850 * 2
def baseEnd_1259850 : Nat := 215636200855667021593687

theorem tailTrace_1259850 : CollatzResearch.WordTrace tailWord_1259850 prefixEnd_1259850 215636200855667021593687 := by
  unfold tailWord_1259850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11487626121446522523732251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30633669657190726729952669 11487626121446522523732251)
  ·
    refine ⟨17231439182169783785598377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11487626121446522523732251 17231439182169783785598377)
    ·
      refine ⟨12923579386627337839198783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17231439182169783785598377 12923579386627337839198783)
      ·
        refine ⟨19385369079941006758798175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12923579386627337839198783 19385369079941006758798175)
        ·
          refine ⟨29078053619911510138197263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19385369079941006758798175 29078053619911510138197263)
          ·
            refine ⟨43617080429867265207295895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29078053619911510138197263 43617080429867265207295895)
            ·
              refine ⟨65425620644800897810943843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43617080429867265207295895 65425620644800897810943843)
              ·
                refine ⟨98138430967201346716415765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65425620644800897810943843 98138430967201346716415765)
                ·
                  refine ⟨4600238951587563127331989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98138430967201346716415765 4600238951587563127331989)
                  ·
                    refine ⟨215636200855667021593687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4600238951587563127331989 215636200855667021593687)
                    ·
                      rfl

theorem cell23_1259850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_1259850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259850 prefixEnd_1259850 := by exact prefixLift 1259850
  have htrace : WordTrace (prefixWord ++ tailWord_1259850) baseStart_1259850 baseEnd_1259850 := by
    simpa [prefixWord, tailWord_1259850, baseEnd_1259850] using wordTrace_append hprefix tailTrace_1259850
  have hstable : (prefixWord ++ tailWord_1259850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259850).length < 2 ^ (prefixWord ++ tailWord_1259850).sum := by decide
  have hdescent : baseEnd_1259850 < baseStart_1259850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259877 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_1259877 : Nat := 118140960795 + 1259877 * 2 ^ 59
def prefixEnd_1259877 : Nat := 4983230072969 + 3 ^ 40 * 1259877 * 2
def baseEnd_1259877 : Nat := 646922466544672459143437

theorem tailTrace_1259877 : CollatzResearch.WordTrace tailWord_1259877 prefixEnd_1259877 646922466544672459143437 := by
  unfold tailWord_1259877
  simp only [CollatzResearch.WordTrace]
  refine ⟨45951489256688273706161885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30634326171125515804107923 45951489256688273706161885)
  ·
    refine ⟨17231808471258102639810707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45951489256688273706161885 17231808471258102639810707)
    ·
      refine ⟨25847712706887153959716061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17231808471258102639810707 25847712706887153959716061)
      ·
        refine ⟨9692892265082682734893523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25847712706887153959716061 9692892265082682734893523)
        ·
          refine ⟨14539338397624024102340285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9692892265082682734893523 14539338397624024102340285)
          ·
            refine ⟨5452251899109009038377607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14539338397624024102340285 5452251899109009038377607)
            ·
              refine ⟨8178377848663513557566411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452251899109009038377607 8178377848663513557566411)
              ·
                refine ⟨12267566772995270336349617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8178377848663513557566411 12267566772995270336349617)
                ·
                  refine ⟨9200675079746452752262213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12267566772995270336349617 9200675079746452752262213)
                  ·
                    refine ⟨1725126577452459891049165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9200675079746452752262213 1725126577452459891049165)
                    ·
                      refine ⟨646922466544672459143437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1725126577452459891049165 646922466544672459143437)
                      ·
                        rfl

theorem cell23_1259877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_1259877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259877 prefixEnd_1259877 := by exact prefixLift 1259877
  have htrace : WordTrace (prefixWord ++ tailWord_1259877) baseStart_1259877 baseEnd_1259877 := by
    simpa [prefixWord, tailWord_1259877, baseEnd_1259877] using wordTrace_append hprefix tailTrace_1259877
  have hstable : (prefixWord ++ tailWord_1259877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259877).length < 2 ^ (prefixWord ++ tailWord_1259877).sum := by decide
  have hdescent : baseEnd_1259877 < baseStart_1259877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259920 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_1259920 : Nat := 118140960795 + 1259920 * 2 ^ 59
def prefixEnd_1259920 : Nat := 4983230072969 + 3 ^ 40 * 1259920 * 2
def baseEnd_1259920 : Nat := 646944546212815790905739

theorem tailTrace_1259920 : CollatzResearch.WordTrace tailWord_1259920 prefixEnd_1259920 646944546212815790905739 := by
  unfold tailWord_1259920
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976528797766246024988607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30635371730354994699984809 22976528797766246024988607)
  ·
    refine ⟨34464793196649369037482911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22976528797766246024988607 34464793196649369037482911)
    ·
      refine ⟨51697189794974053556224367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34464793196649369037482911 51697189794974053556224367)
      ·
        refine ⟨77545784692461080334336551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51697189794974053556224367 77545784692461080334336551)
        ·
          refine ⟨116318677038691620501504827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77545784692461080334336551 116318677038691620501504827)
          ·
            refine ⟨174478015558037430752257241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116318677038691620501504827 174478015558037430752257241)
            ·
              refine ⟨130858511668528073064192931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174478015558037430752257241 130858511668528073064192931)
              ·
                refine ⟨196287767502792109596289397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130858511668528073064192931 196287767502792109596289397)
                ·
                  refine ⟨18401978203386760274652131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196287767502792109596289397 18401978203386760274652131)
                  ·
                    refine ⟨27602967305080140411978197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18401978203386760274652131 27602967305080140411978197)
                    ·
                      refine ⟨646944546212815790905739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27602967305080140411978197 646944546212815790905739)
                      ·
                        rfl

theorem cell23_1259920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_1259920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259920 prefixEnd_1259920 := by exact prefixLift 1259920
  have htrace : WordTrace (prefixWord ++ tailWord_1259920) baseStart_1259920 baseEnd_1259920 := by
    simpa [prefixWord, tailWord_1259920, baseEnd_1259920] using wordTrace_append hprefix tailTrace_1259920
  have hstable : (prefixWord ++ tailWord_1259920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259920).length < 2 ^ (prefixWord ++ tailWord_1259920).sum := by decide
  have hdescent : baseEnd_1259920 < baseStart_1259920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259927 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 2, 5]
def baseStart_1259927 : Nat := 118140960795 + 1259927 * 2 ^ 59
def prefixEnd_1259927 : Nat := 4983230072969 + 3 ^ 40 * 1259927 * 2
def baseEnd_1259927 : Nat := 215649380192465754506069

theorem tailTrace_1259927 : CollatzResearch.WordTrace tailWord_1259927 prefixEnd_1259927 215649380192465754506069 := by
  unfold tailWord_1259927
  simp only [CollatzResearch.WordTrace]
  refine ⟨45953312906507132245482035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30635541937671421496988023 45953312906507132245482035)
  ·
    refine ⟨68929969359760698368223053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45953312906507132245482035 68929969359760698368223053)
    ·
      refine ⟨25848738509910261888083645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68929969359760698368223053 25848738509910261888083645)
      ·
        refine ⟨9693276941216348208031367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25848738509910261888083645 9693276941216348208031367)
        ·
          refine ⟨14539915411824522312047051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9693276941216348208031367 14539915411824522312047051)
          ·
            refine ⟨21809873117736783468070577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14539915411824522312047051 21809873117736783468070577)
            ·
              refine ⟨16357404838302587601052933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21809873117736783468070577 16357404838302587601052933)
              ·
                refine ⟨3067013407181735175197425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16357404838302587601052933 3067013407181735175197425)
                ·
                  refine ⟨2300260055386301381398069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3067013407181735175197425 2300260055386301381398069)
                  ·
                    refine ⟨215649380192465754506069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2300260055386301381398069 215649380192465754506069)
                    ·
                      rfl

theorem cell23_1259927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_1259927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259927 prefixEnd_1259927 := by exact prefixLift 1259927
  have htrace : WordTrace (prefixWord ++ tailWord_1259927) baseStart_1259927 baseEnd_1259927 := by
    simpa [prefixWord, tailWord_1259927, baseEnd_1259927] using wordTrace_append hprefix tailTrace_1259927
  have hstable : (prefixWord ++ tailWord_1259927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259927).length < 2 ^ (prefixWord ++ tailWord_1259927).sum := by decide
  have hdescent : baseEnd_1259927 < baseStart_1259927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259944 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1259944 : Nat := 118140960795 + 1259944 * 2 ^ 59
def prefixEnd_1259944 : Nat := 4983230072969 + 3 ^ 40 * 1259944 * 2
def baseEnd_1259944 : Nat := 215652289916174565668543

theorem tailTrace_1259944 : CollatzResearch.WordTrace tailWord_1259944 prefixEnd_1259944 215652289916174565668543 := by
  unfold tailWord_1259944
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976966473722772074425443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30635955298297029432567257 22976966473722772074425443)
  ·
    refine ⟨34465449710584158111638165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22976966473722772074425443 34465449710584158111638165)
    ·
      refine ⟨1615567955183632411483039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34465449710584158111638165 1615567955183632411483039)
      ·
        refine ⟨2423351932775448617224559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615567955183632411483039 2423351932775448617224559)
        ·
          refine ⟨3635027899163172925836839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423351932775448617224559 3635027899163172925836839)
          ·
            refine ⟨5452541848744759388755259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635027899163172925836839 5452541848744759388755259)
            ·
              refine ⟨8178812773117139083132889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452541848744759388755259 8178812773117139083132889)
              ·
                refine ⟨6134109579837854312349667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8178812773117139083132889 6134109579837854312349667)
                ·
                  refine ⟨9201164369756781468524501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6134109579837854312349667 9201164369756781468524501)
                  ·
                    refine ⟨215652289916174565668543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9201164369756781468524501 215652289916174565668543)
                    ·
                      rfl

theorem cell23_1259944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1259944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259944 prefixEnd_1259944 := by exact prefixLift 1259944
  have htrace : WordTrace (prefixWord ++ tailWord_1259944) baseStart_1259944 baseEnd_1259944 := by
    simpa [prefixWord, tailWord_1259944, baseEnd_1259944] using wordTrace_append hprefix tailTrace_1259944
  have hstable : (prefixWord ++ tailWord_1259944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259944).length < 2 ^ (prefixWord ++ tailWord_1259944).sum := by decide
  have hdescent : baseEnd_1259944 < baseStart_1259944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259964 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1259964 : Nat := 118140960795 + 1259964 * 2 ^ 59
def prefixEnd_1259964 : Nat := 4983230072969 + 3 ^ 40 * 1259964 * 2
def baseEnd_1259964 : Nat := 646967139361613618755537

theorem tailTrace_1259964 : CollatzResearch.WordTrace tailWord_1259964 prefixEnd_1259964 646967139361613618755537 := by
  unfold tailWord_1259964
  simp only [CollatzResearch.WordTrace]
  refine ⟨22977331203686543782289473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30636441604915391709719297 22977331203686543782289473)
  ·
    refine ⟨17232998402764907836717105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22977331203686543782289473 17232998402764907836717105)
    ·
      refine ⟨12924748802073680877537829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17232998402764907836717105 12924748802073680877537829)
      ·
        refine ⟨2423390400388815164538343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12924748802073680877537829 2423390400388815164538343)
        ·
          refine ⟨3635085600583222746807515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423390400388815164538343 3635085600583222746807515)
          ·
            refine ⟨5452628400874834120211273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635085600583222746807515 5452628400874834120211273)
            ·
              refine ⟨4089471300656125590158455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5452628400874834120211273 4089471300656125590158455)
              ·
                refine ⟨6134206950984188385237683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089471300656125590158455 6134206950984188385237683)
                ·
                  refine ⟨9201310426476282577856525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6134206950984188385237683 9201310426476282577856525)
                  ·
                    refine ⟨3450491409928605966696197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9201310426476282577856525 3450491409928605966696197)
                    ·
                      refine ⟨646967139361613618755537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3450491409928605966696197 646967139361613618755537)
                      ·
                        rfl

theorem cell23_1259964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1259964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1259964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1259964 prefixEnd_1259964 := by exact prefixLift 1259964
  have htrace : WordTrace (prefixWord ++ tailWord_1259964) baseStart_1259964 baseEnd_1259964 := by
    simpa [prefixWord, tailWord_1259964, baseEnd_1259964] using wordTrace_append hprefix tailTrace_1259964
  have hstable : (prefixWord ++ tailWord_1259964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259964).length < 2 ^ (prefixWord ++ tailWord_1259964).sum := by decide
  have hdescent : baseEnd_1259964 < baseStart_1259964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260018 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1260018 : Nat := 118140960795 + 1260018 * 2 ^ 59
def prefixEnd_1260018 : Nat := 4983230072969 + 3 ^ 40 * 1260018 * 2
def baseEnd_1260018 : Nat := 646994867316956407480289

theorem tailTrace_1260018 : CollatzResearch.WordTrace tailWord_1260018 prefixEnd_1260018 646994867316956407480289 := by
  unfold tailWord_1260018
  simp only [CollatzResearch.WordTrace]
  refine ⟨11489157987294363696761177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30637754632784969858029805 11489157987294363696761177)
  ·
    refine ⟨8616868490470772772570883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11489157987294363696761177 8616868490470772772570883)
    ·
      refine ⟨12925302735706159158856325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8616868490470772772570883 12925302735706159158856325)
      ·
        refine ⟨2423494262944904842285561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12925302735706159158856325 2423494262944904842285561)
        ·
          refine ⟨1817620697208678631714171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2423494262944904842285561 1817620697208678631714171)
          ·
            refine ⟨2726431045813017947571257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817620697208678631714171 2726431045813017947571257)
            ·
              refine ⟨2044823284359763460678443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2726431045813017947571257 2044823284359763460678443)
              ·
                refine ⟨3067234926539645191017665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2044823284359763460678443 3067234926539645191017665)
                ·
                  refine ⟨2300426194904733893263249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3067234926539645191017665 2300426194904733893263249)
                  ·
                    refine ⟨1725319646178550419947437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2300426194904733893263249 1725319646178550419947437)
                    ·
                      refine ⟨646994867316956407480289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1725319646178550419947437 646994867316956407480289)
                      ·
                        rfl

theorem cell23_1260018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1260018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260018 prefixEnd_1260018 := by exact prefixLift 1260018
  have htrace : WordTrace (prefixWord ++ tailWord_1260018) baseStart_1260018 baseEnd_1260018 := by
    simpa [prefixWord, tailWord_1260018, baseEnd_1260018] using wordTrace_append hprefix tailTrace_1260018
  have hstable : (prefixWord ++ tailWord_1260018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260018).length < 2 ^ (prefixWord ++ tailWord_1260018).sum := by decide
  have hdescent : baseEnd_1260018 < baseStart_1260018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260104 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_1260104 : Nat := 118140960795 + 1260104 * 2 ^ 59
def prefixEnd_1260104 : Nat := 4983230072969 + 3 ^ 40 * 1260104 * 2
def baseEnd_1260104 : Nat := 647039026653243071004893

theorem tailTrace_1260104 : CollatzResearch.WordTrace tailWord_1260104 prefixEnd_1260104 647039026653243071004893 := by
  unfold tailWord_1260104
  simp only [CollatzResearch.WordTrace]
  refine ⟨22979884313432945737337683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30639845751243927649783577 22979884313432945737337683)
  ·
    refine ⟨34469826470149418606006525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22979884313432945737337683 34469826470149418606006525)
    ·
      refine ⟨12926184926306031977252447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34469826470149418606006525 12926184926306031977252447)
      ·
        refine ⟨19389277389459047965878671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12926184926306031977252447 19389277389459047965878671)
        ·
          refine ⟨29083916084188571948818007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19389277389459047965878671 29083916084188571948818007)
          ·
            refine ⟨43625874126282857923227011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29083916084188571948818007 43625874126282857923227011)
            ·
              refine ⟨65438811189424286884840517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43625874126282857923227011 65438811189424286884840517)
              ·
                refine ⟨12269777098017053790907597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65438811189424286884840517 12269777098017053790907597)
                ·
                  refine ⟨4601166411756395171590349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12269777098017053790907597 4601166411756395171590349)
                  ·
                    refine ⟨1725437404408648189346381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4601166411756395171590349 1725437404408648189346381)
                    ·
                      refine ⟨647039026653243071004893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1725437404408648189346381 647039026653243071004893)
                      ·
                        rfl

theorem cell23_1260104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_1260104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260104 prefixEnd_1260104 := by exact prefixLift 1260104
  have htrace : WordTrace (prefixWord ++ tailWord_1260104) baseStart_1260104 baseEnd_1260104 := by
    simpa [prefixWord, tailWord_1260104, baseEnd_1260104] using wordTrace_append hprefix tailTrace_1260104
  have hstable : (prefixWord ++ tailWord_1260104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260104).length < 2 ^ (prefixWord ++ tailWord_1260104).sum := by decide
  have hdescent : baseEnd_1260104 < baseStart_1260104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260107 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 1, 9]
def baseStart_1260107 : Nat := 118140960795 + 1260107 * 2 ^ 59
def prefixEnd_1260107 : Nat := 4983230072969 + 3 ^ 40 * 1260107 * 2
def baseEnd_1260107 : Nat := 215680189031735519755793

theorem tailTrace_1260107 : CollatzResearch.WordTrace tailWord_1260107 prefixEnd_1260107 215680189031735519755793 := by
  unfold tailWord_1260107
  simp only [CollatzResearch.WordTrace]
  refine ⟨45959878045855022987034575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30639918697236681991356383 45959878045855022987034575)
  ·
    refine ⟨68939817068782534480551863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45959878045855022987034575 68939817068782534480551863)
    ·
      refine ⟨103409725603173801720827795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68939817068782534480551863 103409725603173801720827795)
      ·
        refine ⟨155114588404760702581241693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103409725603173801720827795 155114588404760702581241693)
        ·
          refine ⟨58167970651785263467965635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155114588404760702581241693 58167970651785263467965635)
          ·
            refine ⟨87251955977677895201948453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58167970651785263467965635 87251955977677895201948453)
            ·
              refine ⟨16359741745814605350365335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87251955977677895201948453 16359741745814605350365335)
              ·
                refine ⟨24539612618721908025548003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16359741745814605350365335 24539612618721908025548003)
                ·
                  refine ⟨36809418928082862038322005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24539612618721908025548003 36809418928082862038322005)
                  ·
                    refine ⟨215680189031735519755793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 36809418928082862038322005 215680189031735519755793)
                    ·
                      rfl

theorem cell23_1260107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 9].length) (baseStart_1260107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260107 prefixEnd_1260107 := by exact prefixLift 1260107
  have htrace : WordTrace (prefixWord ++ tailWord_1260107) baseStart_1260107 baseEnd_1260107 := by
    simpa [prefixWord, tailWord_1260107, baseEnd_1260107] using wordTrace_append hprefix tailTrace_1260107
  have hstable : (prefixWord ++ tailWord_1260107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260107).length < 2 ^ (prefixWord ++ tailWord_1260107).sum := by decide
  have hdescent : baseEnd_1260107 < baseStart_1260107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260184 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 9]
def baseStart_1260184 : Nat := 118140960795 + 1260184 * 2 ^ 59
def prefixEnd_1260184 : Nat := 4983230072969 + 3 ^ 40 * 1260184 * 2
def baseEnd_1260184 : Nat := 71897789456178084222725

theorem tailTrace_1260184 : CollatzResearch.WordTrace tailWord_1260184 prefixEnd_1260184 71897789456178084222725 := by
  unfold tailWord_1260184
  simp only [CollatzResearch.WordTrace]
  refine ⟨22981343233288032568793803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30641790977717376758391737 22981343233288032568793803)
  ·
    refine ⟨34472014849932048853190705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22981343233288032568793803 34472014849932048853190705)
    ·
      refine ⟨25854011137449036639893029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34472014849932048853190705 25854011137449036639893029)
      ·
        refine ⟨4847627088271694369979943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25854011137449036639893029 4847627088271694369979943)
        ·
          refine ⟨7271440632407541554969915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847627088271694369979943 7271440632407541554969915)
          ·
            refine ⟨10907160948611312332454873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7271440632407541554969915 10907160948611312332454873)
            ·
              refine ⟨8180370711458484249341155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10907160948611312332454873 8180370711458484249341155)
              ·
                refine ⟨12270556067187726374011733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8180370711458484249341155 12270556067187726374011733)
                ·
                  refine ⟨71897789456178084222725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12270556067187726374011733 71897789456178084222725)
                  ·
                    rfl

theorem cell23_1260184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 9].length) (baseStart_1260184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260184 prefixEnd_1260184 := by exact prefixLift 1260184
  have htrace : WordTrace (prefixWord ++ tailWord_1260184) baseStart_1260184 baseEnd_1260184 := by
    simpa [prefixWord, tailWord_1260184, baseEnd_1260184] using wordTrace_append hprefix tailTrace_1260184
  have hstable : (prefixWord ++ tailWord_1260184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260184).length < 2 ^ (prefixWord ++ tailWord_1260184).sum := by decide
  have hdescent : baseEnd_1260184 < baseStart_1260184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260199 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_1260199 : Nat := 118140960795 + 1260199 * 2 ^ 59
def prefixEnd_1260199 : Nat := 4983230072969 + 3 ^ 40 * 1260199 * 2
def baseEnd_1260199 : Nat := 647087807315420199316957

theorem tailTrace_1260199 : CollatzResearch.WordTrace tailWord_1260199 prefixEnd_1260199 647087807315420199316957 := by
  unfold tailWord_1260199
  simp only [CollatzResearch.WordTrace]
  refine ⟨45963233561521722699383651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30642155707681148466255767 45963233561521722699383651)
  ·
    refine ⟨68944850342282584049075477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45963233561521722699383651 68944850342282584049075477)
    ·
      refine ⟨3231789859794496127300413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68944850342282584049075477 3231789859794496127300413)
      ·
        refine ⟨1211921197422936047737655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3231789859794496127300413 1211921197422936047737655)
        ·
          refine ⟨1817881796134404071606483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211921197422936047737655 1817881796134404071606483)
          ·
            refine ⟨2726822694201606107409725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817881796134404071606483 2726822694201606107409725)
            ·
              refine ⟨1022558510325602290278647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2726822694201606107409725 1022558510325602290278647)
              ·
                refine ⟨1533837765488403435417971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022558510325602290278647 1533837765488403435417971)
                ·
                  refine ⟨2300756648232605153126957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533837765488403435417971 2300756648232605153126957)
                  ·
                    refine ⟨862783743087226932422609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300756648232605153126957 862783743087226932422609)
                    ·
                      refine ⟨647087807315420199316957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 862783743087226932422609 647087807315420199316957)
                      ·
                        rfl

theorem cell23_1260199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_1260199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260199 prefixEnd_1260199 := by exact prefixLift 1260199
  have htrace : WordTrace (prefixWord ++ tailWord_1260199) baseStart_1260199 baseEnd_1260199 := by
    simpa [prefixWord, tailWord_1260199, baseEnd_1260199] using wordTrace_append hprefix tailTrace_1260199
  have hstable : (prefixWord ++ tailWord_1260199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260199).length < 2 ^ (prefixWord ++ tailWord_1260199).sum := by decide
  have hdescent : baseEnd_1260199 < baseStart_1260199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
